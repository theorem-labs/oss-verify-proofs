(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.H Require GcFlushY20.  (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP LibDefs LibWP2Spec LibWP2Lib LibFPSpec LibFrame LibRodata LibTagsLib LibBswap.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PerfKc.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf Require SymDriveLB.
From Stdlib Require Zify.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SymDriveLZ.
Unset Nia Cache.  (* [comment removed for export] *)

Module LibReadA2BUba.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Lib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibRodata OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
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
(* [comment removed for export] *)
Local Ltac ev_simpl E ::=   (* [comment removed for export] *)
  lazymatch goal with |- ?G =>
    let G1 := match tt with | _ => eval unfold E in G | _ => G end in
    let G2 := eval lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in G1 in
    change G2
  end.
Local Ltac ev_simpl_in E H ::= try unfold E in H; lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in H.
#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rs_within (rs RS : list (word * Z)) : Prop :=
  Forall (fun r => Exists (fun R => (bv_unsigned (fst R) <= bv_unsigned (fst r))%Z /\
                                     (bv_unsigned (fst r) + snd r <= bv_unsigned (fst R) + snd R)%Z) RS) rs.

Lemma within_outside1 : forall (b : word) (n : Z) RS x,
  Exists (fun R => (bv_unsigned (fst R) <= bv_unsigned b)%Z /\
                   (bv_unsigned b + n <= bv_unsigned (fst R) + snd R)%Z) RS ->
  outside x RS -> ~ in_rng x b n.
Proof.
  intros b n RS x H. induction H as [[B N] RS' HB | [B N] RS' HB IH].
  - cbn [outside fst snd] in *. intros [H1 _]. unfold in_rng in *. lia.
  - cbn [outside]. intros [_ H2]. apply IH. exact H2.
Qed.

Lemma within_outside : forall rs RS x, rs_within rs RS -> outside x RS -> outside x rs.
Proof.
  intros rs RS x H Hout. induction H as [|[b n] rs Hb Hrs IH]; cbn [outside]; [exact I|].
  split; [| exact IH]. eapply within_outside1; [exact Hb | exact Hout].
Qed.

Lemma frame_mod_within : forall m m' rs RS, rs_within rs RS -> frame_mod m m' rs -> frame_mod m m' RS.
Proof.
  intros m m' rs RS Hw Hf. eapply frame_mod_weaken; [| exact Hf]. intros a Ha. eapply within_outside; eauto.
Qed.

Ltac solve_within :=
  unfold rs_within; repeat (apply Forall_cons; [cbn [fst snd];
    first [ apply Exists_cons_hd; cbn [fst snd]; rewrite ?u_small_frame by lia; lia
          | apply Exists_cons_tl; apply Exists_cons_hd; cbn [fst snd]; rewrite ?u_small_frame by lia; lia
          | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd; cbn [fst snd]; rewrite ?u_small_frame by lia; lia ] |]);
  try apply Forall_nil.

(* [comment removed for export] *)
Lemma writable_sub : forall segs mem lo n lo' n',
  writable segs mem lo n -> (lo <= lo')%Z -> (0 < n')%Z -> (lo' + n' <= lo + n)%Z -> writable segs mem lo' n'.
Proof.
  intros segs mem lo n lo' n' (W1 & W2 & W3 & W4) H1 H2 H3.
  split; [lia|]. split; [lia|]. split; [lia|].
  apply store_ok_of_all; [rewrite u_small_frame by lia; lia|].
  intros a Ha. rewrite u_small_frame in Ha by lia.
  pose proof (store_ok_all segs mem (Z.to_nat n) (Z_to_bv 64 lo)) as X.
  rewrite u_small_frame in X by lia. rewrite Z2Nat.id in X by lia.
  apply (X W3 W4 a). rewrite Z2Nat.id in Ha by lia. lia.
Qed.

Lemma add_lit_word : forall (A : word) (k : Z), (0 <= k)%Z -> (bv_unsigned A + k < 2 ^ 64)%Z ->
  Z_to_bv 64 (bv_unsigned A + k) = alu64 ALU_ADD A (Z_to_bv 64 k).
Proof.
  intros A k Hk H. pose proof (u64_range A). apply bv_eq. rewrite u_add64, !u_lit64a.
  rewrite (Z.mod_small k) by lia. reflexivity.
Qed.

Lemma mod8_add : forall a k, (a mod 8 = 0)%Z -> (k mod 8 = 0)%Z -> ((a + k) mod 8 = 0)%Z.
Proof. intros a k Ha Hk. rewrite Z.add_mod, Ha, Hk by lia. reflexivity. Qed.

Lemma mod16_sub : forall s k, (s mod 16 = 0)%Z -> (k mod 16 = 0)%Z -> ((s - k) mod 16 = 0)%Z.
Proof. intros s k Hs Hk. rewrite Zminus_mod, Hs, Hk. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RA.
  Variables (FPI0 : FPState) (regs0 : bvmap 5 word) (mem0 rom : word -> option byte) (ret : word).
  Variables (data : word) (len : Z) (bs : list byte) (sp T A : word) (pcs : Z).
  Hypothesis Hra : getr regs0 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HPRE : a2b_pre SEGS wp2_infoub data len bs sp T A pcs FPI0 regs0 mem0.
  Hypothesis Hcanon : canonicalize_contract SEGS wp3_infoub.

  #[local] Abbreviation a := (bv_unsigned A).
  #[local] Abbreviation spv := (bv_unsigned sp).

  (* [comment removed for export] *)
  Definition saved (M : word -> option byte) : Prop :=
    cell64 SEGS M (spv - 176 + 168) ret /\
    cell64 SEGS M (spv - 176 + 160) (getr regs0 8) /\ cell64 SEGS M (spv - 176 + 152) (getr regs0 9) /\
    cell64 SEGS M (spv - 176 + 144) (getr regs0 18) /\ cell64 SEGS M (spv - 176 + 136) (getr regs0 19) /\
    cell64 SEGS M (spv - 176 + 128) (getr regs0 20) /\ cell64 SEGS M (spv - 176 + 120) (getr regs0 21) /\
    cell64 SEGS M (spv - 176 + 112) (getr regs0 22) /\ cell64 SEGS M (spv - 176 + 104) (getr regs0 23) /\
    cell64 SEGS M (spv - 176 + 96) (getr regs0 24) /\ cell64 SEGS M (spv - 176 + 88) (getr regs0 25) /\
    cell64 SEGS M (spv - 176 + 80) (getr regs0 26) /\ cell64 SEGS M (spv - 176 + 72) (getr regs0 27).

  Definition fkept (FPI : FPState) : Prop :=
    forall r, In r abi_fkept -> reg_get (fp_regs (FPState:=FPI)) r = reg_get (fp_regs (FPState:=FPI0)) r.

  Definition BIG : list (word * Z) := [(Z_to_bv 64 (spv - 352), 352%Z); (Z_to_bv 64 a, 400%Z)].

  (* [comment removed for export] *)
  Definition adm (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
    getr R 2 = Z_to_bv 64 (spv - 176) /\ getr R 3 = getr regs0 3 /\ getr R 4 = getr regs0 4 /\
    getr R 8 = A /\ getr R 18 = T /\ fkept FPI /\ saved M /\ frame_mod mem0 M BIG /\
    data_ok M data len bs /\ rodata_clear M 0x103ec 0x10490 /\
    writable SEGS M a 400 /\ writable SEGS M (spv - 352) 352.

  Definition Qpost : machine_state -> Prop := fun st' : machine_state =>
    exists (FPI' : FPState) regs' mem',
      st' = mkst (FP:=FPI') regs' ret mem' rom /\
      (regs_kept abi_kept regs0 regs' /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI0)) (fp_regs (FPState:=FPI')) /\
       a2b_post SEGS wp2_infoub data len bs sp T A pcs regs0 mem0 FPI' regs' mem').

  (* [comment removed for export] *)
  Lemma pre_facts :
    (spv mod 16 = 0)%Z /\ (a mod 8 = 0)%Z /\ (0 < a)%Z /\ (a + 400 < 2 ^ 64)%Z /\
    (352 <= spv)%Z /\ (spv < 2 ^ 64)%Z /\
    (0 <= len < 2 ^ 26)%Z /\ (0 < bv_unsigned data)%Z /\ (bv_unsigned data + len < 2 ^ 47)%Z /\
    (spv <= a \/ a + 400 <= spv - 352)%Z /\
    (bv_unsigned data + len <= a \/ a + 400 <= bv_unsigned data)%Z /\
    (bv_unsigned data + len <= spv - 352 \/ spv <= bv_unsigned data)%Z /\
    (spv <= 0x103ec \/ 0x10490 <= spv - 352)%Z /\
    (a + 400 <= 0x103ec \/ 0x10490 <= a)%Z.
  Proof using HPRE.
    destruct HPRE as (Hsp & HT & HA & Hpcs & Heob & Hpcs01 & Hdok & Hty & Htag & HTal & HT24 &
                      WA & HAal & HApos & HA400 & Hcurves & Hg & Hspal & WS & Hro & D1 & D2 & D3 & D4 & D5 & D6).
    change (w_ab_d wp2_infoub) with 352%Z in *.
    change (w_ro_lo wp2_infoub) with 0x103ec%Z in *. change (w_ro_hi wp2_infoub) with 0x10490%Z in *.
    pose proof Hdok as (Hlen & Hbs & Hdnz & Hdhi & Hblob).
    pose proof (u64_range sp). pose proof (u64_range A). pose proof (u64_range data).
    pose proof WS as (WS1 & WS2 & WS3 & WS4).
    pose proof (writable_rodata_apart_Ub mem0 _ _ 0x103ec 0x10490 ltac:(lia) ltac:(lia) ltac:(lia) WS Hro).
    pose proof (writable_rodata_apart_Ub mem0 _ _ 0x103ec 0x10490 ltac:(lia) ltac:(lia) ltac:(lia) WA Hro).
    repeat split; try lia.
  Qed.

  Lemma pre_sp : getr regs0 2 = sp.
  Proof using HPRE. exact (proj1 HPRE). Qed.

  (* [comment removed for export] *)
  Lemma adm_frame : forall (FPI FPI' : FPState) R R' M M' rs,
    adm FPI R M -> frame_mod M M' rs -> rs_within rs BIG -> apart (spv - 104) 104 rs ->
    getr R' 2 = getr R 2 -> getr R' 3 = getr R 3 -> getr R' 4 = getr R 4 ->
    getr R' 8 = getr R 8 -> getr R' 18 = getr R 18 ->
    (forall r, In r abi_fkept -> reg_get (fp_regs (FPState:=FPI')) r = reg_get (fp_regs (FPState:=FPI)) r) ->
    adm FPI' R' M'.
  Proof using HPRE.
    intros FPI FPI' R R' M M' rs (A2 & A3 & A4 & A8 & A18 & AF & AS & AFR & AD & ARO & AWA & AWS)
           Hf Hw Hap E2 E3 E4 E8 E18 EF.
    pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14).
    assert (HfB : frame_mod M M' BIG) by (eapply frame_mod_within; eauto).
    split; [rewrite E2; exact A2|]. split; [rewrite E3; exact A3|]. split; [rewrite E4; exact A4|].
    split; [rewrite E8; exact A8|]. split; [rewrite E18; exact A18|].
    split; [intros r Hr; rewrite (EF r Hr); apply AF; exact Hr|].
    split.
    { unfold saved in *.
      destruct AS as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
      repeat match goal with |- _ /\ _ => split end;
        (eapply cell64_frame; [exact Hf | eassumption | lia | lia | eapply apart_sub; [exact Hap|lia|lia|lia]]). }
    split; [eapply frame_mod_trans_same; [exact AFR | exact HfB]|].
    split.
    { eapply data_ok_frame; [exact HfB | exact AD |]. unfold BIG. solve_apart. }
    split.
    { eapply rodata_clear_frame; [exact HfB | exact ARO | lia | lia |]. unfold BIG. solve_apart. }
    split; [eapply writable_frame; [exact Hf | exact AWA]|].
    eapply writable_frame; [exact Hf | exact AWS].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition base_vals : list word :=
    [ret; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20; getr regs0 21;
     getr regs0 22; getr regs0 23; getr regs0 24; getr regs0 25; getr regs0 26; getr regs0 27;
     data; Z_to_bv 64 len].

  (* [comment removed for export] *)
  Definition kn_adm : list kentry :=
    [KWord (SA (EVar 2) 168) 8 (EVar 64); KWord (SA (EVar 2) 160) 8 (EVar 65); KWord (SA (EVar 2) 152) 8 (EVar 66);
     KWord (SA (EVar 2) 144) 8 (EVar 67); KWord (SA (EVar 2) 136) 8 (EVar 68); KWord (SA (EVar 2) 128) 8 (EVar 69);
     KWord (SA (EVar 2) 120) 8 (EVar 70); KWord (SA (EVar 2) 112) 8 (EVar 71); KWord (SA (EVar 2) 104) 8 (EVar 72);
     KWord (SA (EVar 2) 96) 8 (EVar 73); KWord (SA (EVar 2) 88) 8 (EVar 74); KWord (SA (EVar 2) 80) 8 (EVar 75);
     KWord (SA (EVar 2) 72) 8 (EVar 76);
     KImg 0x103ec 0x10490;
     KRange (EVar 2) 176 18446744073709551440; KWr (SA (EVar 2) (-176)) 352;
     KRange (EVar 8) 1 18446744073709551215; KAlign (EVar 8) 8; KWr (SA (EVar 8) 0) 400;
     KDisj (SA (EVar 2) (-176)) 352 (SA (EVar 8) 0) 400].

  Lemma kn_adm_ok : forall (FPI : FPState) R M extra,
    adm FPI R M ->
    know_ok SEGS (Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ base_vals ++ extra)) (blobs_ev [bs])) M kn_adm.
  Proof using HPRE.
    intros FPI R M extra (A2 & A3 & A4 & A8 & A18 & AF & AS & AFR & AD & ARO & AWA & AWS).
    pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14).
    set (E := Env _ _).
    assert (U2 : bv_unsigned (getr R 2) = (spv - 176)%Z) by (rewrite A2, u_small by lia; lia).
    destruct AS as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
    unfold kn_adm.
    repeat apply Forall_cons; try apply Forall_nil.
    all: try (eapply (kword_intro SEGS E M (EVar 2) (getr R 2) _ 8 _ _);
           [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia |
            rewrite U2; unfold cell64, cell in *;
            match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ =>
              first [ replace x with (spv - 176 + 168)%Z by ring; eassumption
                    | replace x with (spv - 176 + 160)%Z by ring; eassumption
                    | replace x with (spv - 176 + 152)%Z by ring; eassumption
                    | replace x with (spv - 176 + 144)%Z by ring; eassumption
                    | replace x with (spv - 176 + 136)%Z by ring; eassumption
                    | replace x with (spv - 176 + 128)%Z by ring; eassumption
                    | replace x with (spv - 176 + 120)%Z by ring; eassumption
                    | replace x with (spv - 176 + 112)%Z by ring; eassumption
                    | replace x with (spv - 176 + 104)%Z by ring; eassumption
                    | replace x with (spv - 176 + 96)%Z by ring; eassumption
                    | replace x with (spv - 176 + 88)%Z by ring; eassumption
                    | replace x with (spv - 176 + 80)%Z by ring; eassumption
                    | replace x with (spv - 176 + 72)%Z by ring; eassumption ] end]).
    - apply kimg_intro; [lia|lia|exact ARO].
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite U2; lia.
    - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-176) 352); [cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia |].
      rewrite U2. replace (spv - 176 + -176)%Z with (spv - 352)%Z by lia. exact (proj2 (proj2 (proj2 AWS))).
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite A8; lia.
    - apply kalign_intro; [lia|]. cbn [edenot]; ev_simpl E. rewrite A8. exact P2.
    - apply (kwr_intro SEGS E M (EVar 8) A 0 400); [cbn [edenot]; ev_simpl E; exact A8 | lia | lia | lia |].
      rewrite Z.add_0_r. exact (proj2 (proj2 (proj2 AWA))).
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite U2, A8. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac adm_facts HADM :=
    pose proof HADM as (A2 & A3 & A4 & A8 & A18 & AF & AS & AFR & AD & ARO & AWA & AWS);
    pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _);
    assert (U2 : bv_unsigned (getr _ 2) = (spv - 176)%Z) by (rewrite A2, u_small by lia; lia).

  (* [comment removed for export] *)
  Ltac pkg HADM extra kx ktac :=
    lazymatch goal with
    | |- runs_to _ (@mkst ?FPI ?R _ ?M _) _ =>
      set (E := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ base_vals ++ extra)) (blobs_ev [bs]));
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs]));
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs]));
      pose proof (HR : id _) as HR0; pose proof (HF : id _) as HF0;
      let HK1 := fresh "HK1" in let HK2 := fresh "HK2" in
      pose proof (kn_adm_ok FPI R M extra HADM) as HK1; change (know_ok SEGS E M kn_adm) in HK1;
      assert (HK2 : know_ok SEGS E M kx); [ktac|];
      pose proof (know_ok_app SEGS E M kn_adm kx HK1 HK2) as HK; clear HK1 HK2;
      cbv beta delta [kn_adm app] in HK
    end.

  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.

  (* [comment removed for export] *)
  Ltac kept_int :=
    lazymatch goal with HR : regs_ok ?E _ ?R' |- regs_kept abi_kept regs0 ?R' =>
      intros r Hr; cbn [abi_kept In] in Hr;
      repeat (destruct Hr as [<-|Hr]);
      [ regv_lin HR (2%bv:reg);
        match goal with U2 : bv_unsigned (getr _ 2) = _ |- _ => rewrite U2 end;
        rewrite pre_sp; apply bv_eq; rewrite u_small by lia; lia
      | regv HR (3%bv:reg); assumption
      | regv HR (4%bv:reg); assumption
      | .. ];
      try (destruct Hr as []);
      lazymatch goal with |- getr _ ?r = _ => regv HR r; try reflexivity; try assumption end
    end.

  Ltac kept_fp :=
    lazymatch goal with
    | HF : fregs_ok ?E ?sfr' (@fp_regs ?I'), HF0 : id (fregs_ok _ ?sfr0 ?fr), AF : fkept _ |- _ =>
      intros r Hr;
      rewrite (fregs_same_on E sfr0 sfr' fr _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity) r Hr);
      apply AF; exact Hr
    end.

  (* [comment removed for export] *)
  Lemma failk : forall (FPI : FPState) R M,
    adm FPI R M -> runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x1525c) M rom) Qpost.
  Proof using HPRE Hret.
    intros FPI R M HADM. adm_facts HADM.
    pkg HADM (@nil word) (@nil kentry) ltac:(constructor).
    run_fp 40%nat (@nil Z) noscr true.
    fin_ret.
    unfold Qpost.
    lazymatch goal with |- context [@mkst ?I ?R' ?pc ?M' _] => exists I, R', M' end.
    split; [regv HR (1%bv:reg); reflexivity|].
    split; [kept_int|].
    split; [kept_fp|].
    unfold a2b_post. cbv zeta. change (w_ab_d wp2_infoub) with 352%Z.
    split; [subst; exact AFR|].
    exists 0%Z. split; [regv HR (10%bv:reg); reflexivity|]. split; [left; reflexivity|].
    intros H01; exfalso; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma failk' : forall (FPI : FPState) R M,
    adm FPI R M -> getr R 20 = Z_to_bv 64 0 ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x15260) M rom) Qpost.
  Proof using HPRE Hret.
    intros FPI R M HADM H20. adm_facts HADM.
    pkg HADM (@nil word) (@nil kentry) ltac:(constructor).
    run_fp 40%nat (@nil Z) noscr true.
    fin_ret.
    unfold Qpost.
    lazymatch goal with |- context [@mkst ?I ?R' ?pc ?M' _] => exists I, R', M' end.
    split; [regv HR (1%bv:reg); reflexivity|].
    split; [kept_int|].
    split; [kept_fp|].
    unfold a2b_post. cbv zeta. change (w_ab_d wp2_infoub) with 352%Z.
    split; [subst; exact AFR|].
    exists 0%Z. split; [regv HR (10%bv:reg); rewrite H20; reflexivity|]. split; [left; reflexivity|].
    intros H01; exfalso; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition chain_inv (ic mc : Z) (M : word -> option byte) : Prop :=
    cell32 SEGS M (a + 144) ic /\ cell32 SEGS M (a + 296) mc /\ cell32 SEGS M (a + 300) 3 /\
    (0 <= ic <= 4)%Z /\ (mc = 0 \/ mc = 3)%Z /\
    Forall (fun off => curve_ok SEGS M data len (a + off)) a2b_curve_offsets /\
    a2b_grid_ok SEGS M data len a.

  Lemma a2b_grid_ok_frame : forall M M' rs,
    a2b_grid_ok SEGS M data len a -> frame_mod M M' rs ->
    apart (a + 128) 24 rs -> apart (a + 296) 8 rs -> a2b_grid_ok SEGS M' data len a.
  Proof using HPRE.
    intros M M' rs (ic & oc & gps & g8 & g16 & Hic & Hoc & Hicr & Hlen & Hgps & Hgp & Hg8 & Hg16 & Hrest) Hf Hap1 Hap2.
    pose proof pre_facts as (P1 & P2 & P3 & P4 & _).
    exists ic, oc, gps, g8, g16.
    split; [eapply cell32_frame; [exact Hf|exact Hic|lia|lia|]; eapply apart_sub; [exact Hap1|lia|lia|lia]|].
    split; [eapply cell32_frame; [exact Hf|exact Hoc|lia|lia|]; eapply apart_sub; [exact Hap2|lia|lia|lia]|].
    split; [exact Hicr|]. split; [exact Hlen|]. split; [exact Hgps|].
    split.
    { intros i Hi. eapply cell8_frame; [exact Hf|exact (Hgp i Hi)|lia|lia|]. eapply apart_sub; [exact Hap1|lia|lia|lia]. }
    split; [eapply cell64_frame; [exact Hf|exact Hg8|lia|lia|]; eapply apart_sub; [exact Hap1|lia|lia|lia]|].
    split; [eapply cell64_frame; [exact Hf|exact Hg16|lia|lia|]; eapply apart_sub; [exact Hap1|lia|lia|lia]|].
    exact Hrest.
  Qed.

  (* [comment removed for export] *)
  Lemma offsets_apart : forall o o', In o a2b_curve_offsets -> In o' a2b_curve_offsets ->
    o = o' \/ (o + 32 <= o')%Z \/ (o' + 32 <= o)%Z.
  Proof using .
    intros o o' Ho Ho'. cbn in Ho, Ho'.
    repeat (destruct Ho as [<-|Ho]); try (destruct Ho as []);
    repeat (destruct Ho' as [<-|Ho']); try (destruct Ho' as []); lia.
  Qed.

  Lemma offsets_bound : forall o, In o a2b_curve_offsets ->
    (0 <= o)%Z /\ (o + 32 <= 400)%Z /\ (o mod 8 = 0)%Z /\
    ((o + 32 <= 128)%Z \/ (152 <= o /\ o + 32 <= 248)%Z \/ (304 <= o)%Z).
  Proof using .
    intros o Ho. cbn in Ho. repeat (destruct Ho as [<-|Ho]); try (destruct Ho as []);
      (split; [lia|]; split; [lia|]; split; [reflexivity|]; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma chain_inv_canon : forall ic mc M M' (w : word) o,
    chain_inv ic mc M -> In o a2b_curve_offsets ->
    frame_mod M M' [(w, 176%Z); (Z_to_bv 64 (a + o), 32%Z)] ->
    (bv_unsigned w + 176 <= a \/ a + 400 <= bv_unsigned w)%Z ->
    curve_ok SEGS M' data len (a + o) ->
    chain_inv ic mc M'.
  Proof using HPRE.
    intros ic mc M M' w o (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid) Ho Hf Hw Hc.
    pose proof pre_facts as (P1 & P2 & P3 & P4 & _).
    pose proof (offsets_bound o Ho) as (B1 & B2 & B3 & B4).
    assert (AP : forall lo n, (0 <= lo)%Z -> (a + o + 32 <= lo \/ lo + n <= a + o)%Z -> (a <= lo)%Z -> (lo + n <= a + 400)%Z ->
                 apart lo n [(w, 176%Z); (Z_to_bv 64 (a + o), 32%Z)]).
    { intros lo n H1 H2 H3 H4. unfold apart. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - lia.
      - rewrite u_small_frame by lia. lia. }
    split; [eapply cell32_frame; [exact Hf|exact C1|lia|lia|apply AP; lia]|].
    split; [eapply cell32_frame; [exact Hf|exact C2|lia|lia|apply AP; lia]|].
    split; [eapply cell32_frame; [exact Hf|exact C3|lia|lia|apply AP; lia]|].
    split; [exact Hic|]. split; [exact Hmc|].
    split.
    - apply Forall_forall. intros o' Ho'.
      pose proof (proj1 (Forall_forall _ _) Hall o' Ho') as Hc'. cbv beta in Hc'.
      destruct (Z.eq_dec o' o) as [->|Hne]; [exact Hc|].
      pose proof (offsets_apart o o' Ho Ho') as HA. pose proof (offsets_bound o' Ho') as (B1' & B2' & _).
      eapply curve_ok_frame; [exact Hf|exact Hc'|lia|lia|]. apply AP; lia.
    - eapply a2b_grid_ok_frame; [exact Hgrid|exact Hf|apply AP; lia|apply AP; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma canon_pre_at : forall (FPI : FPState) R M ic mc o,
    adm FPI R M -> chain_inv ic mc M -> In o a2b_curve_offsets ->
    getr R 10 = Z_to_bv 64 (a + o) ->
    canon_pre SEGS wp3_infoub data len bs (Z_to_bv 64 (spv - 176)) (Z_to_bv 64 (a + o)) FPI R M.
  Proof using HPRE.
    intros FPI R M ic mc o HADM (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid) Ho H10. adm_facts HADM.
    pose proof pre_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10 & P11 & P12 & _).
    pose proof (offsets_bound o Ho) as (B1 & B2 & B3 & B4).
    unfold canon_pre. cbv zeta.
    change (w3_canon_d wp3_infoub) with 176%Z. change (w3_ro_lo wp3_infoub) with 0x103ec%Z. change (w3_ro_hi wp3_infoub) with 0x10490%Z.
    rewrite !u_small by lia.
    split; [exact A2|]. split; [exact H10|].
    split; [apply mod16_sub; [exact P1|reflexivity]|].
    split; [eapply writable_sub; [exact AWS|lia|lia|lia]|].
    split; [apply mod8_add; [exact P2|exact B3]|].
    split; [eapply writable_sub; [exact AWA|lia|lia|lia]|].
    split; [lia|].
    split; [exact (proj1 (Forall_forall _ _) Hall o Ho)|].
    split; [exact AD|]. split; [exact ARO|].
    lia.
  Qed.

  (* [comment removed for export] *)
  Lemma adm_canon : forall (FPI FPI' : FPState) R R' M M' o,
    adm FPI R M -> In o a2b_curve_offsets ->
    frame_mod M M' [(Z_to_bv 64 (spv - 176 - 176), 176%Z); (Z_to_bv 64 (a + o), 32%Z)] ->
    regs_kept abi_kept R R' ->
    (forall r, In r abi_fkept -> reg_get (fp_regs (FPState:=FPI')) r = reg_get (fp_regs (FPState:=FPI)) r) ->
    adm FPI' R' M'.
  Proof using HPRE.
    intros FPI FPI' R R' M M' o HADM Ho Hf Hk Hfk.
    pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _).
    pose proof (offsets_bound o Ho) as (B1 & B2 & _).
    apply (adm_frame FPI FPI' R R' M M' _ HADM Hf).
    - unfold BIG. solve_within.
    - solve_apart.
    - apply Hk; cbn; repeat (first [left; reflexivity | right]).
    - apply Hk; cbn; repeat (first [left; reflexivity | right]).
    - apply Hk; cbn; repeat (first [left; reflexivity | right]).
    - apply Hk; cbn; repeat (first [left; reflexivity | right]).
    - apply Hk; cbn; repeat (first [left; reflexivity | right]).
    - exact Hfk.
  Qed.

  Lemma chain_inv_canon' : forall ic mc M M' o,
    chain_inv ic mc M -> In o a2b_curve_offsets ->
    frame_mod M M' [(Z_to_bv 64 (spv - 176 - 176), 176%Z); (Z_to_bv 64 (a + o), 32%Z)] ->
    curve_ok SEGS M' data len (a + o) ->
    chain_inv ic mc M'.
  Proof using HPRE.
    intros ic mc M M' o HCI Ho Hf Hc.
    pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _).
    eapply (chain_inv_canon ic mc M M' _ o HCI Ho Hf); [|exact Hc].
    rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac subst_mems :=
    repeat match goal with H : @eq (word -> option byte) ?x _ |- _ => is_var x; subst x end.

  Ltac adm_now HADM HADM1 :=
    subst_mems;
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1, HF : fregs_ok _ ?sfr (@fp_regs ?I1), HF0 : id (fregs_ok _ ?sfr0 (@fp_regs ?I0))
      |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      lazymatch type of HADM with adm _ ?R ?M0 =>
        assert (HADM1 : adm I1 R1 M1);
        [ apply (adm_frame I0 I1 R R1 M0 M1 [] HADM);
          [ apply frame_mod_refl
          | apply Forall_nil
          | apply Forall_nil
          | regv HR (2%bv:reg); reflexivity
          | regv HR (3%bv:reg); reflexivity
          | regv HR (4%bv:reg); reflexivity
          | regv HR (8%bv:reg); reflexivity
          | regv HR (18%bv:reg); reflexivity
          | exact (fregs_same_on E sfr0 sfr _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)) ]
        | ]
      end
    end.

  (* [comment removed for export] *)
  Ltac call_canon o HADM HCI retpc k :=
    let HADM1 := fresh "HADMc" in
    adm_now HADM HADM1;
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1 |- runs_to _ (@mkst ?I1 _ _ ?M1 _) _ =>
      let Ho := fresh "Ho" in
      assert (Ho : In o a2b_curve_offsets) by (clear; cbn; tauto);
      eapply rt_call;
      [ eapply (Hcanon data len bs (Z_to_bv 64 (spv - 176)) (Z_to_bv 64 (a + o)) I1 R1 M1 rom (Z_to_bv 64 retpc));
        [ regv HR (1%bv:reg); reflexivity
        | apply ret_ok_even; rewrite u_small by lia; reflexivity
        | eapply (canon_pre_at I1 R1 M1 _ _ o HADM1); [exact HCI | exact Ho | regv_lin HR (10%bv:reg);
            match goal with A8 : getr _ 8 = A |- _ => rewrite A8 end; f_equal; lia] ]
      | cbv beta; let I' := fresh "FPI" in let R' := fresh "R" in let M' := fresh "M" in
        let Hkeep := fresh "Hkeep" in let Hfkeep := fresh "Hfkeep" in let Hfr := fresh "Hfr" in let Hc := fresh "Hcv" in
        intros I' R' M' (Hkeep & Hfkeep & Hfr & Hc);
        change (w3_canon_d wp3_infoub) with 176%Z in Hfr;
        rewrite (u_small (spv - 176)) in Hfr by lia; rewrite (u_small (a + o)) in Hc by lia;
        let HADM' := fresh "HADM" in let HCI' := fresh "HCI" in
        pose proof (adm_canon I1 I' R1 R' M1 M' o HADM1 Ho Hfr Hkeep Hfkeep) as HADM';
        lazymatch type of HCI with chain_inv ?ic ?mc _ =>
          assert (HCI' : chain_inv ic mc M');
          [ eapply (chain_inv_canon' ic mc M1 M' o); [exact HCI | exact Ho | exact Hfr | exact Hc]
          | k I' R' M' HADM' HCI' Hkeep ] end ]
    end.

  (* [comment removed for export] *)
  Ltac pkg_cell HADM off v C :=
    pkg HADM (@nil word) [KWord (SA (EVar 8) off) 4 (ELit v)]
      ltac:(constructor; [|constructor];
            lazymatch goal with |- kentry_ok _ ?E ?M _ =>
              eapply (kword_intro SEGS E M (EVar 8) A off 4 (ELit v) (Z_to_bv 64 v));
              [ cbn [edenot]; ev_simpl E; match goal with A8 : getr _ 8 = A |- _ => exact A8 end
              | reflexivity | lia | lia | lia | lia | exact (proj2 C)] end).

  (* [comment removed for export] *)
  Lemma out4 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M -> getr R 20 = Z_to_bv 64 1 ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x15254) M rom) Qpost.
  Proof using HPRE Hret.
    intros FPI R M ic mc HADM HCI H20. adm_facts HADM.
    pkg HADM (@nil word) (@nil kentry) ltac:(constructor).
    run_fp 40%nat (@nil Z) noscr true.
    fin_ret.
    unfold Qpost.
    lazymatch goal with |- context [@mkst ?I ?R' ?pc ?M' _] => exists I, R', M' end.
    split; [regv HR (1%bv:reg); reflexivity|].
    split; [kept_int|].
    split; [kept_fp|].
    unfold a2b_post. cbv zeta. change (w_ab_d wp2_infoub) with 352%Z.
    split; [subst; exact AFR|].
    exists 1%Z. split; [regv HR (10%bv:reg); rewrite H20; reflexivity|]. split; [right; reflexivity|].
    intros _. subst. destruct HCI as (_ & _ & _ & _ & _ & Hall & Hgrid). split; [exact Hall | exact Hgrid].
  Qed.

  (* [comment removed for export] *)
  Lemma out3 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M -> getr R 20 = Z_to_bv 64 1 -> getr R 9 = Z_to_bv 64 (a + 304) ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x15238) M rom) Qpost.
  Proof using HPRE Hcanon Hret.
    intros FPI R M ic mc HADM HCI H20 H9. adm_facts HADM.
    pose proof HCI as (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid).
    pkg_cell HADM 300%Z 3%Z C3.
    pin_reg HR (9%bv:reg) (EAlu ALU_ADD (EVar 8) (ELit 304%Z)) by (cbn [edenot]; ev_simpl E; rewrite H9, A8; apply add_lit_word; lia).
    run_fp 40%nat [0x165ac%Z] noscr true.
    call_canon 368%Z HADM HCI 0x15254%Z
      ltac:(fun I' R' M' HADM' HCI' Hkeep =>
              apply (out4 I' R' M' ic mc HADM' HCI');
              rewrite (Hkeep 20%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); regv HR (20%bv:reg); exact H20).
  Qed.

  (* [comment removed for export] *)
  Lemma out2 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M -> getr R 20 = Z_to_bv 64 1 -> getr R 9 = Z_to_bv 64 (a + 304) ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x1521c) M rom) Qpost.
  Proof using HPRE Hcanon Hret.
    intros FPI R M ic mc HADM HCI H20 H9. adm_facts HADM.
    pose proof HCI as (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid).
    pkg_cell HADM 300%Z 3%Z C3.
    pin_reg HR (9%bv:reg) (EAlu ALU_ADD (EVar 8) (ELit 304%Z)) by (cbn [edenot]; ev_simpl E; rewrite H9, A8; apply add_lit_word; lia).
    run_fp 40%nat [0x165ac%Z] noscr true.
    call_canon 336%Z HADM HCI 0x15238%Z
      ltac:(fun I' R' M' HADM' HCI' Hkeep =>
              apply (out3 I' R' M' ic mc HADM' HCI');
              [ rewrite (Hkeep 20%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); regv HR (20%bv:reg); exact H20
              | rewrite (Hkeep 9%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); regv_lin HR (9%bv:reg); rewrite A8; f_equal; lia ]).
  Qed.

  (* [comment removed for export] *)
  Lemma out1 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x15204) M rom) Qpost.
  Proof using HPRE Hcanon Hret.
    intros FPI R M ic mc HADM HCI. adm_facts HADM.
    pose proof HCI as (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid).
    pkg_cell HADM 300%Z 3%Z C3.
    run_fp 40%nat [0x165ac%Z] noscr true.
    call_canon 304%Z HADM HCI 0x1521c%Z
      ltac:(fun I' R' M' HADM' HCI' Hkeep =>
              apply (out2 I' R' M' ic mc HADM' HCI');
              [ rewrite (Hkeep 20%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); regv HR (20%bv:reg); reflexivity
              | rewrite (Hkeep 9%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); regv_lin HR (9%bv:reg); rewrite A8; f_equal; lia ]).
  Qed.

  (* [comment removed for export] *)
  Ltac relay L HADM HCI :=
    let HADM1 := fresh "HADMr" in
    adm_now HADM HADM1;
    lazymatch type of HCI with chain_inv ?ic ?mc _ =>
    lazymatch goal with
    | |- runs_to _ (@mkst ?I1 ?R1 _ ?M1 _) _ =>
        apply (L I1 R1 M1 ic mc HADM1); exact HCI
    end end.

  (* [comment removed for export] *)
  Lemma mat3 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M -> mc = 3%Z -> getr R 9 = Z_to_bv 64 (a + 152) ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x151e8) M rom) Qpost.
  Proof using HPRE Hcanon Hret.
    intros FPI R M ic mc HADM HCI Hmc3 H9. adm_facts HADM.
    pose proof HCI as (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid). rewrite Hmc3 in C2.
    pkg_cell HADM 296%Z 3%Z C2.
    pin_reg HR (9%bv:reg) (EAlu ALU_ADD (EVar 8) (ELit 152%Z)) by (cbn [edenot]; ev_simpl E; rewrite H9, A8; apply add_lit_word; lia).
    run_fp 40%nat [0x165ac%Z] noscr true.
    call_canon 216%Z HADM HCI 0x15204%Z
      ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (out1 I' R' M' ic mc HADM' HCI')).
  Qed.

  (* [comment removed for export] *)
  Lemma mat2 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M -> mc = 3%Z -> getr R 9 = Z_to_bv 64 (a + 152) ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x151cc) M rom) Qpost.
  Proof using HPRE Hcanon Hret.
    intros FPI R M ic mc HADM HCI Hmc3 H9. adm_facts HADM.
    pose proof HCI as (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid). rewrite Hmc3 in C2.
    pkg_cell HADM 296%Z 3%Z C2.
    pin_reg HR (9%bv:reg) (EAlu ALU_ADD (EVar 8) (ELit 152%Z)) by (cbn [edenot]; ev_simpl E; rewrite H9, A8; apply add_lit_word; lia).
    run_fp 40%nat [0x165ac%Z] noscr true.
    call_canon 184%Z HADM HCI 0x151e8%Z
      ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (mat3 I' R' M' ic mc HADM' HCI' Hmc3);
              rewrite (Hkeep 9%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); regv_lin HR (9%bv:reg); rewrite A8; f_equal; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma mat1 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x151b8) M rom) Qpost.
  Proof using HPRE Hcanon Hret.
    intros FPI R M ic mc HADM HCI. adm_facts HADM.
    pose proof HCI as (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid).
    destruct Hmc as [Hmc0 | Hmc3].
    - rewrite Hmc0 in C2. pkg_cell HADM 296%Z 0%Z C2.
      run_fp 40%nat [0x15204%Z; 0x165ac%Z] noscr true.
      relay out1 HADM HCI.
    - rewrite Hmc3 in C2. pkg_cell HADM 296%Z 3%Z C2.
      run_fp 40%nat [0x15204%Z; 0x165ac%Z] noscr true.
      call_canon 152%Z HADM HCI 0x151cc%Z
        ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (mat2 I' R' M' ic mc HADM' HCI' Hmc3);
                rewrite (Hkeep 9%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); regv_lin HR (9%bv:reg); rewrite A8; f_equal; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma in4 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M -> (3 <= ic)%Z ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x1519c) M rom) Qpost.
  Proof using HPRE Hcanon Hret.
    intros FPI R M ic mc HADM HCI Hic3. adm_facts HADM.
    pose proof HCI as (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid).
    assert (Hc : ic = 3%Z \/ ic = 4%Z) by lia.
    destruct Hc as [Hc | Hc]; rewrite Hc in C1.
    - pkg_cell HADM 144%Z 3%Z C1.
      run_fp 40%nat [0x151b8%Z; 0x165ac%Z] noscr true.
      relay mat1 HADM HCI.
    - pkg_cell HADM 144%Z 4%Z C1.
      run_fp 40%nat [0x151b8%Z; 0x165ac%Z] noscr true.
      call_canon 96%Z HADM HCI 0x151b8%Z
        ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (mat1 I' R' M' ic mc HADM' HCI')).
  Qed.

  (* [comment removed for export] *)
  Lemma in3 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M -> (2 <= ic)%Z ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x15180) M rom) Qpost.
  Proof using HPRE Hcanon Hret.
    intros FPI R M ic mc HADM HCI Hic2. adm_facts HADM.
    pose proof HCI as (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid).
    assert (Hc : ic = 2%Z \/ ic = 3%Z \/ ic = 4%Z) by lia.
    destruct Hc as [Hc | [Hc | Hc]]; rewrite Hc in C1.
    - pkg_cell HADM 144%Z 2%Z C1.
      run_fp 40%nat [0x151b8%Z; 0x165ac%Z] noscr true.
      relay mat1 HADM HCI.
    - pkg_cell HADM 144%Z 3%Z C1.
      run_fp 40%nat [0x151b8%Z; 0x165ac%Z] noscr true.
      call_canon 64%Z HADM HCI 0x1519c%Z
        ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (in4 I' R' M' ic mc HADM' HCI' ltac:(lia))).
    - pkg_cell HADM 144%Z 4%Z C1.
      run_fp 40%nat [0x151b8%Z; 0x165ac%Z] noscr true.
      call_canon 64%Z HADM HCI 0x1519c%Z
        ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (in4 I' R' M' ic mc HADM' HCI' ltac:(lia))).
  Qed.

  (* [comment removed for export] *)
  Lemma in2 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M -> (1 <= ic)%Z ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x15164) M rom) Qpost.
  Proof using HPRE Hcanon Hret.
    intros FPI R M ic mc HADM HCI Hic1. adm_facts HADM.
    pose proof HCI as (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid).
    assert (Hc : ic = 1%Z \/ ic = 2%Z \/ ic = 3%Z \/ ic = 4%Z) by lia.
    destruct Hc as [Hc | [Hc | [Hc | Hc]]]; rewrite Hc in C1.
    - pkg_cell HADM 144%Z 1%Z C1.
      run_fp 40%nat [0x151b8%Z; 0x165ac%Z] noscr true.
      relay mat1 HADM HCI.
    - pkg_cell HADM 144%Z 2%Z C1.
      run_fp 40%nat [0x151b8%Z; 0x165ac%Z] noscr true.
      call_canon 32%Z HADM HCI 0x15180%Z
        ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (in3 I' R' M' ic mc HADM' HCI' ltac:(lia))).
    - pkg_cell HADM 144%Z 3%Z C1.
      run_fp 40%nat [0x151b8%Z; 0x165ac%Z] noscr true.
      call_canon 32%Z HADM HCI 0x15180%Z
        ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (in3 I' R' M' ic mc HADM' HCI' ltac:(lia))).
    - pkg_cell HADM 144%Z 4%Z C1.
      run_fp 40%nat [0x151b8%Z; 0x165ac%Z] noscr true.
      call_canon 32%Z HADM HCI 0x15180%Z
        ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (in3 I' R' M' ic mc HADM' HCI' ltac:(lia))).
  Qed.

  (* [comment removed for export] *)
  Lemma in1 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M -> getr R 10 = Z_to_bv 64 ic ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x15158) M rom) Qpost.
  Proof using HPRE Hcanon Hret.
    intros FPI R M ic mc HADM HCI H12. adm_facts HADM.
    pose proof HCI as (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid).
    assert (Hc : ic = 0%Z \/ ic = 1%Z \/ ic = 2%Z \/ ic = 3%Z \/ ic = 4%Z) by lia.
    destruct Hc as [Hc | [Hc | [Hc | [Hc | Hc]]]]; rewrite Hc in C1, H12.
    - pkg_cell HADM 144%Z 0%Z C1.
      pin_reg HR (10%bv:reg) (ELit 0%Z) by (cbn [edenot]; exact H12).
      run_fp 40%nat [0x151b8%Z; 0x165ac%Z] noscr true.
      relay mat1 HADM HCI.
    - pkg_cell HADM 144%Z 1%Z C1.
      pin_reg HR (10%bv:reg) (ELit 1%Z) by (cbn [edenot]; exact H12).
      run_fp 40%nat [0x151b8%Z; 0x165ac%Z] noscr true.
      call_canon 0%Z HADM HCI 0x15164%Z
        ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (in2 I' R' M' ic mc HADM' HCI' ltac:(lia))).
    - pkg_cell HADM 144%Z 2%Z C1.
      pin_reg HR (10%bv:reg) (ELit 2%Z) by (cbn [edenot]; exact H12).
      run_fp 40%nat [0x151b8%Z; 0x165ac%Z] noscr true.
      call_canon 0%Z HADM HCI 0x15164%Z
        ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (in2 I' R' M' ic mc HADM' HCI' ltac:(lia))).
    - pkg_cell HADM 144%Z 3%Z C1.
      pin_reg HR (10%bv:reg) (ELit 3%Z) by (cbn [edenot]; exact H12).
      run_fp 40%nat [0x151b8%Z; 0x165ac%Z] noscr true.
      call_canon 0%Z HADM HCI 0x15164%Z
        ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (in2 I' R' M' ic mc HADM' HCI' ltac:(lia))).
    - pkg_cell HADM 144%Z 4%Z C1.
      pin_reg HR (10%bv:reg) (ELit 4%Z) by (cbn [edenot]; exact H12).
      run_fp 40%nat [0x151b8%Z; 0x165ac%Z] noscr true.
      call_canon 0%Z HADM HCI 0x15164%Z
        ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (in2 I' R' M' ic mc HADM' HCI' ltac:(lia))).
  Qed.

  (* [comment removed for export] *)
  Lemma in0 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x15154) M rom) Qpost.
  Proof using HPRE Hcanon Hret.
    intros FPI R M ic mc HADM HCI. adm_facts HADM.
    pose proof HCI as (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid).
    assert (Hc : ic = 0%Z \/ ic = 1%Z \/ ic = 2%Z \/ ic = 3%Z \/ ic = 4%Z) by lia.
    destruct Hc as [Hc | [Hc | [Hc | [Hc | Hc]]]]; rewrite Hc in C1;
    [ pkg_cell HADM 144%Z 0%Z C1 | pkg_cell HADM 144%Z 1%Z C1 | pkg_cell HADM 144%Z 2%Z C1
    | pkg_cell HADM 144%Z 3%Z C1 | pkg_cell HADM 144%Z 4%Z C1 ];
    run_fp 10%nat [0x15158%Z] noscr true;
    (let HADM1 := fresh "HADMr" in
     adm_now HADM HADM1;
     lazymatch goal with
     | |- runs_to _ (@mkst ?I1 ?R1 _ ?M1 _) _ =>
        apply (in1 I1 R1 M1 ic mc HADM1); [exact HCI | regv HR (10%bv:reg); rewrite Hc; reflexivity]
     end).
  Qed.
End RA.
End LibReadA2BUba.

Module LibMftcA2BUb.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Lib.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfKc.
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

#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

Section P.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte) (ret : word).
  Variables (data : word) (len : Z) (bs : list byte) (mft A : word).
  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HPRE : mftc_a2b_pre SEGS data len bs mft A FPI regs mem.

  #[local] Abbreviation ic := (bs_byte bs (bv_unsigned mft + 8 - bv_unsigned data)).
  #[local] Abbreviation oc := (bs_byte bs (bv_unsigned mft + 9 - bv_unsigned data)).
  #[local] Abbreviation g := (bs_byte bs (bv_unsigned mft + 10 - bv_unsigned data)).

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                ++ [Z_to_bv 64 ic; Z_to_bv 64 oc; Z_to_bv 64 g; data; Z_to_bv 64 len])) (blobs_ev [bs]).

  (* [comment removed for export] *)
  Definition kn_base (eic eoc : expr) (glo ghi : Z) : list kentry :=
    [KWord (SA (EVar 10) 8) 1 eic; KWord (SA (EVar 10) 9) 1 eoc; KWord (SA (EVar 10) 10) 1 (EVar 66);
     KRange (EVar 66) glo ghi; KAlign (EVar 11) 8; KRange (EVar 11) 0 (2^64 - 400);
     KWr (SA (EVar 11) 0) 400; KDisj (SA (EVar 11) 0) 400 (SA (EVar 10) 0) 48].

  Lemma kn_base_ok : forall eic eoc glo ghi,
    edenot E eic = Z_to_bv 64 ic -> edenot E eoc = Z_to_bv 64 oc -> (glo <= g <= ghi)%Z ->
    know_ok SEGS E mem (kn_base eic eoc glo ghi).
  Proof.
    intros eic eoc glo ghi Heic Heoc Hg.
    destruct HPRE as (Hmft & HA & Hdok & Hin & Hwr & Hal & Hdisj).
    pose proof Hdok as (Hlen & Hbs & Hdnz & Hdhi & Hblob). destruct Hin as (Hin1 & _ & Hin2). destruct Hwr as (W1 & W2 & W3 & W4).
    pose proof (u64_range mft). pose proof (u64_range A). pose proof (u64_range data).
    pose proof (bs_byte_range bs (bv_unsigned mft + 8 - bv_unsigned data)) as R1.
    pose proof (bs_byte_range bs (bv_unsigned mft + 9 - bv_unsigned data)) as R2.
    pose proof (bs_byte_range bs (bv_unsigned mft + 10 - bv_unsigned data)) as R3.
    unfold kn_base.
    repeat apply Forall_cons; try apply Forall_nil.
    - eapply (kword_intro SEGS E mem (EVar 10) mft 8 1 eic (Z_to_bv 64 ic));
        [cbn [edenot]; ev_simpl E; exact Hmft | exact Heic | lia | lia | lia | lia
        | apply (data_byte_cell SEGS mem data len bs); [exact Hdok | lia | lia]].
    - eapply (kword_intro SEGS E mem (EVar 10) mft 9 1 eoc (Z_to_bv 64 oc));
        [cbn [edenot]; ev_simpl E; exact Hmft | exact Heoc | lia | lia | lia | lia
        | apply (data_byte_cell SEGS mem data len bs); [exact Hdok | lia | lia]].
    - eapply (kword_intro SEGS E mem (EVar 10) mft 10 1 (EVar 66) (Z_to_bv 64 g));
        [cbn [edenot]; ev_simpl E; exact Hmft | reflexivity | lia | lia | lia | lia
        | apply (data_byte_cell SEGS mem data len bs); [exact Hdok | lia | lia]].
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia.
    - apply kalign_intro; [lia|]. cbn [edenot]; ev_simpl E. rewrite HA. exact Hal.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite HA; lia.
    - apply (kwr_intro SEGS E mem (EVar 11) A 0 400); [cbn [edenot]; ev_simpl E; exact HA | lia | lia | lia |].
      rewrite Z.add_0_r. exact W4.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite Hmft, HA. lia.
  Qed.

  (* [comment removed for export] *)
  Definition Qpost : machine_state -> Prop := fun st' : machine_state =>
    exists (FPI' : FPState) regs' mem',
      st' = mkst (FP:=FPI') regs' ret mem' rom /\
      (regs_kept abi_kept regs regs' /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
       mftc_a2b_post SEGS data len bs mft A regs mem FPI' regs' mem').

  Ltac kept_tac :=
    lazymatch goal with
    | HR : regs_ok ?E _ ?R, HF : fregs_ok _ _ (@fp_regs ?I), HR0 : id (regs_ok _ ?sr0 ?regs), HF0 : id (fregs_ok _ ?sfr0 ?fr) |- _ =>
      split; [exact (regs_same_on E sr0 _ regs R abi_kept HR0 HR ltac:(vm_compute; reflexivity))|];
      split; [exact (fregs_same_on E sfr0 _ fr _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))|]
    end.

  (* [comment removed for export] *)
  Ltac frame_of_log E RS fixup :=
    lazymatch goal with
    | |- frame_mod ?M (mem_denot _ ?M ?log) ?regions =>
        replace regions with (regions_denot E RS)
          by (cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl E; fixup; reflexivity);
        apply (frame_mod_mem_denot E M log RS);
          [ lazymatch goal with H : log_flat _ log |- _ => exact H end
          | repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E; fixup; lia
          | vm_compute; reflexivity ]
    end.

  (* [comment removed for export] *)
  Ltac finish_common :=
    fin_ret;
    lazymatch goal with |- Qpost (@mkst ?I ?R' _ ?M' _) =>
      exists I, R', M';
      split; [ lazymatch goal with HR : regs_ok _ _ R' |- _ => regv HR (1%bv:reg) end; rewrite_getr; reflexivity |];
      kept_tac;
      unfold mftc_a2b_post; cbv zeta; split;
      [ lazymatch goal with EQM : M' = _ |- _ => rewrite EQM end;
        frame_of_log E [(SA (EVar 11) 144, 8%Z); (SA (EVar 11) 296, 8%Z)] ltac:(rewrite_getr)
      | exists (bv_unsigned (getr R' 10)); split; [symmetry; apply Z_to_bv_bv_unsigned|] ]
    end.

  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.

  Ltac flat_tac := unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E; rewrite_getr; lia.

  (* [comment removed for export] *)
  Ltac kcell b k n v H :=
    lazymatch goal with HK : know_ok _ ?E ?M ?kn |- _ =>
      let KR := fresh "KR" in let Hfl := fresh "Hfl" in
      kread_rdn_fast SEGS E M kn b k n v HK H;
      lazymatch type of H with ?FL -> _ => assert (Hfl : FL) by flat_tac; specialize (H Hfl); clear Hfl end;
      unfold adenot, v_addi in H; cbn [a_base a_off edenot] in H; ev_simpl_in E H; rewrite_getr_in H
    end.

  Ltac prelim :=
    pose proof HPRE as (Hmft & HA & Hdok & Hin & Hwr & Hal & Hdisj);
    pose proof Hdok as (Hlen & Hbs & Hdnz & Hdhi & Hblob); destruct Hin as (Hin1 & _ & Hin2);
    destruct Hwr as (W1 & W2 & W3 & W4);
    pose proof (u64_range mft); pose proof (u64_range A); pose proof (u64_range data);
    pose proof (bs_byte_range bs (bv_unsigned mft + 8 - bv_unsigned data)) as R1;
    pose proof (bs_byte_range bs (bv_unsigned mft + 9 - bv_unsigned data)) as R2;
    pose proof (bs_byte_range bs (bv_unsigned mft + 10 - bv_unsigned data)) as R3;
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs]));
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs]));
    pose proof (HR : id _) as HR0; pose proof (HF : id _) as HF0.

  (* [comment removed for export] *)
  Ltac fin0 :=
    finish_common;
    lazymatch goal with HR : regs_ok _ _ ?R' |- _ => regv HR (10%bv:reg) end;
    rewrite ?mftc_ret_word; rewrite ?(u_small g), ?u_small by lia;
    try (replace (g <? 2)%Z with true by (symmetry; apply Z.ltb_lt; lia));
    split; [lia | intros; exfalso; lia].

  Ltac cell8_at j :=
    first [ exfalso; lia
          | let C := fresh "C" in
            let k := eval vm_compute in (148 + j)%Z in
            kcell (EVar 11) k 1%nat (EExt false 0 1 (EVar 66)) C;
            rewrite (ext_val_zx_id 1 (Z_to_bv 64 g)) in C by (rewrite u_small by lia; cbn; lia);
            replace (bv_unsigned A + 148 + j)%Z with (bv_unsigned A + k)%Z by lia; exact C ].
  Ltac cells8 :=
    intros i Hi; split; [lia|];
    let Hi4 := fresh "Hi4" in
    assert (Hi4 : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3)%Z) by lia;
    destruct Hi4 as [->|[->|[->| ->]]]; [cell8_at 0%Z | cell8_at 1%Z | cell8_at 2%Z | cell8_at 3%Z].

  (* [comment removed for export] *)
  Ltac case_ok c :=
    lazymatch goal with Hlc : edenot E (ELit c) = Z_to_bv 64 ic, Hl3 : edenot E (ELit 3) = Z_to_bv 64 oc |- _ =>
      assert (HK : know_ok SEGS E mem (kn_base (ELit c) (ELit 3) 2 255)) by (apply kn_base_ok; [exact Hlc | exact Hl3 | lia]);
      unfold kn_base in HK;
      run_fp 100%nat (@nil Z) noscr true;
      finish_common;
      lazymatch goal with HR : regs_ok _ _ ?R' |- _ => regv HR (10%bv:reg) end;
      rewrite mftc_ret_word; rewrite (u_small g) by lia;
      replace (g <? 2)%Z with false by (symmetry; apply Z.ltb_ge; lia);
      lazymatch goal with |- context [if ?b then 1%Z else 0%Z] => destruct b end;
      [ split; [lia|]; intros _;
        exists ic, g; split; [lia|]; split; [lia|];
        let C1 := fresh "C1" in let C2 := fresh "C2" in let C3 := fresh "C3" in
        kcell (EVar 11) 144%Z 4%nat (ELit c) C1;
        kcell (EVar 11) 296%Z 4%nat (ELit 0) C2;
        kcell (EVar 11) 300%Z 4%nat (ELit 3) C3;
        lazymatch goal with Hc : ic = c |- _ => rewrite Hc end;
        split; [split; [lia | exact C1]|];
        split; [split; [lia | exact C2]|];
        split; [split; [lia | exact C3]|];
        cells8
      | split; [lia | intros; exfalso; lia] ]
    end.

  Theorem body : runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x1667c) mem rom) Qpost.
  Proof.
    prelim.
    assert (Hv64 : edenot E (EVar 64) = Z_to_bv 64 ic) by (cbn [edenot]; ev_simpl E; reflexivity).
    assert (Hv65 : edenot E (EVar 65) = Z_to_bv 64 oc) by (cbn [edenot]; ev_simpl E; reflexivity).
    destruct (Z.eq_dec oc 3) as [Hoc3|Hocne].
    - (* [comment removed for export] *)
      assert (Hl3 : edenot E (ELit 3) = Z_to_bv 64 oc) by (rewrite Hoc3; reflexivity).
      destruct (Z_lt_le_dec 0 ic) as [Hic0|Hic0]; [destruct (Z_lt_le_dec ic 5) as [Hic5|Hic5]|].
      + (* [comment removed for export] *)
        destruct (Z_lt_le_dec g 2) as [Hglt|Hgge].
        * (* [comment removed for export] *)
          assert (CASE : forall c : Z, ic = c -> (c = 1 \/ c = 2 \/ c = 3 \/ c = 4)%Z ->
                    runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x1667c) mem rom) Qpost).
          { intros c Hc Hcs.
            assert (Hlc : edenot E (ELit c) = Z_to_bv 64 ic) by (rewrite Hc; reflexivity).
            destruct Hcs as [-> | [-> | [-> | ->]]];
            (eassert (HK : know_ok SEGS E mem (kn_base (ELit _) (ELit 3) 0 1)) by (apply kn_base_ok; [exact Hlc | exact Hl3 | lia]));
            unfold kn_base in HK;
            run_fp 100%nat (@nil Z) noscr true;
            fin0. }
          apply (CASE ic eq_refl). lia.
        * assert (CASE : forall c : Z, ic = c -> (c = 1 \/ c = 2 \/ c = 3 \/ c = 4)%Z ->
                    runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x1667c) mem rom) Qpost).
          { intros c Hc Hcs.
            assert (Hlc : edenot E (ELit c) = Z_to_bv 64 ic) by (rewrite Hc; reflexivity).
            destruct Hcs as [-> | [-> | [-> | ->]]].
            -- case_ok 1%Z.
            -- case_ok 2%Z.
            -- case_ok 3%Z.
            -- case_ok 4%Z. }
          apply (CASE ic eq_refl). lia.
      + (* [comment removed for export] *)
        assert (HK : know_ok SEGS E mem (KRange (EVar 64) 5 255 :: kn_base (EVar 64) (ELit 3) 0 255)).
        { constructor; [apply krange_intro; rewrite Hv64; rewrite u_small by lia; lia | apply kn_base_ok; [exact Hv64 | exact Hl3 | lia]]. }
        unfold kn_base in HK. run_fp 100%nat (@nil Z) noscr true. fin0.
      + (* [comment removed for export] *)
        assert (HK : know_ok SEGS E mem (KRange (EVar 64) 0 0 :: kn_base (EVar 64) (ELit 3) 0 255)).
        { constructor; [apply krange_intro; rewrite Hv64; rewrite u_small by lia; lia | apply kn_base_ok; [exact Hv64 | exact Hl3 | lia]]. }
        unfold kn_base in HK. run_fp 100%nat (@nil Z) noscr true. fin0.
    - (* [comment removed for export] *)
      destruct (Z_lt_le_dec oc 3) as [Hlt|Hge].
      + assert (HK : know_ok SEGS E mem (KRange (EVar 65) 0 2 :: kn_base (EVar 64) (EVar 65) 0 255)).
        { constructor; [apply krange_intro; rewrite Hv65; rewrite u_small by lia; lia | apply kn_base_ok; [exact Hv64 | exact Hv65 | lia]]. }
        unfold kn_base in HK. run_fp 100%nat (@nil Z) noscr true. fin0.
      + assert (HK : know_ok SEGS E mem (KRange (EVar 65) 4 255 :: kn_base (EVar 64) (EVar 65) 0 255)).
        { constructor; [apply krange_intro; rewrite Hv65; rewrite u_small by lia; lia | apply kn_base_ok; [exact Hv64 | exact Hv65 | lia]]. }
        unfold kn_base in HK. run_fp 100%nat (@nil Z) noscr true. fin0.
  Qed.
End P.

Theorem read_mft_common_a2b_Ub_ok : read_mft_common_a2b_contract SEGS wp2_infoub.
Proof.
  intros data len bs mft A FPI regs mem rom ret Hra Hret HPRE.
  exact (runs_to_contract SEGS _ ret rom _ (body FPI regs mem rom ret data len bs mft A Hra Hret HPRE)).
Qed.
End LibMftcA2BUb.

Module LibItabA2BUb.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Lib.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfKc.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
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
(* [comment removed for export] *)
Local Ltac ev_simpl E ::=   (* [comment removed for export] *)
  lazymatch goal with |- ?G =>
    let G1 := match tt with | _ => eval unfold E in G | _ => G end in
    let G2 := eval lazy [ev eb vals_ev blobs_ev app junk_vals fjunk_vals] in G1 in
    let G3 := eval cbn [nth] in G2 in
    change G3
  end.
Local Ltac ev_simpl_in E H ::= try unfold E in H; lazy [ev eb vals_ev blobs_ev app junk_vals fjunk_vals] in H; cbn [nth] in H.
#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition kn_it (c : nat) : list kentry :=
  [KWord (SA (EVar 15) 144) 4 (ELit (Z.of_nat c)); KWord (SA (EVar 15) 300) 4 (ELit 3)]
  ++ firstn c [KWord (SA (EVar 15) 148) 1 (EVar 64); KWord (SA (EVar 15) 149) 1 (EVar 65);
              KWord (SA (EVar 15) 150) 1 (EVar 66); KWord (SA (EVar 15) 151) 1 (EVar 67)]
  ++ firstn c [KRange (EVar 64) 2 255; KRange (EVar 65) 2 255; KRange (EVar 66) 2 255; KRange (EVar 67) 2 255]
  ++ [KRange (EVar 13) 2 4096; KRange (EVar 14) 2 4096; KRange (EVar 11) 0 67108864;
      KRange (EVar 10) 1 140737488355328; KRange (EVar 15) 1 18446744073709551216; KAlign (EVar 15) 8;
      KWr (SA (EVar 15) 0) 400; KWr (SA (EVar 2) (-32)) 32; KDisj (SA (EVar 2) (-32)) 32 (SA (EVar 15) 0) 400].

Section P.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte) (ret : word).
  Variables (data : word) (len : Z) (bs : list byte) (sp tb A : word) (maxlen bw ite ote ic : Z) (gps : list Z).
  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HPRE : itab_a2b_pre SEGS wp2_infoub data len bs sp tb A maxlen bw ite ote ic gps FPI regs mem.

  #[local] Abbreviation g0 := (nth 0 gps 0%Z).
  #[local] Abbreviation g1 := (nth 1 gps 0%Z).
  #[local] Abbreviation g2 := (nth 2 gps 0%Z).
  #[local] Abbreviation g3 := (nth 3 gps 0%Z).

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                ++ [Z_to_bv 64 g0; Z_to_bv 64 g1; Z_to_bv 64 g2; Z_to_bv 64 g3; data; Z_to_bv 64 len])) (blobs_ev [bs]).

  Lemma kn_it_ok : forall c : nat, Z.of_nat c = ic -> know_ok SEGS E mem (kn_it c).
  Proof.
    intros c Hc.
    destruct HPRE as (Hsp & Htb & Hml & Hbw & Hite & Hote & HA & Hdok & Hml0 & Hin & Hbw12 & Hiter & Hoter &
                      Hic & Hlen_g & Hgps & Cic & Coc & Cg & WA & HalA & HposA & Wsp & D1 & D2 & D3).
    pose proof Hdok as (Hlen & Hbs & Hdnz & Hdhi & Hblob). destruct Hin as (Hin1 & _ & Hin2).
    destruct WA as (WA1 & WA2 & WA3 & WA4). destruct Wsp as (WS1 & WS2 & WS3 & WS4).
    change (w_init_fr wp2_infoub) with 32%Z in *.
    pose proof (u64_range tb). pose proof (u64_range A). pose proof (u64_range data). pose proof (u64_range sp).
    assert (Gr : forall i, (0 <= i < ic)%Z -> (2 <= nth (Z.to_nat i) gps 0 <= 255)%Z).
    { intros i Hi. apply (Forall_nth (fun g => (2 <= g <= 255)%Z) gps); [exact Hgps|]. lia. }
    assert (Gc : forall (i : Z) (v : expr) (off : Z), (0 <= i < ic)%Z -> off = (148 + i)%Z ->
              edenot E v = Z_to_bv 64 (nth (Z.to_nat i) gps 0%Z) ->
              kentry_ok SEGS E mem (KWord (SA (EVar 15) off) 1 v)).
    { intros i v off Hi -> Hv. pose proof (Cg i Hi) as [Gi Ci].
      eapply (kword_intro SEGS E mem (EVar 15) A (148 + i) 1 v (Z_to_bv 64 (nth (Z.to_nat i) gps 0%Z)));
        [cbn [edenot]; ev_simpl E; exact HA | exact Hv | lia | lia | lia | lia | ].
      replace (bv_unsigned A + (148 + i))%Z with (bv_unsigned A + 148 + i)%Z by lia. exact Ci. }
    assert (Gk : forall (i : Z) (v : expr), (0 <= i < ic)%Z ->
              edenot E v = Z_to_bv 64 (nth (Z.to_nat i) gps 0%Z) ->
              kentry_ok SEGS E mem (KRange v 2 255)).
    { intros i v Hi Hv. apply krange_intro. pose proof (Gr i Hi) as Gi. rewrite Hv, u_small by lia. lia. }
    assert (V0 : edenot E (EVar 64) = Z_to_bv 64 (nth (Z.to_nat 0) gps 0%Z)) by (cbn [edenot]; ev_simpl E; reflexivity).
    assert (V1 : edenot E (EVar 65) = Z_to_bv 64 (nth (Z.to_nat 1) gps 0%Z)) by (cbn [edenot]; ev_simpl E; reflexivity).
    assert (V2 : edenot E (EVar 66) = Z_to_bv 64 (nth (Z.to_nat 2) gps 0%Z)) by (cbn [edenot]; ev_simpl E; reflexivity).
    assert (V3 : edenot E (EVar 67) = Z_to_bv 64 (nth (Z.to_nat 3) gps 0%Z)) by (cbn [edenot]; ev_simpl E; reflexivity).
    assert (c = 1 \/ c = 2 \/ c = 3 \/ c = 4)%nat as Hc4 by lia.
    unfold kn_it.
    apply know_ok_app.
    { constructor; [|constructor; [|constructor]].
      - eapply (kword_intro SEGS E mem (EVar 15) A 144 4 (ELit (Z.of_nat c)) (Z_to_bv 64 ic));
          [cbn [edenot]; ev_simpl E; exact HA | rewrite Hc; reflexivity | lia | lia | lia | lia | exact (proj2 Cic)].
      - eapply (kword_intro SEGS E mem (EVar 15) A 300 4 (ELit 3) (Z_to_bv 64 3));
          [cbn [edenot]; ev_simpl E; exact HA | reflexivity | lia | lia | lia | lia | exact (proj2 Coc)]. }
    apply know_ok_app.
    { destruct Hc4 as [-> |[-> |[-> | ->]]]; cbn [firstn];
      repeat (apply Forall_cons); try apply Forall_nil;
      first [ exact (Gc 0%Z (EVar 64) 148%Z ltac:(lia) eq_refl V0) | exact (Gc 1%Z (EVar 65) 149%Z ltac:(lia) eq_refl V1)
            | exact (Gc 2%Z (EVar 66) 150%Z ltac:(lia) eq_refl V2) | exact (Gc 3%Z (EVar 67) 151%Z ltac:(lia) eq_refl V3) ]. }
    apply know_ok_app.
    { destruct Hc4 as [-> |[-> |[-> | ->]]]; cbn [firstn];
      repeat (apply Forall_cons); try apply Forall_nil;
      first [ exact (Gk 0%Z (EVar 64) ltac:(lia) V0) | exact (Gk 1%Z (EVar 65) ltac:(lia) V1)
            | exact (Gk 2%Z (EVar 66) ltac:(lia) V2) | exact (Gk 3%Z (EVar 67) ltac:(lia) V3) ]. }
    repeat (apply Forall_cons); try apply Forall_nil.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Hite, u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Hote, u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Hml, u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Htb; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite HA; lia.
    - apply kalign_intro; [lia|]. cbn [edenot]; ev_simpl E. rewrite HA. exact HalA.
    - apply (kwr_intro SEGS E mem (EVar 15) A 0 400); [cbn [edenot]; ev_simpl E; exact HA | lia | lia | lia | exact WA4].
    - apply (kwr_intro SEGS E mem (EVar 2) sp (-32) 32); [cbn [edenot]; ev_simpl E; exact Hsp | lia | lia | lia | ].
      replace (bv_unsigned sp + -32)%Z with (bv_unsigned sp - 32)%Z by lia. exact WS4.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite Hsp, HA. lia.
  Qed.

  Definition Qpost : machine_state -> Prop := fun st' : machine_state =>
    exists (FPI' : FPState) regs' mem',
      st' = mkst (FP:=FPI') regs' ret mem' rom /\
      (regs_kept abi_kept regs regs' /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
       itab_a2b_post SEGS wp2_infoub data len bs sp tb A maxlen bw ite ote ic gps regs mem FPI' regs' mem').

  (* [comment removed for export] *)
  Ltac clear_junk :=
    repeat match goal with H : (_ <= _)%Z \/ (_ <= _)%Z |- _ => clear H end;
    repeat match goal with H : forall i : Z, _ -> mem _ = _ |- _ => clear H end;
    repeat match goal with H : forall i : Z, _ -> cell8 _ _ _ _ |- _ => clear H end.

  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac mods_in H :=
    repeat match type of H with context [ (?a mod ?b)%Z ] =>
      lazymatch a with context [ (_ mod _)%Z ] => fail | _ => rewrite (Z.mod_small a b) in H by lia end end.
  Ltac mods_goal :=
    repeat match goal with |- context [ (?a mod ?b)%Z ] =>
      lazymatch a with context [ (_ mod _)%Z ] => fail | _ => rewrite (Z.mod_small a b) by lia end end.
  Ltac wz_in H :=
    rewrite ?u_add64, ?u_mul64 in H; rewrite_getr_in H; rewrite ?u_lit64a in H; mods_in H.
  Ltac wz_goal :=
    rewrite ?u_add64, ?u_mul64; rewrite_getr; rewrite ?u_lit64a; mods_goal.

  Ltac kept_tac :=
    lazymatch goal with
    | HR : regs_ok ?E _ ?R, HF : fregs_ok _ _ (@fp_regs ?I), HR0 : id (regs_ok _ ?sr0 ?regs), HF0 : id (fregs_ok _ ?sfr0 ?fr) |- _ =>
      split; [exact (regs_same_on E sr0 _ regs R abi_kept HR0 HR ltac:(vm_compute; reflexivity))|];
      split; [exact (fregs_same_on E sfr0 _ fr _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))|]
    end.

  Ltac regions_eq :=
    cbn [regions_denot map fst snd]; unfold adenot, v_addi; cbn [a_base a_off edenot]; ev_simpl E; rewrite_getr;
    repeat (apply f_equal2; [apply f_equal2; [apply f_equal; lia | lia] | ]); reflexivity.

  (* [comment removed for export] *)
  Ltac frame_logs RS :=
    lazymatch goal with
    | |- frame_mod ?m0 ?m0 _ => apply frame_mod_refl
    | |- frame_mod ?m0 (mem_denot _ ?m1 ?log) _ =>
        apply (frame_mod_trans_same m0 m1);
        [ frame_logs RS
        | apply (frame_mod_mem_denot E m1 log RS);
          [ lazymatch goal with H : log_flat _ log |- _ => exact H end
          | repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E; rewrite_getr; lia
          | vm_compute; reflexivity ] ]
    end.
  Ltac subst_mems :=
    repeat match goal with H : @eq (word -> option byte) ?Mx _ |- _ => is_var Mx; subst Mx end.
  Ltac frame_of_log E RS :=
    subst_mems;
    lazymatch goal with
    | |- frame_mod _ _ ?regions => replace regions with (regions_denot E RS) by regions_eq; frame_logs RS
    end.

  Ltac flat_tac := unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E; rewrite_getr; lia.

  (* [comment removed for export] *)
  Ltac kcellv b k n H :=
    lazymatch goal with HK : know_ok _ ?E ?M ?kn |- _ =>
      let r := eval vm_compute in (kread SEGS kn b k n) in
      lazymatch r with
      | Some ?v =>
        let KR := fresh "KR" in let Hfl := fresh "Hfl" in
        kread_rdn_fast SEGS E M kn b k n v HK H;
        lazymatch type of H with ?FL -> _ => assert (Hfl : FL) by flat_tac; specialize (H Hfl); clear Hfl end;
        unfold adenot, v_addi in H; cbn [a_base a_off edenot] in H; ev_simpl_in E H; rewrite_getr_in H;
        rewrite ?ext_val_zx_id4 in H by (rewrite ?u_small by lia; lia);
        rewrite ?ext_val_zx_id1 in H by (rewrite ?u_small by lia; lia)
      | _ => fail "kcellv: no knowledge at" b k n
      end
    end.

  (* [comment removed for export] *)
  Ltac finish_common :=
    fin_ret;
    lazymatch goal with |- Qpost (@mkst ?I ?R' _ ?M' _) =>
      exists I, R', M';
      split; [ lazymatch goal with HR : regs_ok _ _ R' |- _ => regv HR (1%bv:reg) end; rewrite_getr; reflexivity |];
      kept_tac;
      unfold itab_a2b_post; cbv zeta; change (w_init_fr wp2_infoub) with 32%Z;
      exists (bv_unsigned (getr R' 10)); split; [symmetry; apply Z_to_bv_bv_unsigned|];
      lazymatch goal with HR : regs_ok _ _ R' |- _ => regv HR (10%bv:reg) end;
      rewrite u_small by lia
    end.

  (* [comment removed for export] *)
  Ltac fin0 :=
    finish_common; left; split; [lia|];
    frame_of_log E [(SA (EVar 2) (-32), 32%Z)].

  (* [comment removed for export] *)
  Ltac wval t U :=
    eassert (U : bv_unsigned t = _)
      by (rewrite ?u_add64, ?u_mul64; rewrite_getr; rewrite ?u_lit64a; mods_goal; reflexivity).

  (* [comment removed for export] *)
  Ltac curve_at off :=
    let C1 := fresh "C" in let C2 := fresh "C" in let C3 := fresh "C" in
    let U8 := fresh "U" in let U16 := fresh "U" in
    let o8 := eval vm_compute in (off + 8)%Z in let o16 := eval vm_compute in (off + 16)%Z in
    kcellv (EVar 15) off 4%nat C1; kcellv (EVar 15) o8 8%nat C2; kcellv (EVar 15) o16 8%nat C3;
    lazymatch type of C1 with _ = Some (word_to_le_bytes 4 (Z_to_bv 64 ?n)) =>
    lazymatch type of C2 with _ = Some (word_to_le_bytes 8 ?t8) =>
    lazymatch type of C3 with _ = Some (word_to_le_bytes 8 ?t16) =>
      wval t8 U8; wval t16 U16;
      exists n, t8, t16;
      split; [split; [lia | exact C1]|];
      split; [replace (bv_unsigned A + off + 8)%Z with (bv_unsigned A + o8)%Z by lia; exact C2|];
      split; [replace (bv_unsigned A + off + 16)%Z with (bv_unsigned A + o16)%Z by lia; exact C3|];
      right; unfold inDATA; rewrite ?U8, ?U16; lia
    end end end.

  Ltac curves_in :=
    intros i Hi;
    let Hi4 := fresh "Hi4" in
    assert (Hi4 : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3)%Z) by lia;
    destruct Hi4 as [-> |[-> |[-> | ->]]];
    [ replace (bv_unsigned A + 32 * 0)%Z with (bv_unsigned A + 0)%Z by lia; curve_at 0%Z
    | first [exfalso; lia | replace (bv_unsigned A + 32 * 1)%Z with (bv_unsigned A + 32)%Z by lia; curve_at 32%Z]
    | first [exfalso; lia | replace (bv_unsigned A + 32 * 2)%Z with (bv_unsigned A + 64)%Z by lia; curve_at 64%Z]
    | first [exfalso; lia | replace (bv_unsigned A + 32 * 3)%Z with (bv_unsigned A + 96)%Z by lia; curve_at 96%Z] ].

  Ltac curves_out :=
    intros i Hi;
    let Hi3 := fresh "Hi3" in
    assert (Hi3 : (i = 0 \/ i = 1 \/ i = 2)%Z) by lia;
    destruct Hi3 as [-> |[-> | ->]];
    [ replace (bv_unsigned A + 304 + 32 * 0)%Z with (bv_unsigned A + 304)%Z by lia; curve_at 304%Z
    | replace (bv_unsigned A + 304 + 32 * 1)%Z with (bv_unsigned A + 336)%Z by lia; curve_at 336%Z
    | replace (bv_unsigned A + 304 + 32 * 2)%Z with (bv_unsigned A + 368)%Z by lia; curve_at 368%Z ].

  Ltac grid_tac :=
    let C1 := fresh "C" in let C2 := fresh "C" in let U8 := fresh "U" in let U16 := fresh "U" in
    kcellv (EVar 15) 128%Z 8%nat C1; kcellv (EVar 15) 136%Z 8%nat C2;
    lazymatch type of C1 with _ = Some (word_to_le_bytes 8 ?g8) =>
    lazymatch type of C2 with _ = Some (word_to_le_bytes 8 ?g16) =>
      wval g8 U8; wval g16 U16;
      exists g8, g16; split; [exact C1|]; split; [exact C2|];
      lazymatch goal with Hz : zprod gps = _ |- _ => rewrite Hz end;
      unfold inDATA; rewrite ?U8, ?U16; split; (intros Hbw'; try (exfalso; lia); split; lia)
    end end.

  (* [comment removed for export] *)
  Ltac fin1 c :=
    finish_common; right; split; [lia|];
    clear_junk;
    let n := eval vm_compute in (32 * Z.of_nat c)%Z in
    split; [frame_of_log E [(SA (EVar 2) (-32), 32%Z); (SA (EVar 15) 0, n); (SA (EVar 15) 128, 16%Z); (SA (EVar 15) 304, 96%Z)]|];
    split; [curves_in|];
    split; [curves_out|];
    grid_tac.

  Ltac prelim :=
    pose proof HPRE as (Hsp & Htb & Hml & Hbw & Hite & Hote & HA & Hdok & Hml0 & Hin & Hbw12 & Hiter & Hoter &
                      Hic & Hlen_g & Hgps & Cic & Coc & Cg & WA & HalA & HposA & Wsp & D1 & D2 & D3);
    pose proof Hdok as (Hlen & Hbs & Hdnz & Hdhi & Hblob); destruct Hin as (Hin1 & _ & Hin2);
    destruct WA as (WA1 & WA2 & WA3 & WA4); destruct Wsp as (WS1 & WS2 & WS3 & WS4);
    change (w_init_fr wp2_infoub) with 32%Z in *;
    pose proof (u64_range tb); pose proof (u64_range A); pose proof (u64_range data); pose proof (u64_range sp);
    assert (HR0 : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs]));
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs]));
    (* [comment removed for export] *)
    assert (HR : regs_ok E (sr_upd (sr_vars 0) 12 (ELit bw)) regs) by
      (apply (regs_ok_pin E _ regs 12); [exact HR0|]; cbn [edenot]; exact Hbw);
    pose proof (HR0 : id _) as HRid; clear HR0; pose proof (HF : id _) as HFid;
    clear HalA;
    assert (Uite : bv_unsigned (Z_to_bv 64 ite) = ite) by (apply u_small; lia);
    assert (Uote : bv_unsigned (Z_to_bv 64 ote) = ote) by (apply u_small; lia);
    assert (Uml : bv_unsigned (Z_to_bv 64 maxlen) = maxlen) by (apply u_small; lia);
    clear_junk;
    (* [comment removed for export] *)
    assert (Gr : forall i, (0 <= i < ic)%Z -> (2 <= nth (Z.to_nat i) gps 0 <= 255)%Z) by
      (intros i Hi; apply (Forall_nth (fun g => (2 <= g <= 255)%Z) gps); [exact Hgps|]; lia).

  (* [comment removed for export] *)
  Ltac usmall :=
    repeat match goal with U : bv_unsigned (Z_to_bv 64 ?z) = ?z |- context [bv_unsigned (Z_to_bv 64 ?y)] => constr_eq z y; rewrite !U end.

  (* [comment removed for export] *)
  Ltac sc_tac := rewrite ?u_add64, ?u_mul64; rewrite_getr; rewrite ?u_lit64a; usmall; mods_goal; mod2_split; lia.

  (* [comment removed for export] *)
  Ltac run_case c :=
    pose proof (kn_it_ok c ltac:(lia)) as HK; cbv beta delta [kn_it firstn app Z.of_nat Pos.of_succ_nat Pos.succ] in HK;
    run_fp 200%nat [0x1679c%Z] noscr true;
    let Hbr := fresh "Hbr" in
    branch_case as Hbr;
    [ run_fp 200%nat (@nil Z) noscr true
    | br_simpl_in E Hbr; wz_in Hbr;
      run_fp 300%nat (@nil Z) (dirs (repeat false 40)) true by sc_tac ].

  (* [comment removed for export] *)
  Ltac fin_case :=
    first
      [ fin0
      | lazymatch goal with
        | Hc : ic = 1%Z |- _ => fin1 1%nat
        | Hc : ic = 2%Z |- _ => fin1 2%nat
        | Hc : ic = 3%Z |- _ => fin1 3%nat
        | Hc : ic = 4%Z |- _ => fin1 4%nat
        end ].

  Theorem body : runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x16704) mem rom) Qpost.
  Proof.
    prelim.
    assert (Hc4 : (ic = 1 \/ ic = 2 \/ ic = 3 \/ ic = 4)%Z) by lia.
    destruct Hc4 as [Hc|[Hc|[Hc|Hc]]];
      [ assert (Gr0 : (2 <= g0 <= 255)%Z) by (apply (Gr 0%Z); lia);
        pose proof (zprod_len1 gps ltac:(lia)) as Hz
      | assert (Gr0 : (2 <= g0 <= 255)%Z) by (apply (Gr 0%Z); lia);
        assert (Gr1 : (2 <= g1 <= 255)%Z) by (apply (Gr 1%Z); lia);
        pose proof (mul_bnd g0 g1 255%Z 255%Z ltac:(lia) ltac:(lia)) as GB01;
        pose proof (zprod_len2 gps ltac:(lia)) as Hz
      | assert (Gr0 : (2 <= g0 <= 255)%Z) by (apply (Gr 0%Z); lia);
        assert (Gr1 : (2 <= g1 <= 255)%Z) by (apply (Gr 1%Z); lia);
        assert (Gr2 : (2 <= g2 <= 255)%Z) by (apply (Gr 2%Z); lia);
        pose proof (mul_bnd g0 g1 255%Z 255%Z ltac:(lia) ltac:(lia)) as GB01;
        pose proof (mul_bnd (g0 * g1) g2 (255 * 255)%Z 255%Z ltac:(lia) ltac:(lia)) as GB012;
        pose proof (zprod_len3 gps ltac:(lia)) as Hz
      | assert (Gr0 : (2 <= g0 <= 255)%Z) by (apply (Gr 0%Z); lia);
        assert (Gr1 : (2 <= g1 <= 255)%Z) by (apply (Gr 1%Z); lia);
        assert (Gr2 : (2 <= g2 <= 255)%Z) by (apply (Gr 2%Z); lia);
        assert (Gr3 : (2 <= g3 <= 255)%Z) by (apply (Gr 3%Z); lia);
        pose proof (mul_bnd g0 g1 255%Z 255%Z ltac:(lia) ltac:(lia)) as GB01;
        pose proof (mul_bnd (g0 * g1) g2 (255 * 255)%Z 255%Z ltac:(lia) ltac:(lia)) as GB012;
        pose proof (mul_bnd (g0 * g1 * g2) g3 (255 * 255 * 255)%Z 255%Z ltac:(lia) ltac:(lia)) as GB0123;
        pose proof (zprod_len4 gps ltac:(lia)) as Hz ].
    all: destruct Hbw12 as [Hbw1 | Hbw2]; [rewrite Hbw1 in HR | rewrite Hbw2 in HR].
    - run_case 1%nat. + fin_case. + fin_case.
    - run_case 1%nat. + fin_case. + fin_case.
    - run_case 2%nat. + fin_case. + fin_case.
    - run_case 2%nat. + fin_case. + fin_case.
    - run_case 3%nat. + fin_case. + fin_case.
    - run_case 3%nat. + fin_case. + fin_case.
    - run_case 4%nat. + fin_case. + fin_case.
    - run_case 4%nat. + fin_case. + fin_case.
  Qed.
End P.

Theorem init_tables_a2b_Ub_ok : init_tables_a2b_contract SEGS wp2_infoub.
Proof.
  intros data len bs sp tb A maxlen bw ite ote ic gps FPI regs mem rom ret Hra Hret HPRE.
  exact (runs_to_contract SEGS _ ret rom _ (body FPI regs mem rom ret data len bs sp tb A maxlen bw ite ote ic gps Hra Hret HPRE)).
Qed.
End LibItabA2BUb.

Module LibReadA2BUbb.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Lib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibRodata OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib.
Import LibMftcA2BUb LibItabA2BUb LibReadA2BUba.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
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
(* [comment removed for export] *)
Local Ltac ev_simpl E ::=   (* [comment removed for export] *)
  lazymatch goal with |- ?G =>
    let G1 := match tt with | _ => eval unfold E in G | _ => G end in
    let G2 := eval lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in G1 in
    change G2
  end.
Local Ltac ev_simpl_in E H ::= try unfold E in H; lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in H.
#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section Mft2Bits.
Open Scope Z_scope.
Lemma mft2_check : forall hi lo : Z, 0 <= hi < 256 -> 0 <= lo < 256 ->
  (bv_unsigned (alu64 ALU_SRL (alu64 ALU_ADD (alu64 ALU_ADD
       (mul_div M_MUL (Z_to_bv 64 72057594037927936) (Z_to_bv 64 hi))
       (mul_div M_MUL (Z_to_bv 64 281474976710656) (Z_to_bv 64 lo)))
       (Z_to_bv 64 (-1153202979583557632))) (Z_to_bv 64 48)) <? 61441 mod 2 ^ 64) = false ->
  2 <= 256 * hi + lo <= 4096.
Proof.
  intros hi lo Hhi Hlo H.
  apply Z.ltb_ge in H. change (61441 mod 2 ^ 64) with 61441 in H.
  rewrite alu_srl in H. unfold v_srl in H. rewrite !u_add64, !u_mul64, !u_lit64a in H.
  change (48 mod 2 ^ 64 mod 64) with 48 in H.
  rewrite Z.shiftr_div_pow2 in H by lia.
  change (72057594037927936 mod 2 ^ 64) with (2^56) in H.
  change (281474976710656 mod 2 ^ 64) with (2^48) in H.
  change ((-1153202979583557632) mod 2 ^ 64) with (2^64 - 4097 * 2^48) in H.
  rewrite (Z.mod_small hi), (Z.mod_small lo) in H by lia.
  rewrite (Z.mod_small (2^56 * hi)) in H by lia.
  rewrite (Z.mod_small (2^48 * lo)) in H by lia.
  rewrite (Z.mod_small (2^56*hi + 2^48*lo)) in H by lia.
  set (v := 256 * hi + lo) in *.
  replace (2 ^ 56 * hi + 2 ^ 48 * lo + (2 ^ 64 - 4097 * 2 ^ 48)) with ((v - 4097 + 2^16) * 2^48) in H by lia.
  assert (Hv : 0 <= v < 65536) by lia.
  destruct (Z_lt_le_dec v 4097) as [Hl|Hg].
  - rewrite (Z.mod_small ((v - 4097 + 2 ^ 16) * 2 ^ 48)) in H by lia. rewrite Z.div_mul in H by lia.
    rewrite Z.mod_small in H by lia. lia.
  - replace ((v - 4097 + 2 ^ 16) * 2 ^ 48) with ((v - 4097) * 2^48 + 1 * 2^64) in H by lia.
    rewrite Z.mod_add in H by lia. rewrite (Z.mod_small ((v - 4097) * 2 ^ 48)) in H by lia.
    rewrite Z.div_mul in H by lia. rewrite Z.mod_small in H by lia. lia.
Qed.

Lemma mft2_val : forall hi lo : Z, 0 <= hi < 256 -> 0 <= lo < 256 ->
  alu64 ALU_AND (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 256) (Z_to_bv 64 hi))
                                (mul_div M_MUL (Z_to_bv 64 65537) (Z_to_bv 64 lo))) (Z_to_bv 64 65535)
  = Z_to_bv 64 (256 * hi + lo).
Proof.
  intros hi lo Hhi Hlo. rewrite alu_and. unfold v_and. f_equal.
  rewrite !u_add64, !u_mul64, !u_lit64a.
  change (256 mod 2^64) with 256. change (65537 mod 2^64) with 65537. change (65535 mod 2 ^ 64) with (Z.ones 16).
  rewrite (Z.mod_small hi), (Z.mod_small lo) by lia.
  rewrite !Z.mod_small by lia.
  rewrite Z.land_ones by lia. change (2^16) with 65536.
  replace (256 * hi + 65537 * lo) with ((256*hi + lo) + lo * 65536) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
End Mft2Bits.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section RB.
  Variables (FPI0 : FPState) (regs0 : bvmap 5 word) (mem0 rom : word -> option byte) (ret : word).
  Variables (data : word) (len : Z) (bs : list byte) (sp T A : word) (pcs : Z).
  Hypothesis Hra : getr regs0 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HPRE : a2b_pre SEGS wp2_infoub data len bs sp T A pcs FPI0 regs0 mem0.
  Hypothesis Hcanon : canonicalize_contract SEGS wp3_infoub.

  #[local] Abbreviation a := (bv_unsigned A).
  #[local] Abbreviation spv := (bv_unsigned sp).
  #[local] Abbreviation t := (bv_unsigned T).
  #[local] Abbreviation ADM := (adm FPI0 regs0 mem0 ret data len bs sp T A).
  #[local] Abbreviation QP := (Qpost FPI0 regs0 mem0 rom ret data len bs sp T A pcs).
  #[local] Abbreviation CI := (chain_inv data len A).
  #[local] Abbreviation pre_factsI := (pre_facts FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation pre_spI := (pre_sp FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation kn_adm_okI := (kn_adm_ok FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation adm_frameI := (adm_frame FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation base_valsI := (base_vals regs0 ret data len).
  #[local] Abbreviation failkI := (failk FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE).
  #[local] Abbreviation in0I := (in0 FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).

  (* [comment removed for export] *)
  Ltac adm_facts HADM :=
    pose proof HADM as (A2 & A3 & A4 & A8 & A18 & AF & AS & AFR & AD & ARO & AWA & AWS);
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _);
    assert (U2 : bv_unsigned (getr _ 2) = (spv - 176)%Z) by (rewrite A2, u_small by lia; lia).

  Ltac pkg HADM extra kx ktac :=
    lazymatch goal with
    | |- runs_to _ (@mkst ?FPI ?R _ ?M _) _ =>
      set (E := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++
         [ret; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20; getr regs0 21;
          getr regs0 22; getr regs0 23; getr regs0 24; getr regs0 25; getr regs0 26; getr regs0 27;
          data; Z_to_bv 64 len] ++ extra)) (blobs_ev [bs]));
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs]));
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs]));
      pose proof (HR : id _) as HR0; pose proof (HF : id _) as HF0;
      let HK1 := fresh "HK1" in let HK2 := fresh "HK2" in
      pose proof (kn_adm_okI FPI R M extra HADM) as HK1; change (know_ok SEGS E M kn_adm) in HK1;
      assert (HK2 : know_ok SEGS E M kx); [ktac|];
      pose proof (know_ok_app SEGS E M kn_adm kx HK1 HK2) as HK; clear HK1 HK2;
      cbv beta delta [kn_adm app] in HK
    end.

  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.

  Ltac subst_mems :=
    repeat match goal with H : @eq (word -> option byte) ?x _ |- _ => is_var x; subst x end.

  Ltac adm_now HADM HADM1 :=
    subst_mems;
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1, HF : fregs_ok _ ?sfr (@fp_regs ?I1), HF0 : id (fregs_ok _ ?sfr0 (@fp_regs ?I0))
      |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ ?R ?M0 =>
        assert (HADM1 : ADM I1 R1 M1);
        [ apply (adm_frameI I0 I1 R R1 M0 M1 [] HADM);
          [ apply frame_mod_refl
          | apply Forall_nil
          | apply Forall_nil
          | regv HR (2%bv:reg); reflexivity
          | regv HR (3%bv:reg); reflexivity
          | regv HR (4%bv:reg); reflexivity
          | regv HR (8%bv:reg); reflexivity
          | regv HR (18%bv:reg); reflexivity
          | exact (fregs_same_on E sfr0 sfr _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)) ]
        | ]
      end
    end.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition tagc (ty sz : Z) (buf : word) (M : word -> option byte) : Prop :=
    cell32 SEGS M (t + 4) ty /\ cell32 SEGS M (t + 8) sz /\ cell64 SEGS M (t + 16) buf /\
    (4 <= sz)%Z /\ inDATA data len (bv_unsigned buf) sz.

  Lemma pre_tag :
    (t mod 8 = 0)%Z /\ (t + 24 <= 2 ^ 64)%Z /\
    (spv <= t \/ t + 24 <= spv - 352)%Z /\ (t + 24 <= a \/ a + 400 <= t)%Z /\
    (bv_unsigned data + len <= t \/ t + 24 <= bv_unsigned data)%Z.
  Proof using HPRE.
    destruct HPRE as (Hsp & HT & HA & Hpcs & Heob & Hpcs01 & Hdok & Hty & Htag & HTal & HT24 &
                      WA & HAal & HApos & HA400 & Hcurves & Hg & Hspal & WS & Hro & D1 & D2 & D3 & D4 & D5 & D6).
    change (w_ab_d wp2_infoub) with 352%Z in *. repeat split; assumption.
  Qed.

  Lemma tagc_frame : forall ty sz buf M M' rs,
    tagc ty sz buf M -> frame_mod M M' rs -> apart t 24 rs -> tagc ty sz buf M'.
  Proof using HPRE.
    intros ty sz buf M M' rs (C1 & C2 & C3 & H4 & H5) Hf Hap.
    pose proof pre_tag as (Q1 & Q2 & _). pose proof (u64_range T).
    split; [eapply cell32_frame; [exact Hf|exact C1|lia|lia|eapply apart_sub; [exact Hap|lia|lia|lia]]|].
    split; [eapply cell32_frame; [exact Hf|exact C2|lia|lia|eapply apart_sub; [exact Hap|lia|lia|lia]]|].
    split; [eapply cell64_frame; [exact Hf|exact C3|lia|lia|eapply apart_sub; [exact Hap|lia|lia|lia]]|].
    split; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition kn_tag (ty : Z) : list kentry :=
    [KWord (SA (EVar 18) 4) 4 (ELit ty); KWord (SA (EVar 18) 8) 4 (EVar 79); KWord (SA (EVar 18) 16) 8 (EVar 80);
     KRange (EVar 79) 4 67108864; KRange (EVar 80) 1 140737488355328;
     KDisj (SA (EVar 18) 0) 24 (SA (EVar 2) (-176)) 352; KDisj (SA (EVar 18) 0) 24 (SA (EVar 8) 0) 400].

  Lemma kn_tag_ok : forall (FPI : FPState) R M ty sz buf rest,
    ADM FPI R M -> tagc ty sz buf M ->
    know_ok SEGS (Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ base_valsI ++ ([Z_to_bv 64 sz; buf] ++ rest))) (blobs_ev [bs])) M (kn_tag ty).
  Proof using HPRE.
    intros FPI R M ty sz buf rest HADM (C1 & C2 & C3 & H4 & H5). adm_facts HADM.
    pose proof pre_tag as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof (u64_range T). pose proof (u64_range buf).
    destruct H5 as (H5a & H5b & H5c).
    set (E := Env _ _). unfold base_vals in E. unfold kn_tag.
    repeat apply Forall_cons; try apply Forall_nil.
    - eapply (kword_intro SEGS E M (EVar 18) T 4 4 (ELit ty) (Z_to_bv 64 ty));
        [cbn [edenot]; ev_simpl E; exact A18 | reflexivity | lia | lia | lia | lia | exact (proj2 C1)].
    - eapply (kword_intro SEGS E M (EVar 18) T 8 4 (EVar 79) (Z_to_bv 64 sz));
        [cbn [edenot]; ev_simpl E; exact A18 | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | exact (proj2 C2)].
    - eapply (kword_intro SEGS E M (EVar 18) T 16 8 (EVar 80) buf);
        [cbn [edenot]; ev_simpl E; exact A18 | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | exact C3].
    - apply krange_intro; cbn [edenot]; ev_simpl E. destruct C2 as [Hsz _]. rewrite u_small by lia. lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E. lia.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite U2, A18. lia.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite A8, A18. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac pkg_tag HADM HTAG rest kx ktac :=
    lazymatch type of HTAG with tagc ?ty ?sz ?buf _ =>
      pkg HADM ([Z_to_bv 64 sz; buf] ++ rest) (kn_tag ty ++ kx)
        ltac:(apply know_ok_app; [exact (kn_tag_ok _ _ _ ty sz buf rest HADM HTAG) | ktac])
    end.

  (* [comment removed for export] *)
  Lemma f1b : forall (FPI : FPState) R M sz buf r ic,
    ADM FPI R M -> tagc 0x6d667431 sz buf M ->
    getr R 10 = Z_to_bv 64 r -> getr R 21 = Z_to_bv 64 0x6d667000 ->
    (r = 0%Z \/ (r = 1%Z /\ CI ic 0 M)) ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x14eb8) M rom) QP.
  Proof using HPRE Hcanon Hret.
    intros FPI R M sz buf r ic HADM HTAG H10 H21 Hr. adm_facts HADM.
    destruct Hr as [-> | [-> HCI]].
    - pkg_tag HADM HTAG (@nil word) (@nil kentry) ltac:(constructor).
      pin_reg HR (10%bv:reg) (ELit 0%Z) by (cbn [edenot]; exact H10).
      pin_reg HR (21%bv:reg) (ELit 0x6d667000%Z) by (cbn [edenot]; exact H21).
      run_fp 40%nat [0x1525c%Z; 0x15154%Z] noscr true.
      adm_now HADM HADM1. apply (failkI _ _ _ HADM1).
    - pkg_tag HADM HTAG (@nil word) (@nil kentry) ltac:(constructor).
      pin_reg HR (10%bv:reg) (ELit 1%Z) by (cbn [edenot]; exact H10).
      pin_reg HR (21%bv:reg) (ELit 0x6d667000%Z) by (cbn [edenot]; exact H21).
      run_fp 40%nat [0x1525c%Z; 0x15154%Z] noscr true.
      adm_now HADM HADM1. apply (in0I _ _ _ ic 0%Z HADM1). exact HCI.
  Qed.

  Lemma f2b : forall (FPI : FPState) R M sz buf r ic,
    ADM FPI R M -> tagc 0x6d667432 sz buf M ->
    getr R 10 = Z_to_bv 64 r ->
    (r = 0%Z \/ (r = 1%Z /\ CI ic 0 M)) ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x14f7c) M rom) QP.
  Proof using HPRE Hcanon Hret.
    intros FPI R M sz buf r ic HADM HTAG H10 Hr. adm_facts HADM.
    destruct Hr as [-> | [-> HCI]].
    - pkg_tag HADM HTAG (@nil word) (@nil kentry) ltac:(constructor).
      pin_reg HR (10%bv:reg) (ELit 0%Z) by (cbn [edenot]; exact H10).
      run_fp 40%nat [0x1525c%Z; 0x15154%Z] noscr true.
      adm_now HADM HADM1. apply (failkI _ _ _ HADM1).
    - pkg_tag HADM HTAG (@nil word) (@nil kentry) ltac:(constructor).
      pin_reg HR (10%bv:reg) (ELit 1%Z) by (cbn [edenot]; exact H10).
      run_fp 40%nat [0x1525c%Z; 0x15154%Z] noscr true.
      adm_now HADM HADM1. apply (in0I _ _ _ ic 0%Z HADM1). exact HCI.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition mftc_cells (ic g : Z) (M : word -> option byte) : Prop :=
    (1 <= ic <= 4)%Z /\ (2 <= g <= 255)%Z /\
    cell32 SEGS M (a + 144) ic /\ cell32 SEGS M (a + 296) 0 /\ cell32 SEGS M (a + 300) 3 /\
    (forall i, (0 <= i < ic)%Z -> cell8 SEGS M (a + 148 + i) g).

  (* [comment removed for export] *)
  Definition curves0 (M : word -> option byte) : Prop :=
    Forall (fun off => curve_ok SEGS M data len (a + off)) a2b_curve_offsets /\
    exists g8 g16, cell64 SEGS M (a + 128) g8 /\ cell64 SEGS M (a + 136) g16.

  Lemma curves0_frame : forall M M' rs,
    curves0 M -> frame_mod M M' rs ->
    apart (a + 128) 16 rs -> Forall (fun off => apart (a + off) 32 rs) a2b_curve_offsets ->
    curves0 M'.
  Proof using HPRE.
    intros M M' rs [Hall (g8 & g16 & Hg8 & Hg16)] Hf Hap Haps.
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & _).
    split.
    - apply Forall_forall. intros o Ho.
      pose proof (proj1 (Forall_forall _ _) Hall o Ho) as Hc. pose proof (proj1 (Forall_forall _ _) Haps o Ho) as Ha.
      cbv beta in Hc, Ha. pose proof (offsets_bound o Ho) as (B1 & B2 & _).
      eapply curve_ok_frame; [exact Hf|exact Hc|lia|lia|]. eapply apart_sub; [exact Ha|lia|lia|lia].
    - exists g8, g16.
      split; (eapply cell64_frame; [exact Hf|eassumption|lia|lia|eapply apart_sub; [exact Hap|lia|lia|lia]]).
  Qed.

  Ltac offsets_apart_tac :=
    unfold a2b_curve_offsets; repeat (apply Forall_cons; [solve_apart|]); apply Forall_nil.

  (* [comment removed for export] *)
  Lemma itab_pre_mft : forall (FPI : FPState) R M ty sz buf ic g hdr bw ite ote,
    ADM FPI R M -> tagc ty sz buf M -> (hdr <= sz)%Z -> (hdr = 48 \/ hdr = 52)%Z -> mftc_cells ic g M ->
    (bw = 1 \/ bw = 2)%Z -> (2 <= ite <= 4096)%Z -> (2 <= ote <= 4096)%Z ->
    getr R 10 = Z_to_bv 64 (bv_unsigned buf + hdr) -> getr R 11 = Z_to_bv 64 (sz - hdr) ->
    getr R 12 = Z_to_bv 64 bw -> getr R 13 = Z_to_bv 64 ite -> getr R 14 = Z_to_bv 64 ote -> getr R 15 = A ->
    itab_a2b_pre SEGS wp2_infoub data len bs (Z_to_bv 64 (spv - 176)) (Z_to_bv 64 (bv_unsigned buf + hdr)) A
                 (sz - hdr) bw ite ote ic (repeat g (Z.to_nat ic)) FPI R M.
  Proof using HPRE.
    intros FPI R M ty sz buf ic g hdr bw ite ote HADM HTAG Hhdr Hhdr2 (Hic & Hg & C1 & C2 & C3 & Cg) Hbw Hite Hote
           H10 H11 H12 H13 H14 H15. adm_facts HADM.
    pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10 & P11 & P12 & _).
    destruct HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c). pose proof (u64_range buf).
    unfold itab_a2b_pre. cbv zeta. change (w_init_fr wp2_infoub) with 32%Z.
    rewrite !u_small by lia.
    split; [exact A2|]. split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [exact H13|].
    split; [exact H14|]. split; [exact H15|]. split; [exact AD|]. split; [lia|].
    split; [unfold inDATA; lia|].
    split; [exact Hbw|]. split; [exact Hite|]. split; [exact Hote|]. split; [exact Hic|].
    split; [rewrite repeat_length; lia|].
    split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; subst x; lia|].
    split; [exact C1|]. split; [exact C3|].
    split; [intros i Hi; rewrite nth_repeat_lt by lia; apply Cg; lia|].
    split; [rewrite Z.add_0_r; exact AWA|]. split; [exact P2|]. split; [lia|].
    split; [eapply writable_sub; [exact AWS|lia|lia|lia]|].
    lia.
  Qed.

  (* [comment removed for export] *)
  Lemma adm_itab : forall (FPI FPI' : FPState) R R' M M' ic rs,
    ADM FPI R M -> (1 <= ic <= 4)%Z ->
    (rs = [(Z_to_bv 64 (spv - 176 - 32), 32%Z)] \/
     rs = [(Z_to_bv 64 (spv - 176 - 32), 32%Z); (Z_to_bv 64 a, (32 * ic)%Z); (Z_to_bv 64 (a + 128), 16%Z); (Z_to_bv 64 (a + 304), 96%Z)]) ->
    frame_mod M M' rs -> regs_kept abi_kept R R' ->
    (forall r, In r abi_fkept -> reg_get (fp_regs (FPState:=FPI')) r = reg_get (fp_regs (FPState:=FPI)) r) ->
    ADM FPI' R' M' /\ (forall ty sz buf, tagc ty sz buf M -> tagc ty sz buf M').
  Proof using HPRE.
    intros FPI FPI' R R' M M' ic rs HADM Hic Hrs Hf Hk Hfk.
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _).
    pose proof pre_tag as (Q1 & Q2 & Q3 & Q4 & Q5).
    split.
    - apply (adm_frameI FPI FPI' R R' M M' rs HADM Hf).
      + destruct Hrs as [-> | ->]; unfold BIG; solve_within.
      + destruct Hrs as [-> | ->]; solve_apart.
      + apply Hk; cbn; repeat (first [left; reflexivity | right]). + apply Hk; cbn; repeat (first [left; reflexivity | right]). + apply Hk; cbn; repeat (first [left; reflexivity | right]). + apply Hk; cbn; repeat (first [left; reflexivity | right]). + apply Hk; cbn; repeat (first [left; reflexivity | right]).
      + exact Hfk.
    - intros ty sz buf HT. eapply tagc_frame; [exact HT|exact Hf|]. destruct Hrs as [-> | ->]; solve_apart.
  Qed.

  (* [comment removed for export] *)
  Lemma chain_from_itab : forall M M' ic g bw,
    mftc_cells ic g M -> curves0 M ->
    frame_mod M M' [(Z_to_bv 64 (spv - 176 - 32), 32%Z); (Z_to_bv 64 a, (32 * ic)%Z); (Z_to_bv 64 (a + 128), 16%Z); (Z_to_bv 64 (a + 304), 96%Z)] ->
    (forall i, (0 <= i < ic)%Z -> curve_ok SEGS M' data len (a + 32 * i)) ->
    (forall i, (0 <= i < 3)%Z -> curve_ok SEGS M' data len (a + 304 + 32 * i)) ->
    (exists g8 g16 : word,
        cell64 SEGS M' (a + 128) g8 /\ cell64 SEGS M' (a + 136) g16 /\
        (bw = 1%Z -> bv_unsigned g16 = 0%Z /\ inDATA data len (bv_unsigned g8) (3 * zprod (repeat g (Z.to_nat ic)))) /\
        (bw = 2%Z -> bv_unsigned g8 = 0%Z /\ inDATA data len (bv_unsigned g16) (2 * (3 * zprod (repeat g (Z.to_nat ic)))))) ->
    (bw = 1 \/ bw = 2)%Z ->
    CI ic 0 M'.
  Proof using HPRE ret rom.
    intros M M' ic g bw (Hic & Hg & C1 & C2 & C3 & Cg) [Hall _] Hf Hin Hout (g8 & g16 & Hg8 & Hg16 & Hbw1 & Hbw2) Hbw.
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _).
    assert (AP : forall lo n, (a + 32 * ic <= lo)%Z -> (lo + n <= a + 128 \/ a + 144 <= lo)%Z -> (lo + n <= a + 304)%Z -> (0 <= n)%Z ->
              apart lo n [(Z_to_bv 64 (spv - 176 - 32), 32%Z); (Z_to_bv 64 a, (32 * ic)%Z); (Z_to_bv 64 (a + 128), 16%Z); (Z_to_bv 64 (a + 304), 96%Z)]).
    { intros lo n H1 H2 H3 H4. solve_apart. }
    split; [eapply cell32_frame; [exact Hf|exact C1|lia|lia|apply AP; lia]|].
    split; [eapply cell32_frame; [exact Hf|exact C2|lia|lia|apply AP; lia]|].
    split; [eapply cell32_frame; [exact Hf|exact C3|lia|lia|apply AP; lia]|].
    split; [lia|]. split; [left; reflexivity|].
    split.
    - unfold a2b_curve_offsets.
      assert (X : forall o, In o [0; 32; 64; 96]%Z -> curve_ok SEGS M' data len (a + o)).
      { intros o Ho.
        destruct (Z_lt_le_dec o (32 * ic)) as [Hlt|Hge].
        - cbn in Ho. 
          assert (Hoi : exists i, (0 <= i < ic)%Z /\ o = (32 * i)%Z).
          { repeat (destruct Ho as [<-|Ho]); [exists 0%Z|exists 1%Z|exists 2%Z|exists 3%Z|destruct Ho]; lia. }
          destruct Hoi as (i & Hi & ->). apply Hin. exact Hi.
        - assert (Hoin : In o a2b_curve_offsets) by (cbn in Ho |- *; clear - Ho; tauto).
          pose proof (proj1 (Forall_forall _ _) Hall o Hoin) as Hc. cbv beta in Hc.
          pose proof (offsets_bound o Hoin) as (B1 & B2 & _).
          assert (o + 32 <= 128)%Z by (cbn in Ho; repeat (destruct Ho as [<-|Ho]); [..|destruct Ho]; lia).
          eapply curve_ok_frame; [exact Hf|exact Hc|lia|lia|apply AP; lia]. }
      assert (Y : forall o, In o [152; 184; 216]%Z -> curve_ok SEGS M' data len (a + o)).
      { intros o Ho.
        assert (Hoin : In o a2b_curve_offsets) by (cbn in Ho |- *; clear - Ho; tauto).
        pose proof (proj1 (Forall_forall _ _) Hall o Hoin) as Hc. cbv beta in Hc.
        assert (152 <= o /\ o + 32 <= 248)%Z by (cbn in Ho; repeat (destruct Ho as [<-|Ho]); [..|destruct Ho]; lia).
        eapply curve_ok_frame; [exact Hf|exact Hc|lia|lia|apply AP; lia]. }
      repeat apply Forall_cons; try apply Forall_nil;
        first [ apply X; clear; cbn; tauto | apply Y; clear; cbn; tauto
              | replace (a + 304)%Z with (a + 304 + 32 * 0)%Z by lia; apply Hout; lia
              | replace (a + 336)%Z with (a + 304 + 32 * 1)%Z by lia; apply Hout; lia
              | replace (a + 368)%Z with (a + 304 + 32 * 2)%Z by lia; apply Hout; lia ].
    - exists ic, 3%Z, (repeat g (Z.to_nat ic)), g8, g16.
      split; [eapply cell32_frame; [exact Hf|exact C1|lia|lia|apply AP; lia]|].
      split; [eapply cell32_frame; [exact Hf|exact C3|lia|lia|apply AP; lia]|].
      split; [lia|]. split; [rewrite repeat_length; lia|].
      split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; subst x; lia|].
      split.
      { intros i Hi. rewrite nth_repeat_lt by lia.
        eapply cell8_frame; [exact Hf|apply Cg; exact Hi|lia|lia|apply AP; lia]. }
      split; [exact Hg8|]. split; [exact Hg16|]. split; [reflexivity|].
      intros _. destruct Hbw as [Hb|Hb]; [destruct (Hbw1 Hb) as [Z1 Z2] | destruct (Hbw2 Hb) as [Z1 Z2]]; split; intros Hnz.
      + exact Z2. + exfalso. apply Hnz. exact Z1. + exfalso. apply Hnz. exact Z1. + exact Z2.
  Qed.

  (* [comment removed for export] *)
  Lemma f1 : forall (FPI : FPState) R M sz buf r,
    ADM FPI R M -> tagc 0x6d667431 sz buf M -> (48 <= sz)%Z ->
    getr R 20 = buf -> getr R 21 = Z_to_bv 64 0x6d667000 -> getr R 10 = Z_to_bv 64 r ->
    (r = 0%Z \/ (r = 1%Z /\ exists ic g, mftc_cells ic g M)) -> curves0 M ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x14e94) M rom) QP.
  Proof using HPRE Hcanon Hret.
    intros FPI R M sz buf r HADM HTAG Hsz H20 H21 H10 Hr HC0. adm_facts HADM.
    pose proof HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c). pose proof (u64_range buf).
    destruct Hr as [-> | (-> & ic & g & HMC)].
    - pkg_tag HADM HTAG (@nil word) (@nil kentry) ltac:(constructor).
      pin_reg HR (10%bv:reg) (ELit 0%Z) by (cbn [edenot]; exact H10).
      run_fp 20%nat [0x14eb8%Z] noscr true.
      adm_now HADM HADM1.
      apply (f1b _ _ _ sz buf 0%Z 0%Z HADM1); [exact HTAG | regv HR (10%bv:reg); reflexivity
        | regv HR (21%bv:reg); exact H21 | left; reflexivity].
    - pose proof HMC as (Hic & Hg & _).
      pkg_tag HADM HTAG (@nil word) [KRange (EVar 79) 48 67108864]
        ltac:(constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia | constructor]).
      pin_reg HR (10%bv:reg) (ELit 1%Z) by (cbn [edenot]; exact H10).
      pin_reg HR (20%bv:reg) (EVar 80) by (cbn [edenot]; ev_simpl E; exact H20).
      run_fp 30%nat [0x14eb8%Z; 0x16704%Z] noscr true.
      adm_now HADM HADM1.
      eapply rt_call.
      { eapply (init_tables_a2b_Ub_ok data len bs (Z_to_bv 64 (spv - 176)) (Z_to_bv 64 (bv_unsigned buf + 48)) A
                  (sz - 48)%Z 1%Z 256%Z 256%Z ic (repeat g (Z.to_nat ic)) _ _ _ rom (Z_to_bv 64 0x14eb8)).
        - regv HR (1%bv:reg). reflexivity.
        - apply ret_ok_even. rewrite u_small by lia. reflexivity.
        - eapply (itab_pre_mft _ _ _ 0x6d667431%Z sz buf ic g 48%Z); try first [exact HADM1 | lia].
          + exact HTAG.
          + exact HMC.
          + regv_lin HR (10%bv:reg). f_equal. lia.
          + regv_lin HR (11%bv:reg). rewrite u_small by lia. f_equal. lia.
          + regv HR (12%bv:reg). reflexivity.
          + regv HR (13%bv:reg). reflexivity.
          + regv HR (14%bv:reg). reflexivity.
          + regv HR (15%bv:reg). exact A8. }
      cbv beta. intros FPI' R' M' (Hkeep & Hfkeep & r' & H10' & Hpost).
      change (w_init_fr wp2_infoub) with 32%Z in Hpost. rewrite (u_small (spv - 176)) in Hpost by lia.
      destruct Hpost as [[-> Hfr] | [-> (Hfr & Hin & Hout & Hgrid)]].
      + destruct (adm_itab _ FPI' _ R' _ M' ic _ HADM1 Hic (or_introl eq_refl) Hfr Hkeep Hfkeep) as [HADM' HT'].
        apply (f1b FPI' R' M' sz buf 0%Z 0%Z HADM'); [apply HT'; exact HTAG | exact H10'
          | rewrite (Hkeep 21%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); regv HR (21%bv:reg); exact H21 | left; reflexivity].
      + destruct (adm_itab _ FPI' _ R' _ M' ic _ HADM1 Hic (or_intror eq_refl) Hfr Hkeep Hfkeep) as [HADM' HT'].
        apply (f1b FPI' R' M' sz buf 1%Z ic HADM'); [apply HT'; exact HTAG | exact H10'
          | rewrite (Hkeep 21%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); regv HR (21%bv:reg); exact H21 | right; split; [reflexivity|]].
        eapply (chain_from_itab _ M' ic g 1%Z);
          [exact HMC | exact HC0 | exact Hfr | exact Hin | exact Hout | exact Hgrid | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma data_byte : forall M p, data_ok M data len bs ->
    (bv_unsigned data <= p)%Z -> (p < bv_unsigned data + len)%Z ->
    cell SEGS M p 1 (Z_to_bv 64 (bs_byte bs (p - bv_unsigned data))).
  Proof using . intros M p HD H1 H2. unfold cell. apply (data_byte_cell SEGS M data len bs p HD H1 H2). Qed.

  (* [comment removed for export] *)
  Lemma f2 : forall (FPI : FPState) R M sz buf r,
    ADM FPI R M -> tagc 0x6d667432 sz buf M -> (52 <= sz)%Z ->
    getr R 20 = buf -> getr R 10 = Z_to_bv 64 r ->
    (r = 0%Z \/ (r = 1%Z /\ exists ic g, mftc_cells ic g M)) -> curves0 M ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x14eec) M rom) QP.
  Proof using HPRE Hcanon Hret.
    intros FPI R M sz buf r HADM HTAG Hsz H20 H10 Hr HC0. adm_facts HADM.
    pose proof HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c). pose proof (u64_range buf).
    destruct Hr as [-> | (-> & ic & g & HMC)].
    - pkg_tag HADM HTAG (@nil word) (@nil kentry) ltac:(constructor).
      pin_reg HR (10%bv:reg) (ELit 0%Z) by (cbn [edenot]; exact H10).
      run_fp 20%nat [0x14f7c%Z] noscr true.
      adm_now HADM HADM1.
      apply (f2b _ _ _ sz buf 0%Z 0%Z HADM1); [exact HTAG | regv HR (10%bv:reg); reflexivity | left; reflexivity].
    - pose proof HMC as (Hic & Hg & _).
      set (b48 := bs_byte bs (bv_unsigned buf + 48 - bv_unsigned data)).
      set (b49 := bs_byte bs (bv_unsigned buf + 49 - bv_unsigned data)).
      set (b50 := bs_byte bs (bv_unsigned buf + 50 - bv_unsigned data)).
      set (b51 := bs_byte bs (bv_unsigned buf + 51 - bv_unsigned data)).
      pose proof (bs_byte_range bs (bv_unsigned buf + 48 - bv_unsigned data)) as R48.
      pose proof (bs_byte_range bs (bv_unsigned buf + 49 - bv_unsigned data)) as R49.
      pose proof (bs_byte_range bs (bv_unsigned buf + 50 - bv_unsigned data)) as R50.
      pose proof (bs_byte_range bs (bv_unsigned buf + 51 - bv_unsigned data)) as R51.
      fold b48 in R48. fold b49 in R49. fold b50 in R50. fold b51 in R51.
      pkg_tag HADM HTAG [Z_to_bv 64 b48; Z_to_bv 64 b49; Z_to_bv 64 b50; Z_to_bv 64 b51]
        [KRange (EVar 79) 52 67108864;
         KWord (SA (EVar 80) 48) 1 (EVar 81); KWord (SA (EVar 80) 49) 1 (EVar 82);
         KWord (SA (EVar 80) 50) 1 (EVar 83); KWord (SA (EVar 80) 51) 1 (EVar 84);
         KRange (EVar 81) 0 255; KRange (EVar 82) 0 255; KRange (EVar 83) 0 255; KRange (EVar 84) 0 255]
        ltac:(repeat apply Forall_cons; try apply Forall_nil;
              [ apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia
              | eapply (kword_intro SEGS E _ (EVar 80) buf 48 1 (EVar 81)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply data_byte; [exact AD|lia|lia]]
              | eapply (kword_intro SEGS E _ (EVar 80) buf 49 1 (EVar 82)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply data_byte; [exact AD|lia|lia]]
              | eapply (kword_intro SEGS E _ (EVar 80) buf 50 1 (EVar 83)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply data_byte; [exact AD|lia|lia]]
              | eapply (kword_intro SEGS E _ (EVar 80) buf 51 1 (EVar 84)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply data_byte; [exact AD|lia|lia]]
              | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia
              | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia
              | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia
              | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia ]).
      pin_reg HR (10%bv:reg) (ELit 1%Z) by (cbn [edenot]; exact H10).
      pin_reg HR (20%bv:reg) (EVar 80) by (cbn [edenot]; ev_simpl E; exact H20).
      run_fp 60%nat [0x14f7c%Z; 0x16704%Z] noscr true.
      branch_case as Hc1.
      { adm_now HADM HADM1.
        apply (f2b _ _ _ sz buf 0%Z 0%Z HADM1); [exact HTAG | regv HR (10%bv:reg); reflexivity | left; reflexivity]. }
      br_simpl_in E Hc1. apply (mft2_check b48 b49 R48 R49) in Hc1.
      run_fp 60%nat [0x14f7c%Z; 0x16704%Z] noscr true.
      branch_case as Hc2.
      { adm_now HADM HADM1.
        apply (f2b _ _ _ sz buf 0%Z 0%Z HADM1); [exact HTAG | regv HR (10%bv:reg); reflexivity | left; reflexivity]. }
      br_simpl_in E Hc2. apply (mft2_check b50 b51 R50 R51) in Hc2.
      run_fp 60%nat [0x14f7c%Z; 0x16704%Z] noscr true.
      adm_now HADM HADM1.
      eapply rt_call.
      { eapply (init_tables_a2b_Ub_ok data len bs (Z_to_bv 64 (spv - 176)) (Z_to_bv 64 (bv_unsigned buf + 52)) A
                  (sz - 52)%Z 2%Z (256 * b48 + b49)%Z (256 * b50 + b51)%Z ic (repeat g (Z.to_nat ic)) _ _ _ rom (Z_to_bv 64 0x14f7c)).
        - regv HR (1%bv:reg). reflexivity.
        - apply ret_ok_even. rewrite u_small by lia. reflexivity.
        - eapply (itab_pre_mft _ _ _ 0x6d667432%Z sz buf ic g 52%Z); try first [exact HADM1 | lia].
          + exact HTAG.
          + exact HMC.
          + regv_lin HR (10%bv:reg). f_equal. lia.
          + regv_lin HR (11%bv:reg). rewrite u_small by lia. f_equal. lia.
          + regv HR (12%bv:reg). reflexivity.
          + regv HR (13%bv:reg). exact (mft2_val b48 b49 R48 R49).
          + regv HR (14%bv:reg). exact (mft2_val b50 b51 R50 R51).
          + regv HR (15%bv:reg). exact A8. }
      cbv beta. intros FPI' R' M' (Hkeep & Hfkeep & r' & H10' & Hpost).
      change (w_init_fr wp2_infoub) with 32%Z in Hpost. rewrite (u_small (spv - 176)) in Hpost by lia.
      destruct Hpost as [[-> Hfr] | [-> (Hfr & Hin & Hout & Hgrid)]].
      + destruct (adm_itab _ FPI' _ R' _ M' ic _ HADM1 Hic (or_introl eq_refl) Hfr Hkeep Hfkeep) as [HADM' HT'].
        apply (f2b FPI' R' M' sz buf 0%Z 0%Z HADM'); [apply HT'; exact HTAG | exact H10' | left; reflexivity].
      + destruct (adm_itab _ FPI' _ R' _ M' ic _ HADM1 Hic (or_intror eq_refl) Hfr Hkeep Hfkeep) as [HADM' HT'].
        apply (f2b FPI' R' M' sz buf 1%Z ic HADM'); [apply HT'; exact HTAG | exact H10' | right; split; [reflexivity|]].
        eapply (chain_from_itab _ M' ic g 2%Z);
          [exact HMC | exact HC0 | exact Hfr | exact Hin | exact Hout | exact Hgrid | lia].
  Qed.
End RB.
End LibReadA2BUbb.

Module LibReadA2BUbc.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Lib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibRodata OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibBswap.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfKc.
Import LibReadA2BUba LibReadA2BUbb.
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
#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ZHelpers.
Open Scope Z_scope.

Lemma u_sltu64 : forall x y : word,
  bv_unsigned (alu64 ALU_SLTU x y) = (if bv_unsigned x <? bv_unsigned y then 1 else 0).
Proof.
  intros x y. rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu.
  destruct (bv_unsigned x <? bv_unsigned y); rewrite u_lit64a; reflexivity.
Qed.

Lemma slack_val : forall bw : word, (bv_unsigned bw = 1 \/ bv_unsigned bw = 2) ->
  alu64 ALU_ADD (alu64 ALU_SLTU (Z_to_bv 64 0) (alu64 ALU_ADD bw (Z_to_bv 64 (-1)))) (Z_to_bv 64 1) = bw.
Proof.
  intros bw Hbw. apply bv_eq. rewrite u_add64, u_sltu64, u_add64, !u_lit64a.
  destruct Hbw as [H|H]; rewrite H; reflexivity.
Qed.

Lemma u_mul_small : forall (x y : word) (bx by_ : Z),
  0 <= bv_unsigned x <= bx -> 0 <= bv_unsigned y <= by_ -> bx * by_ < 2 ^ 64 ->
  bv_unsigned (mul_div M_MUL x y) = bv_unsigned x * bv_unsigned y /\
  0 <= bv_unsigned x * bv_unsigned y <= bx * by_.
Proof.
  intros x y bx by_ Hx Hy Hb.
  pose proof (mul_bnd _ _ _ _ Hx Hy) as B.
  rewrite u_mul64, Z.mod_small by lia. split; [reflexivity | exact B].
Qed.

Lemma u3 : bv_unsigned (Z_to_bv 64 3) = 3.
Proof. apply u_small. lia. Qed.

Lemma uP0 : forall bw : word, bv_unsigned bw <= 255 ->
  bv_unsigned (mul_div M_MUL (Z_to_bv 64 3) bw) = 3 * bv_unsigned bw /\ 0 <= 3 * bv_unsigned bw <= 765.
Proof.
  intros bw H. pose proof (u64_range bw).
  destruct (u_mul_small (Z_to_bv 64 3) bw 3 255) as [E B]; [rewrite u3; lia | lia | lia |].
  rewrite u3 in E, B. split; [exact E | lia].
Qed.

Lemma uP1 : forall bw g0 : word, bv_unsigned bw <= 255 -> bv_unsigned g0 <= 255 ->
  bv_unsigned (mul_div M_MUL (mul_div M_MUL (Z_to_bv 64 3) bw) g0) = 3 * bv_unsigned bw * bv_unsigned g0 /\
  0 <= 3 * bv_unsigned bw * bv_unsigned g0 <= 195075.
Proof.
  intros bw g0 Hb H0. pose proof (u64_range g0). destruct (uP0 bw Hb) as [E0 B0].
  destruct (u_mul_small (mul_div M_MUL (Z_to_bv 64 3) bw) g0 765 255) as [E B]; [rewrite E0; exact B0 | lia | lia |].
  rewrite E0 in E, B. split; [exact E | lia].
Qed.

Lemma uP2 : forall bw g0 g1 : word, bv_unsigned bw <= 255 -> bv_unsigned g0 <= 255 -> bv_unsigned g1 <= 255 ->
  bv_unsigned (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (Z_to_bv 64 3) bw) g0) g1)
    = 3 * bv_unsigned bw * bv_unsigned g0 * bv_unsigned g1 /\
  0 <= 3 * bv_unsigned bw * bv_unsigned g0 * bv_unsigned g1 <= 49744125.
Proof.
  intros bw g0 g1 Hb H0 H1. pose proof (u64_range g1). destruct (uP1 bw g0 Hb H0) as [E0 B0].
  destruct (u_mul_small (mul_div M_MUL (mul_div M_MUL (Z_to_bv 64 3) bw) g0) g1 195075 255) as [E B];
    [rewrite E0; exact B0 | lia | lia |].
  rewrite E0 in E, B. split; [exact E | lia].
Qed.

Lemma uP3 : forall bw g0 g1 g2 : word, bv_unsigned bw <= 255 -> bv_unsigned g0 <= 255 -> bv_unsigned g1 <= 255 ->
  bv_unsigned g2 <= 255 ->
  bv_unsigned (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (Z_to_bv 64 3) bw) g0) g1) g2)
    = 3 * bv_unsigned bw * bv_unsigned g0 * bv_unsigned g1 * bv_unsigned g2 /\
  0 <= 3 * bv_unsigned bw * bv_unsigned g0 * bv_unsigned g1 * bv_unsigned g2 <= 12684751875.
Proof.
  intros bw g0 g1 g2 Hb H0 H1 H2. pose proof (u64_range g2). destruct (uP2 bw g0 g1 Hb H0 H1) as [E0 B0].
  destruct (u_mul_small (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (Z_to_bv 64 3) bw) g0) g1) g2 49744125 255) as [E B];
    [rewrite E0; exact B0 | lia | lia |].
  rewrite E0 in E, B. split; [exact E | lia].
Qed.

Lemma uP4 : forall bw g0 g1 g2 g3 : word, bv_unsigned bw <= 255 -> bv_unsigned g0 <= 255 -> bv_unsigned g1 <= 255 ->
  bv_unsigned g2 <= 255 -> bv_unsigned g3 <= 255 ->
  bv_unsigned (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (Z_to_bv 64 3) bw) g0) g1) g2) g3)
    = 3 * bv_unsigned bw * bv_unsigned g0 * bv_unsigned g1 * bv_unsigned g2 * bv_unsigned g3 /\
  0 <= 3 * bv_unsigned bw * bv_unsigned g0 * bv_unsigned g1 * bv_unsigned g2 * bv_unsigned g3 <= 3234611728125.
Proof.
  intros bw g0 g1 g2 g3 Hb H0 H1 H2 H3. pose proof (u64_range g3). destruct (uP3 bw g0 g1 g2 Hb H0 H1 H2) as [E0 B0].
  destruct (u_mul_small (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (Z_to_bv 64 3) bw) g0) g1) g2) g3 12684751875 255) as [E B];
    [rewrite E0; exact B0 | lia | lia |].
  rewrite E0 in E, B. split; [exact E | lia].
Qed.

Lemma zprod_bnd : forall l, Forall (fun g => 0 <= g <= 255) l -> 0 <= zprod l <= 255 ^ (Z.of_nat (length l)).
Proof.
  induction l as [|x r IH]; intros H; cbn [zprod length].
  - cbn. lia.
  - apply Forall_cons_iff in H as [H1 H2]. specialize (IH H2).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    pose proof (mul_bnd x (zprod r) 255 (255 ^ Z.of_nat (length r)) H1 IH). lia.
Qed.

(* [comment removed for export] *)
Lemma sltu_0_pos : forall w : word, 0 < bv_unsigned w -> alu64 ALU_SLTU (Z_to_bv 64 0) w = Z_to_bv 64 1.
Proof.
  intros w Hw. apply bv_eq. rewrite u_sltu64, !u_lit64a. change (0 mod 2 ^ 64) with 0.
  destruct (Z.ltb_spec 0 (bv_unsigned w)); [reflexivity | lia].
Qed.
Lemma sltiu_ge1 : forall w : word, 1 <= bv_unsigned w -> alu64 ALU_SLTU w (Z_to_bv 64 1) = Z_to_bv 64 0.
Proof.
  intros w Hw. apply bv_eq. rewrite u_sltu64, !u_lit64a. change (1 mod 2 ^ 64) with 1.
  destruct (Z.ltb_spec (bv_unsigned w) 1); [lia | reflexivity].
Qed.
End ZHelpers.

Section RC.
  Variables (FPI0 : FPState) (regs0 : bvmap 5 word) (mem0 rom : word -> option byte) (ret : word).
  Variables (data : word) (len : Z) (bs : list byte) (sp T A : word) (pcs : Z).
  Hypothesis Hra : getr regs0 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HPRE : a2b_pre SEGS wp2_infoub data len bs sp T A pcs FPI0 regs0 mem0.
  Hypothesis Hcanon : canonicalize_contract SEGS wp3_infoub.

  #[local] Abbreviation a := (bv_unsigned A).
  #[local] Abbreviation spv := (bv_unsigned sp).
  #[local] Abbreviation t := (bv_unsigned T).
  #[local] Abbreviation ADM := (adm FPI0 regs0 mem0 ret data len bs sp T A).
  #[local] Abbreviation QP := (Qpost FPI0 regs0 mem0 rom ret data len bs sp T A pcs).
  #[local] Abbreviation CI := (chain_inv data len A).
  #[local] Abbreviation TAGC := (tagc data len T).
  #[local] Abbreviation pre_factsI := (pre_facts FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation pre_tagI := (pre_tag FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation pre_spI := (pre_sp FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation kn_adm_okI := (kn_adm_ok FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation kn_tag_okI := (kn_tag_ok FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation adm_frameI := (adm_frame FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation base_valsI := (base_vals regs0 ret data len).
  #[local] Abbreviation failkI := (failk FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE).
  #[local] Abbreviation in0I := (in0 FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).

  (* [comment removed for export] *)
  Ltac adm_facts HADM :=
    pose proof HADM as (A2 & A3 & A4 & A8 & A18 & AF & AS & AFR & AD & ARO & AWA & AWS);
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _);
    assert (U2 : bv_unsigned (getr _ 2) = (spv - 176)%Z) by (rewrite A2, u_small by lia; lia).

  Ltac pkg HADM extra kx ktac :=
    lazymatch goal with
    | |- runs_to _ (@mkst ?FPI ?R _ ?M _) _ =>
      set (E := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++
         [ret; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20; getr regs0 21;
          getr regs0 22; getr regs0 23; getr regs0 24; getr regs0 25; getr regs0 26; getr regs0 27;
          data; Z_to_bv 64 len] ++ extra)) (blobs_ev [bs]));
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs]));
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs]));
      pose proof (HR : id _) as HR0; pose proof (HF : id _) as HF0;
      let HK1 := fresh "HK1" in let HK2 := fresh "HK2" in
      pose proof (kn_adm_okI FPI R M extra HADM) as HK1; change (know_ok SEGS E M kn_adm) in HK1;
      assert (HK2 : know_ok SEGS E M kx); [ktac|];
      pose proof (know_ok_app SEGS E M kn_adm kx HK1 HK2) as HK; clear HK1 HK2;
      cbv beta delta [kn_adm app] in HK
    end.

  Ltac pkg_tag HADM HTAG rest kx ktac :=
    lazymatch type of HTAG with tagc _ _ _ ?ty ?sz ?buf _ =>
      pkg HADM ([Z_to_bv 64 sz; buf] ++ rest) (kn_tag ty ++ kx)
        ltac:(apply know_ok_app; [exact (kn_tag_okI _ _ _ ty sz buf rest HADM HTAG) | ktac])
    end.

  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.

  Ltac subst_mems :=
    repeat match goal with H : @eq (word -> option byte) ?x _ |- _ => is_var x; subst x end.

  Ltac adm_now HADM HADM1 :=
    subst_mems;
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1, HF : fregs_ok _ ?sfr (@fp_regs ?I1), HF0 : id (fregs_ok _ ?sfr0 (@fp_regs ?I0))
      |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ ?R ?M0 =>
        assert (HADM1 : ADM I1 R1 M1);
        [ apply (adm_frameI I0 I1 R R1 M0 M1 [] HADM);
          [ apply frame_mod_refl
          | apply Forall_nil
          | apply Forall_nil
          | regv HR (2%bv:reg); reflexivity
          | regv HR (3%bv:reg); reflexivity
          | regv HR (4%bv:reg); reflexivity
          | regv HR (8%bv:reg); reflexivity
          | regv HR (18%bv:reg); reflexivity
          | exact (fregs_same_on E sfr0 sfr _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)) ]
        | ]
      end
    end.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition bb (buf : word) (i : Z) : Z := bs_byte bs (bv_unsigned buf + i - bv_unsigned data).
  Definition W (buf : word) (i : Z) : word := Z_to_bv 64 (bb buf i).

  Lemma bb_range : forall buf i, (0 <= bb buf i < 256)%Z.
  Proof. intros. unfold bb. apply bs_byte_range. Qed.

  (* [comment removed for export] *)
  Definition curves10 (M : word -> option byte) : Prop :=
    Forall (fun off => curve_ok SEGS M data len (a + off)) a2b_curve_offsets.

  (* [comment removed for export] *)
  Definition mab_cells (ic mc : Z) (M : word -> option byte) : Prop :=
    cell32 SEGS M (a + 144) ic /\ cell32 SEGS M (a + 300) 3 /\ cell32 SEGS M (a + 296) mc /\
    (0 <= ic <= 4)%Z /\ (mc = 0 \/ mc = 3)%Z.

  #[local] Abbreviation eobw := (Z_to_bv 64 (bv_unsigned data + len)).

  Lemma uW : forall buf i, bv_unsigned (W buf i) = bb buf i.
  Proof. intros. unfold W. pose proof (bb_range buf i). rewrite u_small by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition gsl (buf : word) (co : Z) (n : nat) : list Z :=
    firstn n [bb buf co; bb buf (co + 1); bb buf (co + 2); bb buf (co + 3)]%Z.
  Definition Pval (buf : word) (co : Z) (n : nat) : Z := (3 * bb buf (co + 16) * zprod (gsl buf co n))%Z.

  Lemma gsl_bnd : forall buf co n, Forall (fun g => 0 <= g <= 255)%Z (gsl buf co n).
  Proof.
    intros buf co n. unfold gsl.
    pose proof (bb_range buf co). pose proof (bb_range buf (co + 1)).
    pose proof (bb_range buf (co + 2)). pose proof (bb_range buf (co + 3)).
    destruct n as [|[|[|[|n]]]]; cbn [firstn]; rewrite ?firstn_nil; repeat apply Forall_cons; try apply Forall_nil; lia.
  Qed.

  Lemma Pval_bnd : forall buf co n, (n <= 4)%nat -> (0 <= Pval buf co n <= 3234611728125)%Z.
  Proof.
    intros buf co n Hn. unfold Pval.
    pose proof (bb_range buf (co + 16)).
    pose proof (zprod_bnd _ (gsl_bnd buf co n)) as B.
    assert (L : (Z.of_nat (length (gsl buf co n)) <= 4)%Z).
    { unfold gsl. rewrite length_firstn. cbn [length]. lia. }
    assert (B4 : (255 ^ Z.of_nat (length (gsl buf co n)) <= 255 ^ 4)%Z) by (apply Z.pow_le_mono_r; lia).
    change (255 ^ 4)%Z with 4228250625%Z in B4.
    pose proof (mul_bnd (3 * bb buf (co + 16)) (zprod (gsl buf co n)) 765 4228250625 ltac:(lia) ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma curves10_frame1 : forall M M' (w : word) n,
    curves10 M -> frame_mod M M' [(w, n)] ->
    (forall o, In o a2b_curve_offsets -> (bv_unsigned w + n <= a + o \/ a + o + 24 <= bv_unsigned w)%Z) ->
    curves10 M'.
  Proof.
    intros M M' w n HC Hf Ho. pose proof pre_factsI as (P1 & P2 & P3 & P4 & _).
    unfold curves10 in *. apply Forall_forall. intros o Hin.
    pose proof (proj1 (Forall_forall _ _) HC o Hin) as Hc. cbv beta in Hc.
    pose proof (offsets_bound o Hin) as (B1 & B2 & _).
    eapply curve_ok_frame; [exact Hf | exact Hc | lia | lia |].
    unfold apart. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. apply Ho. exact Hin.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac mods_in H :=
    repeat match type of H with context [ (?x mod ?m)%Z ] =>
      lazymatch x with context [ (_ mod _)%Z ] => fail | _ => rewrite (Z.mod_small x m) in H by lia end end.
  Ltac mods_goal :=
    repeat match goal with |- context [ (?x mod ?m)%Z ] =>
      lazymatch x with context [ (_ mod _)%Z ] => fail | _ => rewrite (Z.mod_small x m) by lia end end.

  (* [comment removed for export] *)
  Ltac zbool H :=
    first [ apply Z.ltb_lt in H | apply Z.ltb_ge in H | apply Z.eqb_eq in H | apply Z.eqb_neq in H ].
  Ltac hc_lin Hc :=
    revert Hc; rewrite ?branch_taken_Z; cbv beta iota; linearize;
    cbn [edenot fop1_denot fop2_denot fop3_denot];
    lazymatch goal with HK : know_ok _ ?E _ _ |- _ => ev_simpl E end;
    rewrite ?uW, ?Z_to_bv_unsigned, ?bv_wrap64_mod; intros Hc;
    try (apply (f_equal negb) in Hc; rewrite negb_involutive in Hc; cbn [negb] in Hc);
    mods_in Hc; zbool Hc.

  Ltac regions_eq :=
    cbn [regions_denot map fst snd]; unfold adenot, v_addi; cbn [a_base a_off edenot];
    lazymatch goal with HK : know_ok _ ?E _ _ |- _ => ev_simpl E end; rewrite_getr;
    repeat (apply f_equal2; [apply f_equal2; [apply f_equal; lia | lia] | ]); reflexivity.

  (* [comment removed for export] *)
  Ltac frame_logs RS :=
    lazymatch goal with
    | |- frame_mod ?m0 ?m0 _ => apply frame_mod_refl
    | HK : know_ok _ ?E _ _ |- frame_mod ?m0 (mem_denot _ ?m1 ?log) _ =>
        apply (frame_mod_trans_same m0 m1);
        [ frame_logs RS
        | apply (frame_mod_mem_denot E m1 log RS);
          [ lazymatch goal with H : log_flat _ log |- _ => exact H end
          | repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; unfold flat, estart;
            cbn [a_base a_off edenot]; ev_simpl E; rewrite_getr; lia
          | vm_compute; reflexivity ] ]
    end.

  (* [comment removed for export] *)
  Ltac frame_now HADM RS rsZ Hfr :=
    subst_mems;
    lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ _ ?M0 =>
    lazymatch goal with HK : know_ok _ ?E ?M1 _ |- _ =>
      assert (Hfr : frame_mod M0 M1 rsZ);
      [ replace rsZ with (regions_denot E RS) by regions_eq; frame_logs RS | ]
    end end.

  (* [comment removed for export] *)
  Ltac adm_fr HADM Hfr HADM1 :=
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1, HF : fregs_ok _ ?sfr (@fp_regs ?I1), HF0 : id (fregs_ok _ ?sfr0 (@fp_regs ?I0))
      |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ ?R ?M0 =>
        assert (HADM1 : ADM I1 R1 M1);
        [ apply (adm_frameI I0 I1 R R1 M0 M1 _ HADM Hfr);
          [ solve [unfold BIG; solve_within]
          | solve [pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ? & _); solve_apart]
          | regv HR (2%bv:reg); reflexivity
          | regv HR (3%bv:reg); reflexivity
          | regv HR (4%bv:reg); reflexivity
          | regv HR (8%bv:reg); reflexivity
          | regv HR (18%bv:reg); reflexivity
          | exact (fregs_same_on E sfr0 sfr _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)) ]
        | ]
      end
    end.

  (* [comment removed for export] *)
  Ltac w_lt :=
    rewrite ?uW;
    lazymatch goal with
    | |- (bb ?b ?i < _)%Z => pose proof (bb_range b i); lia
    | |- _ => rewrite ?u_small by lia; lia
    end.

  (* [comment removed for export] *)
  Ltac flat_tac := unfold flat, estart; cbn [a_base a_off edenot];
    lazymatch goal with HK : know_ok _ ?E _ _ |- _ => ev_simpl E end; rewrite_getr; lia.
  Ltac kcellv b k n H :=
    lazymatch goal with HK : know_ok _ ?E ?M ?kn |- _ =>
      let r := eval vm_compute in (kread SEGS kn b k n) in
      lazymatch r with
      | Some ?v =>
        let KR := fresh "KR" in let Hfl := fresh "Hfl" in
        kread_rdn_fast SEGS E M kn b k n v HK H;
        lazymatch type of H with ?FL -> _ => assert (Hfl : FL) by flat_tac; specialize (H Hfl); clear Hfl end;
        unfold adenot, v_addi in H; cbn [a_base a_off edenot] in H; ev_simpl_in E H; rewrite_getr_in H;
        rewrite ?ext_val_zx_id4 in H by w_lt;
        rewrite ?ext_val_zx_id1 in H by w_lt
      | _ => fail "kcellv: no knowledge at" b k n
      end
    end.

  (* [comment removed for export] *)
  Ltac wle := lazymatch goal with |- (bv_unsigned (W ?b ?i) <= _)%Z => pose proof (bb_range b i); rewrite uW; lia end.

  (* [comment removed for export] *)
  Ltac pin_P n :=
    lazymatch goal with HR : regs_ok ?E _ _ |- _ =>
      pin_reg HR (13%bv:reg) (EVar 90) by
        (regv HR (13%bv:reg); cbn [edenot]; ev_simpl E; apply bv_eq;
         lazymatch goal with
         | |- bv_unsigned (mul_div M_MUL (Z_to_bv 64 3) ?bw) = _ =>
             rewrite (proj1 (uP0 bw ltac:(wle)))
         | |- bv_unsigned (mul_div M_MUL (mul_div M_MUL (Z_to_bv 64 3) ?bw) ?g0) = _ =>
             rewrite (proj1 (uP1 bw g0 ltac:(wle) ltac:(wle)))
         | |- bv_unsigned (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (Z_to_bv 64 3) ?bw) ?g0) ?g1) = _ =>
             rewrite (proj1 (uP2 bw g0 g1 ltac:(wle) ltac:(wle) ltac:(wle)))
         | |- bv_unsigned (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (Z_to_bv 64 3) ?bw) ?g0) ?g1) ?g2) = _ =>
             rewrite (proj1 (uP3 bw g0 g1 g2 ltac:(wle) ltac:(wle) ltac:(wle) ltac:(wle)))
         | |- bv_unsigned (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (Z_to_bv 64 3) ?bw) ?g0) ?g1) ?g2) ?g3) = _ =>
             rewrite (proj1 (uP4 bw g0 g1 g2 g3 ltac:(wle) ltac:(wle) ltac:(wle) ltac:(wle) ltac:(wle)))
         end;
         rewrite !uW;
         lazymatch goal with |- _ = bv_unsigned (Z_to_bv 64 (Pval ?b ?c ?k)) =>
           rewrite (u_small (Pval b c k)) by (pose proof (Pval_bnd b c k ltac:(cbn; lia)); lia) end;
         unfold Pval, gsl; cbn [firstn zprod]; lia)
    end.

  (* [comment removed for export] *)
  Ltac pin_slack :=
    lazymatch goal with HR : regs_ok ?E _ _ |- _ =>
      pin_reg HR (10%bv:reg) (EVar 87) by
        (regv HR (10%bv:reg); cbn [edenot]; ev_simpl E; apply slack_val; rewrite uW; lia)
    end.

  (* [comment removed for export] *)
  Ltac frame_g HADM Hfr := frame_now HADM [(SA (EVar 8) 128, 24%Z)] [(Z_to_bv 64 (a + 128), 24%Z)] Hfr.
  Ltac fail_g HADM :=
    let Hfr := fresh "Hfr" in let HADM1 := fresh "HADMf" in
    frame_g HADM Hfr; adm_fr HADM Hfr HADM1;
    match goal with H : adm _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => apply (failkI _ _ _ H) end.

  (* [comment removed for export] *)
  Definition kn_m3 (n : Z) : list kentry :=
    [KWord (SA (EVar 2) 0) 8 (EVar 81); KRange (EVar 81) 1 140737488355328;
     KRange (EVar 82) 1 140737488355328;
     KWord (SA (EVar 82) 0) 1 (EVar 83); KWord (SA (EVar 82) 1) 1 (EVar 84); KWord (SA (EVar 82) 2) 1 (EVar 85);
     KWord (SA (EVar 82) 3) 1 (EVar 86); KWord (SA (EVar 82) 16) 1 (EVar 87);
     KRange (EVar 83) 0 255; KRange (EVar 84) 0 255; KRange (EVar 85) 0 255; KRange (EVar 86) 0 255; KRange (EVar 87) 0 255;
     KRange (EVar 88) 20 4294967316; KRange (EVar 90) 0 3234611728125; KRange (EVar 91) 21 281474976710656;
     KDisj (SA (EVar 82) 0) 20 (SA (EVar 8) 0) 400;
     KWord (SA (EVar 8) 144) 4 (ELit n); KWord (SA (EVar 8) 300) 4 (ELit 3); KWord (SA (EVar 8) 296) 4 (EVar 89)].

  Definition vals_m3 (buf : word) (co mc : Z) (n : nat) : list word :=
    [eobw; Z_to_bv 64 (bv_unsigned buf + co); W buf co; W buf (co + 1); W buf (co + 2); W buf (co + 3); W buf (co + 16);
     Z_to_bv 64 (co + 20); Z_to_bv 64 mc; Z_to_bv 64 (Pval buf co n); Z_to_bv 64 (bv_unsigned buf + co + 20 + Pval buf co n)].

  Lemma kn_m3_ok : forall (FPI : FPState) R M sz buf ic mc co (n : nat),
    ADM FPI R M -> TAGC 0x6d414220 sz buf M -> mab_cells ic mc M ->
    (0 <= co < 4294967296)%Z -> (co + 20 <= sz)%Z -> ic = Z.of_nat n ->
    cell64 SEGS M (spv - 176 + 0) eobw ->
    know_ok SEGS (Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ base_valsI ++
                                  ([Z_to_bv 64 sz; buf] ++ vals_m3 buf co mc n))) (blobs_ev [bs])) M (kn_m3 (Z.of_nat n)).
  Proof.
    intros FPI R M sz buf ic mc co n HADM HTAG (C1 & C2 & C3 & Hic & Hmc) Hco Hco20 Hn S0. adm_facts HADM.
    pose proof HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c). pose proof (u64_range buf).
    pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P11 & _).
    pose proof (Pval_bnd buf co n ltac:(lia)) as HP.
    pose proof (bb_range buf co) as R0. pose proof (bb_range buf (co+1)) as R1. pose proof (bb_range buf (co+2)) as R2.
    pose proof (bb_range buf (co+3)) as R3. pose proof (bb_range buf (co+16)) as R16.
    set (E := Env _ _). unfold base_vals, vals_m3, W in E. unfold kn_m3.
    repeat apply Forall_cons; try apply Forall_nil.
    - eapply (kword_intro SEGS E _ (EVar 2) (getr R 2) 0 8 (EVar 81)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | rewrite U2; exact S0].
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia.
    - eapply (kword_intro SEGS E _ (EVar 82) (Z_to_bv 64 (bv_unsigned buf + co)) 0 1 (EVar 83)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia | rewrite u_small by lia; replace (bv_unsigned buf + co + 0)%Z with (bv_unsigned buf + co)%Z by lia; apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 82) (Z_to_bv 64 (bv_unsigned buf + co)) 1 1 (EVar 84)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia | rewrite u_small by lia; replace (bv_unsigned buf + co + 1)%Z with (bv_unsigned buf + (co + 1))%Z by lia; apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 82) (Z_to_bv 64 (bv_unsigned buf + co)) 2 1 (EVar 85)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia | rewrite u_small by lia; replace (bv_unsigned buf + co + 2)%Z with (bv_unsigned buf + (co + 2))%Z by lia; apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 82) (Z_to_bv 64 (bv_unsigned buf + co)) 3 1 (EVar 86)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia | rewrite u_small by lia; replace (bv_unsigned buf + co + 3)%Z with (bv_unsigned buf + (co + 3))%Z by lia; apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 82) (Z_to_bv 64 (bv_unsigned buf + co)) 16 1 (EVar 87)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia | rewrite u_small by lia; replace (bv_unsigned buf + co + 16)%Z with (bv_unsigned buf + (co + 16))%Z by lia; apply (data_byte data len bs); [exact AD|lia|lia]].
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia.
    - cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl E; rewrite A8; rewrite u_small by lia; lia.
    - eapply (kword_intro SEGS E _ (EVar 8) A 144 4 (ELit (Z.of_nat n)) (Z_to_bv 64 (Z.of_nat n))); [cbn [edenot]; ev_simpl E; exact A8 | reflexivity | lia | lia | lia | lia | rewrite <- Hn; exact (proj2 C1)].
    - eapply (kword_intro SEGS E _ (EVar 8) A 300 4 (ELit 3%Z) (Z_to_bv 64 3)); [cbn [edenot]; ev_simpl E; exact A8 | reflexivity | lia | lia | lia | lia | exact (proj2 C2)].
    - eapply (kword_intro SEGS E _ (EVar 8) A 296 4 (EVar 89) (Z_to_bv 64 mc)); [cbn [edenot]; ev_simpl E; exact A8 | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | exact (proj2 C3)].
  Qed.

  (* [comment removed for export] *)
  Ltac pkg_m3 HADM HTAG HMC Hco Hco20 Hn S0 n :=
    lazymatch type of HTAG with tagc _ _ _ ?ty ?sz ?buf _ =>
    lazymatch type of HMC with mab_cells ?ic ?mc _ =>
    lazymatch type of Hco with (0 <= ?co < _)%Z =>
      pkg HADM ([Z_to_bv 64 sz; buf] ++ vals_m3 buf co mc n) (kn_tag ty ++ kn_m3 (Z.of_nat n))
        ltac:(apply know_ok_app; [exact (kn_tag_okI _ _ _ ty sz buf _ HADM HTAG) | exact (kn_m3_ok _ _ _ sz buf ic mc co n HADM HTAG HMC Hco Hco20 Hn S0)]);
      lazymatch goal with HK : know_ok _ _ _ ?kn |- _ =>
        let kn' := eval vm_compute in kn in change kn with kn' in HK end;
      match goal with Edef := Env _ _ |- _ => cbv beta delta [vals_m3 app] in Edef end
    end end end.

  (* [comment removed for export] *)
  Definition be4 (buf : word) (i : Z) : Z :=
    (bb buf (i + 3) + 256 * bb buf (i + 2) + 65536 * bb buf (i + 1) + 16777216 * bb buf i)%Z.
  Lemma be4_range : forall buf i, (0 <= be4 buf i < 4294967296)%Z.
  Proof.
    intros buf i. unfold be4. pose proof (bb_range buf i). pose proof (bb_range buf (i+1)).
    pose proof (bb_range buf (i+2)). pose proof (bb_range buf (i+3)). lia.
  Qed.
  (* [comment removed for export] *)
  Definition le4w (buf : word) (i : Z) : word :=
    alu64 ALU_ADD (W buf i) (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 256) (W buf (i + 1)))
      (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 65536) (W buf (i + 2))) (mul_div M_MUL (Z_to_bv 64 16777216) (W buf (i + 3))))).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac m3_loop k HADM :=
    lazymatch k with
    | O => idtac
    | S ?k' =>
        (* [comment removed for export] *)
        run_fp 80%nat [0x1525c%Z; 0x1582c%Z] (dirs [false]) true by (mod2_split; lia);
        let H := fresh "Hg" in
        branch_case as H; [ fail_g HADM | hc_lin H; m3_loop k' HADM ]
    end.

  (* [comment removed for export] *)
  Ltac m3_success n HADM HTAG HMC HC10 Hco Hn :=
    lazymatch goal with Heob : branch_taken _ _ _ = true |- _ =>
    lazymatch type of HTAG with tagc _ _ _ _ ?sz ?buf _ =>
    lazymatch type of Hco with (0 <= ?co < _)%Z =>
    lazymatch type of HMC with mab_cells ?ic ?mc _ =>
      pose proof (zprod_bnd _ (gsl_bnd buf co n)) as HZb;
      hc_lin Heob;
      let Hfr := fresh "Hfr" in let HADMs := fresh "HADMs" in
      frame_g HADM Hfr; adm_fr HADM Hfr HADMs;
      lazymatch goal with |- runs_to _ (@mkst _ _ _ ?M1 _) _ => remember M1 as Mz eqn:HMz; clear HMz end;
      eapply (in0I _ _ _ ic mc); [exact HADMs | ];
      let C144 := fresh "C144" in let C300 := fresh "C300" in let C296 := fresh "C296" in
      let C128 := fresh "C128" in let C136 := fresh "C136" in
      kcellv (EVar 8) 144%Z 4%nat C144; kcellv (EVar 8) 300%Z 4%nat C300; kcellv (EVar 8) 296%Z 4%nat C296;
      kcellv (EVar 8) 128%Z 8%nat C128; kcellv (EVar 8) 136%Z 8%nat C136;
      split; [split; [lia | rewrite Hn; exact C144]|];
      split; [split; [lia | exact C296]|];
      split; [split; [lia | exact C300]|];
      split; [lia|]; split; [assumption|];
      split; [eapply curves10_frame1; [exact HC10 | exact Hfr | intros o Ho; pose proof (offsets_bound o Ho);
              rewrite u_small_frame by lia; lia]|];
      lazymatch type of C128 with _ = Some (word_to_le_bytes 8 ?g8) =>
      lazymatch type of C136 with _ = Some (word_to_le_bytes 8 ?g16) =>
        exists ic, 3%Z, (gsl buf co n), g8, g16 end end;
      split; [split; [lia | rewrite Hn; exact C144]|];
      split; [split; [lia | exact C300]|];
      split; [lia|];
      split; [rewrite Hn; unfold gsl; rewrite length_firstn; cbn; lia|];
      split; [unfold gsl; cbn [firstn]; repeat apply Forall_cons; try apply Forall_nil;
              match goal with |- (2 <= bb ?b ?i <= 255)%Z => pose proof (bb_range b i); lia end|];
      split; [intros i Hi; rewrite Hn in Hi; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi;
              first [ exfalso; lia
                    | let Hi' := fresh in
                      assert (Hi' : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3)%Z) by lia;
                      let G := fresh "G" in
                      destruct Hi' as [-> |[-> |[-> | ->]]];
                      [ kcellv (EVar 8) 148%Z 1%nat G; replace (a + 148 + 0)%Z with (a + 148)%Z by lia
                      | first [ exfalso; lia | kcellv (EVar 8) 149%Z 1%nat G; replace (a + 148 + 1)%Z with (a + 149)%Z by lia ]
                      | first [ exfalso; lia | kcellv (EVar 8) 150%Z 1%nat G; replace (a + 148 + 2)%Z with (a + 150)%Z by lia ]
                      | first [ exfalso; lia | kcellv (EVar 8) 151%Z 1%nat G; replace (a + 148 + 3)%Z with (a + 151)%Z by lia ] ];
                      unfold gsl; cbn [firstn]; unfold Z.to_nat, Pos.to_nat; cbn [Pos.iter_op Nat.add nth];
                      (split; [ match goal with |- (0 <= bb ?b ?i' < 256)%Z => apply bb_range end
                              | unfold W in G; exact G ]) ]|];
      split; [exact C128|]; split; [exact C136|]; split; [reflexivity|];
      intros _; unfold inDATA; unfold Pval in Heob;
      split; intros Hnz;
        first [ exfalso; apply Hnz; rewrite u_lit64a; reflexivity
              | rewrite ?u_add64, ?u_lit64a; mods_goal; lia ]
    end end end end.

  (* [comment removed for export] *)
  Ltac m3_rest n HADM HTAG HMC HC10 Hco Hn :=
    lazymatch type of HTAG with tagc _ _ _ _ ?sz ?buf _ =>
    lazymatch type of Hco with (0 <= ?co < _)%Z =>
    pose proof (Pval_bnd buf co n ltac:(cbn; lia)) as HPb;
    m3_loop n HADM;
    run_fp 80%nat [0x1525c%Z; 0x1582c%Z] noscr true;
    (* [comment removed for export] *)
    lazymatch n with
    | 4%nat => let H := fresh "Hmx" in branch_case as H; [ fail_g HADM | run_fp 20%nat [0x1525c%Z; 0x1582c%Z] noscr true ]
    | _ => idtac
    end;
    pin_P n;
    run_fp 80%nat [0x1525c%Z; 0x15858%Z] noscr true;
    let Hs := fresh "Hszc" in
    branch_case as Hs; [ fail_g HADM |];
    run_fp 80%nat [0x1525c%Z; 0x15858%Z] noscr true;
    pin_slack;
    (* [comment removed for export] *)
    run_fp 10%nat [0x15860%Z] noscr true;
    lazymatch goal with HR : regs_ok ?E _ _ |- _ =>
      pin_reg HR (11%bv:reg) (EVar 91) by (regv_lin HR (11%bv:reg); cbn [edenot]; ev_simpl E; rewrite !u_small by lia; f_equal; lia) end;
    run_fp 5%nat [0x15868%Z] (dirs [false]) true;
    lazymatch goal with HR : regs_ok ?E _ _ |- _ =>
      pin_reg HR (12%bv:reg) (ELit 1%Z) by (regv HR (12%bv:reg); cbn [edenot]; ev_simpl E; apply sltu_0_pos; lia) end;
    run_fp 3%nat [0x1586c%Z] noscr true;
    lazymatch goal with HR : regs_ok ?E _ _ |- _ =>
      pin_reg HR (13%bv:reg) (ELit 0%Z) by (regv HR (13%bv:reg); cbn [edenot]; ev_simpl E; apply sltiu_ge1; rewrite u_small by lia; lia) end;
    run_fp 5%nat [0x15878%Z] noscr true;
    run_fp 3%nat [0x15880%Z] (dirs [false]) true;
    lazymatch goal with HR : regs_ok ?E _ _ |- _ =>
      pin_reg HR (11%bv:reg) (ELit 0%Z) by (regv HR (11%bv:reg); cbn [edenot]; ev_simpl E; apply sltiu_ge1;
        rewrite u_add64, uW, u_small by lia; pose proof (bb_range buf (co + 16)); rewrite Z.mod_small by lia; lia) end;
    run_fp 10%nat [0x1525c%Z; 0x15154%Z] noscr true;
    let Heob := fresh "Heob" in
    branch_case as Heob; [ m3_success n HADM HTAG HMC HC10 Hco Hn | run_fp 10%nat [0x1525c%Z] noscr true; fail_g HADM ]
    end end.

  (* [comment removed for export] *)

  Definition m3b_stmt (n : nat) : Prop := forall (FPI : FPState) R M sz buf ic mc co,
    ADM FPI R M -> TAGC 0x6d414220 sz buf M -> mab_cells ic mc M -> curves10 M ->
    (0 <= co < 4294967296)%Z -> (co + 20 <= sz)%Z -> ic = Z.of_nat n ->
    getr R 10 = Z_to_bv 64 (bv_unsigned buf + co) -> getr R 11 = Z_to_bv 64 (co + 20) -> getr R 12 = Z_to_bv 64 sz ->
    getr R 13 = buf ->
    cell64 SEGS M (spv - 176 + 0) eobw ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x15768) M rom) QP.

  Ltac m3b_intro :=
    intros FPI R M sz buf ic mc co HADM HTAG HMC HC10 Hco Hco20 Hn H10 H11 H12 H13 S0;
    adm_facts HADM; pose proof HMC as (C1 & C2 & C3 & Hic & Hmc);
    pose proof HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c); pose proof (u64_range buf);
    pose proof (bb_range buf (co+16)) as R16.

  Lemma m3b0 : m3b_stmt 0.
  Proof.
    unfold m3b_stmt. m3b_intro.
    pkg_m3 HADM HTAG HMC Hco Hco20 Hn S0 0%nat.
    pin_reg HR (10%bv:reg) (EVar 82) by (cbn [edenot]; ev_simpl E; exact H10).
    pin_reg HR (11%bv:reg) (EVar 88) by (cbn [edenot]; ev_simpl E; exact H11).
    pin_reg HR (12%bv:reg) (EVar 79) by (cbn [edenot]; ev_simpl E; exact H12).
    pin_reg HR (13%bv:reg) (EVar 80) by (cbn [edenot]; ev_simpl E; exact H13).
    run_fp 80%nat [0x1525c%Z; 0x1582c%Z] (dirs [false]) true.
    branch_case as Hbw2.
    - hc_lin Hbw2. m3_rest 0%nat HADM HTAG HMC HC10 Hco Hn.
    - hc_lin Hbw2.
      run_fp 80%nat [0x1525c%Z; 0x1582c%Z] noscr true.
      branch_case as Hbw1; [ fail_g HADM |].
      hc_lin Hbw1. m3_rest 0%nat HADM HTAG HMC HC10 Hco Hn.
  Qed.

  Lemma m3b1 : m3b_stmt 1.
  Proof.
    unfold m3b_stmt. m3b_intro.
    pkg_m3 HADM HTAG HMC Hco Hco20 Hn S0 1%nat.
    pin_reg HR (10%bv:reg) (EVar 82) by (cbn [edenot]; ev_simpl E; exact H10).
    pin_reg HR (11%bv:reg) (EVar 88) by (cbn [edenot]; ev_simpl E; exact H11).
    pin_reg HR (12%bv:reg) (EVar 79) by (cbn [edenot]; ev_simpl E; exact H12).
    pin_reg HR (13%bv:reg) (EVar 80) by (cbn [edenot]; ev_simpl E; exact H13).
    run_fp 80%nat [0x1525c%Z; 0x1582c%Z] (dirs [false]) true.
    branch_case as Hbw2.
    - hc_lin Hbw2. m3_rest 1%nat HADM HTAG HMC HC10 Hco Hn.
    - hc_lin Hbw2.
      run_fp 80%nat [0x1525c%Z; 0x1582c%Z] noscr true.
      branch_case as Hbw1; [ fail_g HADM |].
      hc_lin Hbw1. m3_rest 1%nat HADM HTAG HMC HC10 Hco Hn.
  Qed.

  Lemma m3b2 : m3b_stmt 2.
  Proof.
    unfold m3b_stmt. m3b_intro.
    pkg_m3 HADM HTAG HMC Hco Hco20 Hn S0 2%nat.
    pin_reg HR (10%bv:reg) (EVar 82) by (cbn [edenot]; ev_simpl E; exact H10).
    pin_reg HR (11%bv:reg) (EVar 88) by (cbn [edenot]; ev_simpl E; exact H11).
    pin_reg HR (12%bv:reg) (EVar 79) by (cbn [edenot]; ev_simpl E; exact H12).
    pin_reg HR (13%bv:reg) (EVar 80) by (cbn [edenot]; ev_simpl E; exact H13).
    run_fp 80%nat [0x1525c%Z; 0x1582c%Z] (dirs [false]) true.
    branch_case as Hbw2.
    - hc_lin Hbw2. m3_rest 2%nat HADM HTAG HMC HC10 Hco Hn.
    - hc_lin Hbw2.
      run_fp 80%nat [0x1525c%Z; 0x1582c%Z] noscr true.
      branch_case as Hbw1; [ fail_g HADM |].
      hc_lin Hbw1. m3_rest 2%nat HADM HTAG HMC HC10 Hco Hn.
  Qed.

End RC.
End LibReadA2BUbc.

Module LibReadA2BUbd.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Lib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibRodata OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibBswap.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfKc.
Import LibReadA2BUba LibReadA2BUbb LibReadA2BUbc.
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
#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section RD.
  Variables (FPI0 : FPState) (regs0 : bvmap 5 word) (mem0 rom : word -> option byte) (ret : word).
  Variables (data : word) (len : Z) (bs : list byte) (sp T A : word) (pcs : Z).
  Hypothesis Hra : getr regs0 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HPRE : a2b_pre SEGS wp2_infoub data len bs sp T A pcs FPI0 regs0 mem0.
  Hypothesis Hcanon : canonicalize_contract SEGS wp3_infoub.

  #[local] Abbreviation a := (bv_unsigned A).
  #[local] Abbreviation spv := (bv_unsigned sp).
  #[local] Abbreviation t := (bv_unsigned T).
  #[local] Abbreviation ADM := (adm FPI0 regs0 mem0 ret data len bs sp T A).
  #[local] Abbreviation QP := (Qpost FPI0 regs0 mem0 rom ret data len bs sp T A pcs).
  #[local] Abbreviation CI := (chain_inv data len A).
  #[local] Abbreviation TAGC := (tagc data len T).
  #[local] Abbreviation pre_factsI := (pre_facts FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation pre_tagI := (pre_tag FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation pre_spI := (pre_sp FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation kn_adm_okI := (kn_adm_ok FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation kn_tag_okI := (kn_tag_ok FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation adm_frameI := (adm_frame FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation base_valsI := (base_vals regs0 ret data len).
  #[local] Abbreviation failkI := (failk FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE).
  #[local] Abbreviation in0I := (in0 FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).
  #[local] Abbreviation eobw := (Z_to_bv 64 (bv_unsigned data + len)).
  #[local] Abbreviation bbI := (bb data bs).
  #[local] Abbreviation WI := (W data bs).
  #[local] Abbreviation curves10I := (curves10 data len A).
  #[local] Abbreviation mab_cellsI := (mab_cells A).
  #[local] Abbreviation gslI := (gsl data bs).
  #[local] Abbreviation PvalI := (Pval data bs).
  #[local] Abbreviation be4I := (be4 data bs).
  #[local] Abbreviation le4wI := (le4w data bs).
  #[local] Abbreviation vals_m3I := (vals_m3 data len bs).
  #[local] Abbreviation curves10_frame1I := (curves10_frame1 FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation kn_m3_okI := (kn_m3_ok FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation m3b_stmtI := (m3b_stmt FPI0 regs0 mem0 rom ret data len bs sp T A pcs).
  #[local] Abbreviation m3b0I := (m3b0 FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).
  #[local] Abbreviation m3b1I := (m3b1 FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).
  #[local] Abbreviation m3b2I := (m3b2 FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).

  (* [comment removed for export] *)
  Ltac adm_facts HADM :=
    pose proof HADM as (A2 & A3 & A4 & A8 & A18 & AF & AS & AFR & AD & ARO & AWA & AWS);
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _);
    assert (U2 : bv_unsigned (getr _ 2) = (spv - 176)%Z) by (rewrite A2, u_small by lia; lia).

  Ltac pkg HADM extra kx ktac :=
    lazymatch goal with
    | |- runs_to _ (@mkst ?FPI ?R _ ?M _) _ =>
      set (E := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++
         [ret; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20; getr regs0 21;
          getr regs0 22; getr regs0 23; getr regs0 24; getr regs0 25; getr regs0 26; getr regs0 27;
          data; Z_to_bv 64 len] ++ extra)) (blobs_ev [bs]));
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs]));
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs]));
      pose proof (HR : id _) as HR0; pose proof (HF : id _) as HF0;
      let HK1 := fresh "HK1" in let HK2 := fresh "HK2" in
      pose proof (kn_adm_okI FPI R M extra HADM) as HK1; change (know_ok SEGS E M kn_adm) in HK1;
      assert (HK2 : know_ok SEGS E M kx); [ktac|];
      pose proof (know_ok_app SEGS E M kn_adm kx HK1 HK2) as HK; clear HK1 HK2;
      cbv beta delta [kn_adm app] in HK
    end.

  Ltac pkg_tag HADM HTAG rest kx ktac :=
    lazymatch type of HTAG with tagc _ _ _ ?ty ?sz ?buf _ =>
      pkg HADM ([Z_to_bv 64 sz; buf] ++ rest) (kn_tag ty ++ kx)
        ltac:(apply know_ok_app; [exact (kn_tag_okI _ _ _ ty sz buf rest HADM HTAG) | ktac])
    end.

  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.

  Ltac subst_mems :=
    repeat match goal with H : @eq (word -> option byte) ?x _ |- _ => is_var x; subst x end.

  Ltac adm_now HADM HADM1 :=
    subst_mems;
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1, HF : fregs_ok _ ?sfr (@fp_regs ?I1), HF0 : id (fregs_ok _ ?sfr0 (@fp_regs ?I0))
      |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ ?R ?M0 =>
        assert (HADM1 : ADM I1 R1 M1);
        [ apply (adm_frameI I0 I1 R R1 M0 M1 [] HADM);
          [ apply frame_mod_refl
          | apply Forall_nil
          | apply Forall_nil
          | regv HR (2%bv:reg); reflexivity
          | regv HR (3%bv:reg); reflexivity
          | regv HR (4%bv:reg); reflexivity
          | regv HR (8%bv:reg); reflexivity
          | regv HR (18%bv:reg); reflexivity
          | exact (fregs_same_on E sfr0 sfr _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)) ]
        | ]
      end
    end.
  (* [comment removed for export] *)


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac mods_in H :=
    repeat match type of H with context [ (?x mod ?m)%Z ] =>
      lazymatch x with context [ (_ mod _)%Z ] => fail | _ => rewrite (Z.mod_small x m) in H by lia end end.
  Ltac mods_goal :=
    repeat match goal with |- context [ (?x mod ?m)%Z ] =>
      lazymatch x with context [ (_ mod _)%Z ] => fail | _ => rewrite (Z.mod_small x m) by lia end end.

  (* [comment removed for export] *)
  Ltac zbool H :=
    first [ apply Z.ltb_lt in H | apply Z.ltb_ge in H | apply Z.eqb_eq in H | apply Z.eqb_neq in H ].
  Ltac hc_lin Hc :=
    revert Hc; rewrite ?branch_taken_Z; cbv beta iota; linearize;
    cbn [edenot fop1_denot fop2_denot fop3_denot];
    lazymatch goal with HK : know_ok _ ?E _ _ |- _ => ev_simpl E end;
    rewrite ?uW, ?Z_to_bv_unsigned, ?bv_wrap64_mod; intros Hc;
    try (apply (f_equal negb) in Hc; rewrite negb_involutive in Hc; cbn [negb] in Hc);
    mods_in Hc; zbool Hc.

  Ltac regions_eq :=
    cbn [regions_denot map fst snd]; unfold adenot, v_addi; cbn [a_base a_off edenot];
    lazymatch goal with HK : know_ok _ ?E _ _ |- _ => ev_simpl E end; rewrite_getr;
    repeat (apply f_equal2; [apply f_equal2; [apply f_equal; lia | lia] | ]); reflexivity.

  (* [comment removed for export] *)
  Ltac frame_logs RS :=
    lazymatch goal with
    | |- frame_mod ?m0 ?m0 _ => apply frame_mod_refl
    | HK : know_ok _ ?E _ _ |- frame_mod ?m0 (mem_denot _ ?m1 ?log) _ =>
        apply (frame_mod_trans_same m0 m1);
        [ frame_logs RS
        | apply (frame_mod_mem_denot E m1 log RS);
          [ lazymatch goal with H : log_flat _ log |- _ => exact H end
          | repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; unfold flat, estart;
            cbn [a_base a_off edenot]; ev_simpl E; rewrite_getr; lia
          | vm_compute; reflexivity ] ]
    end.

  (* [comment removed for export] *)
  Ltac frame_now HADM RS rsZ Hfr :=
    subst_mems;
    lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ _ ?M0 =>
    lazymatch goal with HK : know_ok _ ?E ?M1 _ |- _ =>
      assert (Hfr : frame_mod M0 M1 rsZ);
      [ replace rsZ with (regions_denot E RS) by regions_eq; frame_logs RS | ]
    end end.

  (* [comment removed for export] *)
  Ltac adm_fr HADM Hfr HADM1 :=
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1, HF : fregs_ok _ ?sfr (@fp_regs ?I1), HF0 : id (fregs_ok _ ?sfr0 (@fp_regs ?I0))
      |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ ?R ?M0 =>
        assert (HADM1 : ADM I1 R1 M1);
        [ apply (adm_frameI I0 I1 R R1 M0 M1 _ HADM Hfr);
          [ solve [unfold BIG; solve_within]
          | solve [pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ? & _); solve_apart]
          | regv HR (2%bv:reg); reflexivity
          | regv HR (3%bv:reg); reflexivity
          | regv HR (4%bv:reg); reflexivity
          | regv HR (8%bv:reg); reflexivity
          | regv HR (18%bv:reg); reflexivity
          | exact (fregs_same_on E sfr0 sfr _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)) ]
        | ]
      end
    end.

  (* [comment removed for export] *)
  Ltac w_lt :=
    rewrite ?uW;
    lazymatch goal with
    | |- (bb _ _ ?b ?i < _)%Z => pose proof (bb_range data bs b i); lia
    | |- _ => rewrite ?u_small by lia; lia
    end.

  (* [comment removed for export] *)
  Ltac flat_tac := unfold flat, estart; cbn [a_base a_off edenot];
    lazymatch goal with HK : know_ok _ ?E _ _ |- _ => ev_simpl E end; rewrite_getr; lia.
  Ltac kcellv b k n H :=
    lazymatch goal with HK : know_ok _ ?E ?M ?kn |- _ =>
      let r := eval vm_compute in (kread SEGS kn b k n) in
      lazymatch r with
      | Some ?v =>
        let KR := fresh "KR" in let Hfl := fresh "Hfl" in
        kread_rdn_fast SEGS E M kn b k n v HK H;
        lazymatch type of H with ?FL -> _ => assert (Hfl : FL) by flat_tac; specialize (H Hfl); clear Hfl end;
        unfold adenot, v_addi in H; cbn [a_base a_off edenot] in H; ev_simpl_in E H; rewrite_getr_in H;
        rewrite ?ext_val_zx_id4 in H by w_lt;
        rewrite ?ext_val_zx_id1 in H by w_lt
      | _ => fail "kcellv: no knowledge at" b k n
      end
    end.

  (* [comment removed for export] *)
  Ltac wle := lazymatch goal with |- (bv_unsigned (W _ _ ?b ?i) <= _)%Z => pose proof (bb_range data bs b i); rewrite uW; lia end.

  (* [comment removed for export] *)
  Ltac pin_P n :=
    lazymatch goal with HR : regs_ok ?E _ _ |- _ =>
      pin_reg HR (13%bv:reg) (EVar 90) by
        (regv HR (13%bv:reg); cbn [edenot]; ev_simpl E; apply bv_eq;
         lazymatch goal with
         | |- bv_unsigned (mul_div M_MUL (Z_to_bv 64 3) ?bw) = _ =>
             rewrite (proj1 (uP0 bw ltac:(wle)))
         | |- bv_unsigned (mul_div M_MUL (mul_div M_MUL (Z_to_bv 64 3) ?bw) ?g0) = _ =>
             rewrite (proj1 (uP1 bw g0 ltac:(wle) ltac:(wle)))
         | |- bv_unsigned (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (Z_to_bv 64 3) ?bw) ?g0) ?g1) = _ =>
             rewrite (proj1 (uP2 bw g0 g1 ltac:(wle) ltac:(wle) ltac:(wle)))
         | |- bv_unsigned (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (Z_to_bv 64 3) ?bw) ?g0) ?g1) ?g2) = _ =>
             rewrite (proj1 (uP3 bw g0 g1 g2 ltac:(wle) ltac:(wle) ltac:(wle) ltac:(wle)))
         | |- bv_unsigned (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (mul_div M_MUL (Z_to_bv 64 3) ?bw) ?g0) ?g1) ?g2) ?g3) = _ =>
             rewrite (proj1 (uP4 bw g0 g1 g2 g3 ltac:(wle) ltac:(wle) ltac:(wle) ltac:(wle) ltac:(wle)))
         end;
         rewrite !uW;
         lazymatch goal with |- _ = bv_unsigned (Z_to_bv 64 (Pval _ _ ?b ?c ?k)) =>
           rewrite (u_small (PvalI b c k)) by (pose proof (Pval_bnd data bs b c k ltac:(cbn; lia)); lia) end;
         unfold Pval, gsl; cbn [firstn zprod]; lia)
    end.

  (* [comment removed for export] *)
  Ltac pin_slack :=
    lazymatch goal with HR : regs_ok ?E _ _ |- _ =>
      pin_reg HR (10%bv:reg) (EVar 87) by
        (regv HR (10%bv:reg); cbn [edenot]; ev_simpl E; apply slack_val; rewrite uW; lia)
    end.

  (* [comment removed for export] *)
  Ltac frame_g HADM Hfr := frame_now HADM [(SA (EVar 8) 128, 24%Z)] [(Z_to_bv 64 (a + 128), 24%Z)] Hfr.
  Ltac fail_g HADM :=
    let Hfr := fresh "Hfr" in let HADM1 := fresh "HADMf" in
    frame_g HADM Hfr; adm_fr HADM Hfr HADM1;
    match goal with H : adm _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => apply (failkI _ _ _ H) end.

  (* [comment removed for export] *)
  Ltac pkg_m3 HADM HTAG HMC Hco Hco20 Hn S0 n :=
    lazymatch type of HTAG with tagc _ _ _ ?ty ?sz ?buf _ =>
    lazymatch type of HMC with mab_cells _ ?ic ?mc _ =>
    lazymatch type of Hco with (0 <= ?co < _)%Z =>
      pkg HADM ([Z_to_bv 64 sz; buf] ++ vals_m3I buf co mc n) (kn_tag ty ++ kn_m3 (Z.of_nat n))
        ltac:(apply know_ok_app; [exact (kn_tag_okI _ _ _ ty sz buf _ HADM HTAG) | exact (kn_m3_okI _ _ _ sz buf ic mc co n HADM HTAG HMC Hco Hco20 Hn S0)]);
      lazymatch goal with HK : know_ok _ _ _ ?kn |- _ =>
        let kn' := eval vm_compute in kn in change kn with kn' in HK end;
      match goal with Edef := Env _ _ |- _ => cbv beta delta [vals_m3 app] in Edef end
    end end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac m3_loop k HADM :=
    lazymatch k with
    | O => idtac
    | S ?k' =>
        (* [comment removed for export] *)
        run_fp 80%nat [0x1525c%Z; 0x1582c%Z] (dirs [false]) true by (mod2_split; lia);
        let H := fresh "Hg" in
        branch_case as H; [ fail_g HADM | hc_lin H; m3_loop k' HADM ]
    end.

  (* [comment removed for export] *)
  Ltac m3_success n HADM HTAG HMC HC10 Hco Hn :=
    lazymatch goal with Heob : branch_taken _ _ _ = true |- _ =>
    lazymatch type of HTAG with tagc _ _ _ _ ?sz ?buf _ =>
    lazymatch type of Hco with (0 <= ?co < _)%Z =>
    lazymatch type of HMC with mab_cells _ ?ic ?mc _ =>
      pose proof (zprod_bnd _ (gsl_bnd data bs buf co n)) as HZb;
      hc_lin Heob;
      let Hfr := fresh "Hfr" in let HADMs := fresh "HADMs" in
      frame_g HADM Hfr; adm_fr HADM Hfr HADMs;
      lazymatch goal with |- runs_to _ (@mkst _ _ _ ?M1 _) _ => remember M1 as Mz eqn:HMz; clear HMz end;
      eapply (in0I _ _ _ ic mc); [exact HADMs | ];
      let C144 := fresh "C144" in let C300 := fresh "C300" in let C296 := fresh "C296" in
      let C128 := fresh "C128" in let C136 := fresh "C136" in
      kcellv (EVar 8) 144%Z 4%nat C144; kcellv (EVar 8) 300%Z 4%nat C300; kcellv (EVar 8) 296%Z 4%nat C296;
      kcellv (EVar 8) 128%Z 8%nat C128; kcellv (EVar 8) 136%Z 8%nat C136;
      split; [split; [lia | rewrite Hn; exact C144]|];
      split; [split; [lia | exact C296]|];
      split; [split; [lia | exact C300]|];
      split; [lia|]; split; [assumption|];
      split; [eapply curves10_frame1I; [exact HC10 | exact Hfr | intros o Ho; pose proof (offsets_bound o Ho);
              rewrite u_small_frame by lia; lia]|];
      lazymatch type of C128 with _ = Some (word_to_le_bytes 8 ?g8) =>
      lazymatch type of C136 with _ = Some (word_to_le_bytes 8 ?g16) =>
        exists ic, 3%Z, (gslI buf co n), g8, g16 end end;
      split; [split; [lia | rewrite Hn; exact C144]|];
      split; [split; [lia | exact C300]|];
      split; [lia|];
      split; [rewrite Hn; unfold gsl; rewrite length_firstn; cbn; lia|];
      split; [unfold gsl; cbn [firstn]; repeat apply Forall_cons; try apply Forall_nil;
              match goal with |- (2 <= bb _ _ ?b ?i <= 255)%Z => pose proof (bb_range data bs b i); lia end|];
      split; [intros i Hi; rewrite Hn in Hi; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi;
              first [ exfalso; lia
                    | let Hi' := fresh in
                      assert (Hi' : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3)%Z) by lia;
                      let G := fresh "G" in
                      destruct Hi' as [-> |[-> |[-> | ->]]];
                      [ kcellv (EVar 8) 148%Z 1%nat G; replace (a + 148 + 0)%Z with (a + 148)%Z by lia
                      | first [ exfalso; lia | kcellv (EVar 8) 149%Z 1%nat G; replace (a + 148 + 1)%Z with (a + 149)%Z by lia ]
                      | first [ exfalso; lia | kcellv (EVar 8) 150%Z 1%nat G; replace (a + 148 + 2)%Z with (a + 150)%Z by lia ]
                      | first [ exfalso; lia | kcellv (EVar 8) 151%Z 1%nat G; replace (a + 148 + 3)%Z with (a + 151)%Z by lia ] ];
                      unfold gsl; cbn [firstn]; unfold Z.to_nat, Pos.to_nat; cbn [Pos.iter_op Nat.add nth];
                      (split; [ match goal with |- (0 <= bb _ _ ?b ?i' < 256)%Z => apply bb_range end
                              | unfold W in G; exact G ]) ]|];
      split; [exact C128|]; split; [exact C136|]; split; [reflexivity|];
      intros _; unfold inDATA; unfold Pval in Heob;
      split; intros Hnz;
        first [ exfalso; apply Hnz; rewrite u_lit64a; reflexivity
              | rewrite ?u_add64, ?u_lit64a; mods_goal; lia ]
    end end end end.

  (* [comment removed for export] *)
  Ltac m3_rest n HADM HTAG HMC HC10 Hco Hn :=
    lazymatch type of HTAG with tagc _ _ _ _ ?sz ?buf _ =>
    lazymatch type of Hco with (0 <= ?co < _)%Z =>
    pose proof (Pval_bnd data bs buf co n ltac:(cbn; lia)) as HPb;
    m3_loop n HADM;
    run_fp 80%nat [0x1525c%Z; 0x1582c%Z] noscr true;
    (* [comment removed for export] *)
    lazymatch n with
    | 4%nat => let H := fresh "Hmx" in branch_case as H; [ fail_g HADM | run_fp 20%nat [0x1525c%Z; 0x1582c%Z] noscr true ]
    | _ => idtac
    end;
    pin_P n;
    run_fp 80%nat [0x1525c%Z; 0x15858%Z] noscr true;
    let Hs := fresh "Hszc" in
    branch_case as Hs; [ fail_g HADM |];
    run_fp 80%nat [0x1525c%Z; 0x15858%Z] noscr true;
    pin_slack;
    (* [comment removed for export] *)
    run_fp 10%nat [0x15860%Z] noscr true;
    lazymatch goal with HR : regs_ok ?E _ _ |- _ =>
      pin_reg HR (11%bv:reg) (EVar 91) by (regv_lin HR (11%bv:reg); cbn [edenot]; ev_simpl E; rewrite !u_small by lia; f_equal; lia) end;
    run_fp 5%nat [0x15868%Z] (dirs [false]) true;
    lazymatch goal with HR : regs_ok ?E _ _ |- _ =>
      pin_reg HR (12%bv:reg) (ELit 1%Z) by (regv HR (12%bv:reg); cbn [edenot]; ev_simpl E; apply sltu_0_pos; lia) end;
    run_fp 3%nat [0x1586c%Z] noscr true;
    lazymatch goal with HR : regs_ok ?E _ _ |- _ =>
      pin_reg HR (13%bv:reg) (ELit 0%Z) by (regv HR (13%bv:reg); cbn [edenot]; ev_simpl E; apply sltiu_ge1; rewrite u_small by lia; lia) end;
    run_fp 5%nat [0x15878%Z] noscr true;
    run_fp 3%nat [0x15880%Z] (dirs [false]) true;
    lazymatch goal with HR : regs_ok ?E _ _ |- _ =>
      pin_reg HR (11%bv:reg) (ELit 0%Z) by (regv HR (11%bv:reg); cbn [edenot]; ev_simpl E; apply sltiu_ge1;
        rewrite u_add64, uW, u_small by lia; pose proof (bb_range data bs buf (co + 16)); rewrite Z.mod_small by lia; lia) end;
    run_fp 10%nat [0x1525c%Z; 0x15154%Z] noscr true;
    let Heob := fresh "Heob" in
    branch_case as Heob; [ m3_success n HADM HTAG HMC HC10 Hco Hn | run_fp 10%nat [0x1525c%Z] noscr true; fail_g HADM ]
    end end.

  (* [comment removed for export] *)

  Ltac m3b_intro :=
    intros FPI R M sz buf ic mc co HADM HTAG HMC HC10 Hco Hco20 Hn H10 H11 H12 H13 S0;
    adm_facts HADM; pose proof HMC as (C1 & C2 & C3 & Hic & Hmc);
    pose proof HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c); pose proof (u64_range buf);
    pose proof (bb_range data bs buf (co+16)) as R16.


  Lemma m3b3 : m3b_stmtI 3.
  Proof.
    unfold m3b_stmt. m3b_intro.
    pkg_m3 HADM HTAG HMC Hco Hco20 Hn S0 3%nat.
    pin_reg HR (10%bv:reg) (EVar 82) by (cbn [edenot]; ev_simpl E; exact H10).
    pin_reg HR (11%bv:reg) (EVar 88) by (cbn [edenot]; ev_simpl E; exact H11).
    pin_reg HR (12%bv:reg) (EVar 79) by (cbn [edenot]; ev_simpl E; exact H12).
    pin_reg HR (13%bv:reg) (EVar 80) by (cbn [edenot]; ev_simpl E; exact H13).
    run_fp 80%nat [0x1525c%Z; 0x1582c%Z] (dirs [false]) true.
    branch_case as Hbw2.
    - hc_lin Hbw2. m3_rest 3%nat HADM HTAG HMC HC10 Hco Hn.
    - hc_lin Hbw2.
      run_fp 80%nat [0x1525c%Z; 0x1582c%Z] noscr true.
      branch_case as Hbw1; [ fail_g HADM |].
      hc_lin Hbw1. m3_rest 3%nat HADM HTAG HMC HC10 Hco Hn.
  Qed.

  Lemma m3b4 : m3b_stmtI 4.
  Proof.
    unfold m3b_stmt. m3b_intro.
    pkg_m3 HADM HTAG HMC Hco Hco20 Hn S0 4%nat.
    pin_reg HR (10%bv:reg) (EVar 82) by (cbn [edenot]; ev_simpl E; exact H10).
    pin_reg HR (11%bv:reg) (EVar 88) by (cbn [edenot]; ev_simpl E; exact H11).
    pin_reg HR (12%bv:reg) (EVar 79) by (cbn [edenot]; ev_simpl E; exact H12).
    pin_reg HR (13%bv:reg) (EVar 80) by (cbn [edenot]; ev_simpl E; exact H13).
    run_fp 80%nat [0x1525c%Z; 0x1582c%Z] (dirs [false]) true.
    branch_case as Hbw2.
    - hc_lin Hbw2. m3_rest 4%nat HADM HTAG HMC HC10 Hco Hn.
    - hc_lin Hbw2.
      run_fp 80%nat [0x1525c%Z; 0x1582c%Z] noscr true.
      branch_case as Hbw1; [ fail_g HADM |].
      hc_lin Hbw1. m3_rest 4%nat HADM HTAG HMC HC10 Hco Hn.
  Qed.


  Lemma m3b : forall (FPI : FPState) R M sz buf ic mc co,
    ADM FPI R M -> TAGC 0x6d414220 sz buf M -> mab_cellsI ic mc M -> curves10I M ->
    (0 <= co < 4294967296)%Z -> (co + 20 <= sz)%Z ->
    getr R 10 = Z_to_bv 64 (bv_unsigned buf + co) -> getr R 11 = Z_to_bv 64 (co + 20) -> getr R 12 = Z_to_bv 64 sz ->
    getr R 13 = buf ->
    cell64 SEGS M (spv - 176 + 0) eobw ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x15768) M rom) QP.
  Proof.
    intros FPI R M sz buf ic mc co HADM HTAG HMC HC10 Hco Hco20 H10 H11 H12 H13 S0.
    pose proof HMC as (_ & _ & _ & Hic & _).
    assert (H5 : ic = Z.of_nat 0 \/ ic = Z.of_nat 1 \/ ic = Z.of_nat 2 \/ ic = Z.of_nat 3 \/ ic = Z.of_nat 4) by (cbn; lia).
    destruct H5 as [Hn|[Hn|[Hn|[Hn|Hn]]]];
      [ eapply m3b0I | eapply m3b1I | eapply m3b2I | eapply m3b3 | eapply m3b4 ]; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma m3a : forall (FPI : FPState) R M sz buf ic mc r,
    ADM FPI R M -> TAGC 0x6d414220 sz buf M -> mab_cellsI ic mc M ->
    getr R 10 = Z_to_bv 64 r -> (r = 0%Z \/ (r = 1%Z /\ curves10I M)) ->
    getr R 19 = le4wI buf 24 -> getr R 20 = WI buf 24 -> getr R 21 = WI buf 27 -> getr R 22 = WI buf 26 ->
    getr R 9 = Z_to_bv 64 0xff00 ->
    cell64 SEGS M (spv - 176 + 0) eobw ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x1572c) M rom) QP.
  Proof.
    intros FPI R M sz buf ic mc r HADM HTAG HMC H10 Hr H19 H20 H21 H22 H23 S0.
    adm_facts HADM. pose proof HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c). pose proof (u64_range buf).
    pose proof (bb_range data bs buf 24) as R24. pose proof (bb_range data bs buf 25) as R25.
    pose proof (bb_range data bs buf 26) as R26. pose proof (bb_range data bs buf 27) as R27.
    destruct Hr as [-> | [-> HC10]].
    - pkg_tag HADM HTAG (@nil word) (@nil kentry) ltac:(constructor).
      pin_reg HR (10%bv:reg) (ELit 0%Z) by (cbn [edenot]; exact H10).
      run_fp 10%nat [0x1525c%Z] noscr true.
      adm_now HADM HADM1. apply (failkI _ _ _ HADM1).
    - pose proof (be4_range data bs buf 24) as Hco.
      pkg_tag HADM HTAG [WI buf 24; WI buf 25; WI buf 26; WI buf 27; Z_to_bv 64 (be4I buf 24)]
        [KRange (EVar 81) 0 255; KRange (EVar 82) 0 255; KRange (EVar 83) 0 255; KRange (EVar 84) 0 255;
         KRange (EVar 85) 0 4294967295]
        ltac:(repeat apply Forall_cons; try apply Forall_nil;
              apply krange_intro; cbn [edenot]; ev_simpl E; rewrite ?uW; try lia; rewrite u_small by lia; lia).
      pin_reg HR (10%bv:reg) (ELit 1%Z) by (cbn [edenot]; exact H10).
      pin_reg HR (19%bv:reg) (EAlu ALU_ADD (EVar 81) (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 82))
           (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 83)) (EMd M_MUL (ELit 16777216) (EVar 84)))))
        by (cbn [edenot]; ev_simpl E; rewrite H19; reflexivity).
      pin_reg HR (20%bv:reg) (EVar 81) by (cbn [edenot]; ev_simpl E; exact H20).
      pin_reg HR (21%bv:reg) (EVar 84) by (cbn [edenot]; ev_simpl E; exact H21).
      pin_reg HR (22%bv:reg) (EVar 83) by (cbn [edenot]; ev_simpl E; exact H22).
      pin_reg HR (9%bv:reg) (ELit 0xff00%Z) by (cbn [edenot]; exact H23).
      run_fp 30%nat [0x1525c%Z; 0x15758%Z] noscr true.
      (* [comment removed for export] *)
      assert (Hbe : be4I buf 24 = (bbI buf 27 + 256 * bbI buf 26 + 65536 * bbI buf 25 + 16777216 * bbI buf 24)%Z) by reflexivity.
      set (nu := fun k : nat => nth k [bbI buf 24; bbI buf 25; bbI buf 26; bbI buf 27] 0%Z).
      assert (nu_range : forall k, (0 <= nu k < 256)%Z).
      { intros k. unfold nu. destruct k as [|[|[|[|k]]]]; cbn [nth]; try lia. destruct k; cbn; lia. }
      set (atoms := [(EVar 81, (false, 0%nat)); (EVar 82, (false, 1%nat)); (EVar 83, (false, 2%nat)); (EVar 84, (false, 3%nat))]).
      assert (Hat : atoms_ok E nu atoms).
      { unfold atoms, atoms_ok. repeat apply Forall_cons; try apply Forall_nil;
          unfold atom_ok; cbn [edenot]; ev_simpl E; rewrite uW; reflexivity. }
      pin_reg HR (10%bv:reg) (EVar 85) by
        (rewrite (HR (10%bv:reg));
         lazymatch goal with |- edenot _ ?e = _ =>
           apply bv_eq; rewrite (beval_bytes E nu nu_range atoms e [3; 2; 1; 0]%nat Hat ltac:(cbn; lia) ltac:(vm_compute; reflexivity))
         end;
         cbn [edenot]; ev_simpl E; rewrite u_small by lia; rewrite Hbe; unfold nu; cbn [bytes_val nth]; lia).
      run_fp 20%nat [0x1525c%Z; 0x15768%Z] noscr true.
      branch_case as Hco20.
      { adm_now HADM HADM1. apply (failkI _ _ _ HADM1). }
      hc_lin Hco20.
      run_fp 20%nat [0x1525c%Z; 0x15768%Z] noscr true.
      adm_now HADM HADM1.
      apply (m3b _ _ _ sz buf ic mc (be4I buf 24) HADM1 HTAG HMC HC10 Hco ltac:(lia)).
      + regv_lin HR (10%bv:reg). rewrite u_small by lia. f_equal. lia.
      + regv_lin HR (11%bv:reg). rewrite u_small by lia. f_equal. lia.
      + regv HR (12%bv:reg). reflexivity.
      + regv HR (13%bv:reg). reflexivity.
      + exact S0.
  Qed.
End RD.
End LibReadA2BUbd.

Module LibReadA2BUbe.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Lib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibRodata OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibBswap.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfKc.
Import LibReadA2BUba LibReadA2BUbb LibReadA2BUbc LibReadA2BUbd.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
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
(* [comment removed for export] *)
Local Ltac ev_simpl E ::=   (* [comment removed for export] *)
  lazymatch goal with |- ?G =>
    let G1 := match tt with | _ => eval unfold E in G | _ => G end in
    let G2 := eval lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in G1 in
    change G2
  end.
Local Ltac ev_simpl_in E H ::= try unfold E in H; lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in H.
#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section RE.
  Variables (FPI0 : FPState) (regs0 : bvmap 5 word) (mem0 rom : word -> option byte) (ret : word).
  Variables (data : word) (len : Z) (bs : list byte) (sp T A : word) (pcs : Z).
  Hypothesis Hra : getr regs0 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HPRE : a2b_pre SEGS wp2_infoub data len bs sp T A pcs FPI0 regs0 mem0.
  Hypothesis Hcanon : canonicalize_contract SEGS wp3_infoub.
  Hypothesis Hrc : read_curves_contract SEGS wp2_infoub.

  #[local] Abbreviation a := (bv_unsigned A).
  #[local] Abbreviation spv := (bv_unsigned sp).
  #[local] Abbreviation t := (bv_unsigned T).
  #[local] Abbreviation ADM := (adm FPI0 regs0 mem0 ret data len bs sp T A).
  #[local] Abbreviation QP := (Qpost FPI0 regs0 mem0 rom ret data len bs sp T A pcs).
  #[local] Abbreviation CI := (chain_inv data len A).
  #[local] Abbreviation TAGC := (tagc data len T).
  #[local] Abbreviation pre_factsI := (pre_facts FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation pre_tagI := (pre_tag FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation pre_spI := (pre_sp FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation kn_adm_okI := (kn_adm_ok FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation kn_tag_okI := (kn_tag_ok FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation adm_frameI := (adm_frame FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation base_valsI := (base_vals regs0 ret data len).
  #[local] Abbreviation failkI := (failk FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE).
  #[local] Abbreviation in1I := (in1 FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).
  #[local] Abbreviation eobw := (Z_to_bv 64 (bv_unsigned data + len)).
  #[local] Abbreviation bbI := (bb data bs).
  #[local] Abbreviation WI := (W data bs).
  #[local] Abbreviation curves10I := (curves10 data len A).
  #[local] Abbreviation mab_cellsI := (mab_cells A).
  #[local] Abbreviation gslI := (gsl data bs).
  #[local] Abbreviation PvalI := (Pval data bs).
  #[local] Abbreviation be4I := (be4 data bs).
  #[local] Abbreviation le4wI := (le4w data bs).
  #[local] Abbreviation vals_m3I := (vals_m3 data len bs).
  #[local] Abbreviation curves10_frame1I := (curves10_frame1 FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation kn_m3_okI := (kn_m3_ok FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation curves0I := (curves0 data len A).
  #[local] Abbreviation curves0_frameI := (curves0_frame FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation tagc_frameI := (tagc_frame FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation in0I := (in0 FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).
  #[local] Abbreviation m3aI := (m3a FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).

  (* [comment removed for export] *)
  Ltac adm_facts HADM :=
    pose proof HADM as (A2 & A3 & A4 & A8 & A18 & AF & AS & AFR & AD & ARO & AWA & AWS);
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _);
    assert (U2 : bv_unsigned (getr _ 2) = (spv - 176)%Z) by (rewrite A2, u_small by lia; lia).

  Ltac pkg HADM extra kx ktac :=
    lazymatch goal with
    | |- runs_to _ (@mkst ?FPI ?R _ ?M _) _ =>
      set (E := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++
         [ret; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20; getr regs0 21;
          getr regs0 22; getr regs0 23; getr regs0 24; getr regs0 25; getr regs0 26; getr regs0 27;
          data; Z_to_bv 64 len] ++ extra)) (blobs_ev [bs]));
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs]));
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs]));
      pose proof (HR : id _) as HR0; pose proof (HF : id _) as HF0;
      let HK1 := fresh "HK1" in let HK2 := fresh "HK2" in
      pose proof (kn_adm_okI FPI R M extra HADM) as HK1; change (know_ok SEGS E M kn_adm) in HK1;
      assert (HK2 : know_ok SEGS E M kx); [ktac|];
      pose proof (know_ok_app SEGS E M kn_adm kx HK1 HK2) as HK; clear HK1 HK2;
      cbv beta delta [kn_adm app] in HK
    end.

  Ltac pkg_tag HADM HTAG rest kx ktac :=
    lazymatch type of HTAG with tagc _ _ _ ?ty ?sz ?buf _ =>
      pkg HADM ([Z_to_bv 64 sz; buf] ++ rest) (kn_tag ty ++ kx)
        ltac:(apply know_ok_app; [exact (kn_tag_okI _ _ _ ty sz buf rest HADM HTAG) | ktac])
    end.

  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.

  Ltac subst_mems :=
    repeat match goal with H : @eq (word -> option byte) ?x _ |- _ => is_var x; subst x end.

  Ltac adm_now HADM HADM1 :=
    subst_mems;
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1, HF : fregs_ok _ ?sfr (@fp_regs ?I1), HF0 : id (fregs_ok _ ?sfr0 (@fp_regs ?I0))
      |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ ?R ?M0 =>
        assert (HADM1 : ADM I1 R1 M1);
        [ apply (adm_frameI I0 I1 R R1 M0 M1 [] HADM);
          [ apply frame_mod_refl
          | apply Forall_nil
          | apply Forall_nil
          | regv HR (2%bv:reg); reflexivity
          | regv HR (3%bv:reg); reflexivity
          | regv HR (4%bv:reg); reflexivity
          | regv HR (8%bv:reg); reflexivity
          | regv HR (18%bv:reg); reflexivity
          | exact (fregs_same_on E sfr0 sfr _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)) ]
        | ]
      end
    end.
  (* [comment removed for export] *)


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac mods_in H :=
    repeat match type of H with context [ (?x mod ?m)%Z ] =>
      lazymatch x with context [ (_ mod _)%Z ] => fail | _ => rewrite (Z.mod_small x m) in H by lia end end.
  Ltac mods_goal :=
    repeat match goal with |- context [ (?x mod ?m)%Z ] =>
      lazymatch x with context [ (_ mod _)%Z ] => fail | _ => rewrite (Z.mod_small x m) by lia end end.

  (* [comment removed for export] *)
  Ltac zbool H :=
    first [ apply Z.ltb_lt in H | apply Z.ltb_ge in H | apply Z.eqb_eq in H | apply Z.eqb_neq in H ].
  Ltac hc_lin Hc :=
    revert Hc; rewrite ?branch_taken_Z; cbv beta iota; linearize;
    cbn [edenot fop1_denot fop2_denot fop3_denot];
    lazymatch goal with HK : know_ok _ ?E _ _ |- _ => ev_simpl E end;
    rewrite ?uW, ?Z_to_bv_unsigned, ?bv_wrap64_mod; intros Hc;
    try (apply (f_equal negb) in Hc; rewrite negb_involutive in Hc; cbn [negb] in Hc);
    mods_in Hc; zbool Hc.

  Ltac regions_eq :=
    cbn [regions_denot map fst snd]; unfold adenot, v_addi; cbn [a_base a_off edenot];
    lazymatch goal with HK : know_ok _ ?E _ _ |- _ => ev_simpl E end; rewrite_getr;
    repeat (apply f_equal2; [apply f_equal2; [apply f_equal; lia | lia] | ]); reflexivity.

  (* [comment removed for export] *)
  Ltac frame_logs RS :=
    lazymatch goal with
    | |- frame_mod ?m0 ?m0 _ => apply frame_mod_refl
    | HK : know_ok _ ?E _ _ |- frame_mod ?m0 (mem_denot _ ?m1 ?log) _ =>
        apply (frame_mod_trans_same m0 m1);
        [ frame_logs RS
        | apply (frame_mod_mem_denot E m1 log RS);
          [ lazymatch goal with H : log_flat _ log |- _ => exact H end
          | repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; unfold flat, estart;
            cbn [a_base a_off edenot]; ev_simpl E; rewrite_getr; lia
          | vm_compute; reflexivity ] ]
    end.

  (* [comment removed for export] *)
  Ltac frame_now HADM RS rsZ Hfr :=
    subst_mems;
    lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ _ ?M0 =>
    lazymatch goal with HK : know_ok _ ?E ?M1 _ |- _ =>
      assert (Hfr : frame_mod M0 M1 rsZ);
      [ replace rsZ with (regions_denot E RS) by regions_eq; frame_logs RS | ]
    end end.

  (* [comment removed for export] *)
  Ltac adm_fr HADM Hfr HADM1 :=
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1, HF : fregs_ok _ ?sfr (@fp_regs ?I1), HF0 : id (fregs_ok _ ?sfr0 (@fp_regs ?I0))
      |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ ?R ?M0 =>
        assert (HADM1 : ADM I1 R1 M1);
        [ apply (adm_frameI I0 I1 R R1 M0 M1 _ HADM Hfr);
          [ solve [unfold BIG; solve_within]
          | solve [pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ? & _); solve_apart]
          | regv HR (2%bv:reg); reflexivity
          | regv HR (3%bv:reg); reflexivity
          | regv HR (4%bv:reg); reflexivity
          | regv HR (8%bv:reg); reflexivity
          | regv HR (18%bv:reg); reflexivity
          | exact (fregs_same_on E sfr0 sfr _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)) ]
        | ]
      end
    end.

  (* [comment removed for export] *)
  Ltac w_lt :=
    rewrite ?uW;
    lazymatch goal with
    | |- (bb _ _ ?b ?i < _)%Z => pose proof (bb_range data bs b i); lia
    | |- _ => rewrite ?u_small by lia; lia
    end.

  (* [comment removed for export] *)
  Ltac flat_tac := unfold flat, estart; cbn [a_base a_off edenot];
    lazymatch goal with HK : know_ok _ ?E _ _ |- _ => ev_simpl E end; rewrite_getr; lia.
  Ltac kcellv b k n H :=
    lazymatch goal with HK : know_ok _ ?E ?M ?kn |- _ =>
      let r := eval vm_compute in (kread SEGS kn b k n) in
      lazymatch r with
      | Some ?v =>
        let KR := fresh "KR" in let Hfl := fresh "Hfl" in
        kread_rdn_fast SEGS E M kn b k n v HK H;
        lazymatch type of H with ?FL -> _ => assert (Hfl : FL) by flat_tac; specialize (H Hfl); clear Hfl end;
        unfold adenot, v_addi in H; cbn [a_base a_off edenot] in H; ev_simpl_in E H; rewrite_getr_in H;
        rewrite ?ext_val_zx_id4 in H by w_lt;
        rewrite ?ext_val_zx_id1 in H by w_lt
      | _ => fail "kcellv: no knowledge at" b k n
      end
    end.


  (* [comment removed for export] *)
  Ltac fail_st HADM RS rsZ :=
    let Hfr := fresh "Hfr" in let HADM1 := fresh "HADMf" in
    frame_now HADM RS rsZ Hfr; adm_fr HADM Hfr HADM1;
    match goal with H : adm _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => apply (failkI _ _ _ H) end.
  (* [comment removed for export] *)
  Ltac in_kept := cbn; repeat (first [ left; reflexivity | right ]).

  (* [comment removed for export] *)
  Ltac fail0 HADM :=
    let HADM1 := fresh "HADMf" in adm_now HADM HADM1;
    match goal with H : adm _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => apply (failkI _ _ _ H) end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition stk (buf : word) (M : word -> option byte) : Prop :=
    cell64 SEGS M (spv - 176 + 64) (WI buf 24) /\ cell64 SEGS M (spv - 176 + 56) (WI buf 27) /\
    cell64 SEGS M (spv - 176 + 48) (WI buf 26) /\ cell64 SEGS M (spv - 176 + 24) (WI buf 28) /\
    cell64 SEGS M (spv - 176 + 40) (WI buf 30) /\ cell64 SEGS M (spv - 176 + 32) (WI buf 31) /\
    cell64 SEGS M (spv - 176 + 16) (WI buf 25) /\ cell64 SEGS M (spv - 176 + 8) (WI buf 29) /\
    cell64 SEGS M (spv - 176 + 0) eobw.

  Lemma stk_frame : forall buf M M' rs,
    stk buf M -> frame_mod M M' rs -> apart (spv - 176) 72 rs -> stk buf M'.
  Proof.
    intros buf M M' rs (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9) Hf Hap.
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & _). unfold stk.
    repeat match goal with |- _ /\ _ => split end;
      (eapply cell64_frame; [exact Hf | eassumption | lia | lia | eapply apart_sub; [exact Hap|lia|lia|lia]]).
  Qed.

  (* [comment removed for export] *)
  Definition kn_stk : list kentry :=
    [KWord (SA (EVar 2) 64) 8 (EVar 81); KWord (SA (EVar 2) 16) 8 (EVar 82); KWord (SA (EVar 2) 48) 8 (EVar 83);
     KWord (SA (EVar 2) 56) 8 (EVar 84); KWord (SA (EVar 2) 24) 8 (EVar 85); KWord (SA (EVar 2) 8) 8 (EVar 86);
     KWord (SA (EVar 2) 40) 8 (EVar 87); KWord (SA (EVar 2) 32) 8 (EVar 88); KWord (SA (EVar 2) 0) 8 (EVar 89);
     KRange (EVar 81) 0 255; KRange (EVar 82) 0 255; KRange (EVar 83) 0 255; KRange (EVar 84) 0 255;
     KRange (EVar 85) 0 255; KRange (EVar 86) 0 255; KRange (EVar 87) 0 255; KRange (EVar 88) 0 255;
     KRange (EVar 89) 1 140737488355328].
  Definition vals_stk (buf : word) : list word :=
    [WI buf 24; WI buf 25; WI buf 26; WI buf 27; WI buf 28; WI buf 29; WI buf 30; WI buf 31; eobw].

  Lemma kn_stk_ok : forall (FPI : FPState) R M sz buf rest,
    ADM FPI R M -> stk buf M ->
    know_ok SEGS (Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ base_valsI ++
                                  ([Z_to_bv 64 sz; buf] ++ vals_stk buf ++ rest))) (blobs_ev [bs])) M kn_stk.
  Proof.
    intros FPI R M sz buf rest HADM (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9). adm_facts HADM.
    set (E := Env _ _). unfold base_vals, vals_stk in E. unfold kn_stk.
    repeat apply Forall_cons; try apply Forall_nil.
    all: try (apply krange_intro; cbn [edenot]; ev_simpl E; rewrite ?uW;
              first [ match goal with |- (_ <= bb _ _ ?b ?i <= _)%Z => pose proof (bb_range data bs b i); lia end
                    | rewrite u_small by lia; lia ]).
    all: eapply (kword_intro SEGS E M (EVar 2) (getr R 2) _ 8 _ _);
           [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia |
            rewrite U2; unfold cell64, cell in *;
            match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ =>
              first [ replace x with (spv - 176 + 64)%Z by ring; eassumption
                    | replace x with (spv - 176 + 16)%Z by ring; eassumption
                    | replace x with (spv - 176 + 48)%Z by ring; eassumption
                    | replace x with (spv - 176 + 56)%Z by ring; eassumption
                    | replace x with (spv - 176 + 40)%Z by ring; eassumption
                    | replace x with (spv - 176 + 8)%Z by ring; eassumption
                    | replace x with (spv - 176 + 32)%Z by ring; eassumption
                    | replace x with (spv - 176 + 24)%Z by ring; eassumption
                    | replace x with (spv - 176 + 0)%Z by ring; eassumption ] end].
  Qed.

  (* [comment removed for export] *)
  Ltac pkg_stk HADM HTAG HSTK rest kx ktac :=
    lazymatch type of HTAG with tagc _ _ _ ?ty ?sz ?buf _ =>
      pkg HADM ([Z_to_bv 64 sz; buf] ++ [WI buf 24; WI buf 25; WI buf 26; WI buf 27; WI buf 28; WI buf 29; WI buf 30; WI buf 31; eobw] ++ rest) (kn_tag ty ++ kn_stk ++ kx)
        ltac:(apply know_ok_app; [exact (kn_tag_okI _ _ _ ty sz buf _ HADM HTAG)
             | apply know_ok_app; [exact (kn_stk_ok _ _ _ sz buf rest HADM HSTK) | ktac]]);
      lazymatch goal with HK : know_ok _ _ _ ?kn |- _ =>
        let kn' := eval vm_compute in kn in change kn with kn' in HK end;
      match goal with Edef := Env _ _ |- _ => cbn [app] in Edef end
    end.

  (* [comment removed for export] *)
  Lemma mab_cells_frame : forall ic mc M M' rs,
    mab_cellsI ic mc M -> frame_mod M M' rs -> apart (a + 144) 4 rs -> apart (a + 296) 8 rs -> mab_cellsI ic mc M'.
  Proof.
    intros ic mc M M' rs (C1 & C2 & C3 & H4 & H5) Hf Hap1 Hap2. pose proof pre_factsI as (P1 & P2 & P3 & P4 & _).
    split; [eapply cell32_frame; [exact Hf|exact C1|lia|lia|exact Hap1]|].
    split; [eapply cell32_frame; [exact Hf|exact C2|lia|lia|eapply apart_sub; [exact Hap2|lia|lia|lia]]|].
    split; [eapply cell32_frame; [exact Hf|exact C3|lia|lia|eapply apart_sub; [exact Hap2|lia|lia|lia]]|].
    split; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rc_pre_at : forall (FPI : FPState) R M ty sz buf Cz k (offw : word),
    ADM FPI R M -> TAGC ty sz buf M -> (0 <= k <= 4)%Z -> (a <= Cz)%Z -> (Cz + 32 * k <= a + 400)%Z -> (Cz mod 8 = 0)%Z ->
    getr R 10 = buf -> getr R 11 = Z_to_bv 64 sz -> getr R 12 = offw -> getr R 13 = Z_to_bv 64 k ->
    getr R 14 = Z_to_bv 64 Cz ->
    rcurves_pre SEGS wp2_infoub data len bs (Z_to_bv 64 (spv - 176)) buf (Z_to_bv 64 Cz) sz offw k FPI R M.
  Proof.
    intros FPI R M ty sz buf Cz k offw HADM (T1 & T2 & T3 & T4 & T5) Hk HC1 HC2 HC3 H10 H11 H12 H13 H14.
    adm_facts HADM. pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10 & P11 & P12 & _).
    unfold rcurves_pre. cbv zeta.
    change (w_rcurves_d wp2_infoub) with 128%Z. change (w_ro_lo wp2_infoub) with 0x103ec%Z. change (w_ro_hi wp2_infoub) with 0x10490%Z.
    rewrite !u_small by lia. destruct T2 as [Hsz _].
    split; [exact A2|]. split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [exact H13|].
    split; [exact H14|]. split; [exact AD|]. split; [lia|]. split; [exact T5|]. split; [exact Hk|].
    split; [intros Hk0; eapply writable_sub; [exact AWA|lia|lia|lia]|].
    split; [exact HC3|]. split; [intros; lia|].
    split; [apply mod16_sub; [exact P1|reflexivity]|].
    split; [eapply writable_sub; [exact AWS|lia|lia|lia]|].
    split; [exact ARO|]. lia.
  Qed.

  Lemma adm_rc : forall (FPI FPI' : FPState) R R' M M' Cz k,
    ADM FPI R M -> (a <= Cz)%Z -> (0 <= k)%Z -> (Cz + 32 * k <= a + 400)%Z ->
    frame_mod M M' [(Z_to_bv 64 (spv - 176 - 128), 128%Z); (Z_to_bv 64 Cz, (32 * k)%Z)] ->
    regs_kept abi_kept R R' ->
    (forall r, In r abi_fkept -> reg_get (fp_regs (FPState:=FPI')) r = reg_get (fp_regs (FPState:=FPI)) r) ->
    ADM FPI' R' M' /\ (forall ty sz buf, TAGC ty sz buf M -> TAGC ty sz buf M') /\ (forall buf, stk buf M -> stk buf M').
  Proof.
    intros FPI FPI' R R' M M' Cz k HADM H1 H2 H3 Hf Hk Hfk.
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _).
    pose proof pre_tagI as (Q1 & Q2 & Q3 & Q4 & Q5).
    split; [|split].
    - apply (adm_frameI FPI FPI' R R' M M' _ HADM Hf).
      + unfold BIG; solve_within.
      + solve_apart.
      + apply Hk; in_kept. + apply Hk; in_kept. + apply Hk; in_kept. + apply Hk; in_kept. + apply Hk; in_kept.
      + exact Hfk.
    - intros ty sz buf HT. eapply tagc_frameI; [exact HT|exact Hf|]. solve_apart.
    - intros buf HS. eapply stk_frame; [exact HS|exact Hf|]. solve_apart.
  Qed.

  (* [comment removed for export] *)
  Lemma curves0_rc : forall M M' base k,
    curves0I M ->
    frame_mod M M' [(Z_to_bv 64 (spv - 176 - 128), 128%Z); (Z_to_bv 64 (a + base), (32 * k)%Z)] ->
    (0 <= k)%Z -> (0 <= base)%Z -> (base + 32 * k <= 128 \/ (144 <= base /\ base + 32 * k <= 400))%Z ->
    (forall i, (0 <= i < k)%Z -> curve_ok SEGS M' data len (a + base + 32 * i)) ->
    (forall o, In o a2b_curve_offsets ->
       (base + 32 * k <= o \/ o + 32 <= base)%Z \/ (exists i, (0 <= i < k)%Z /\ o = (base + 32 * i)%Z)) ->
    curves0I M'.
  Proof.
    intros M M' base k [Hall (g8 & g16 & Hg8 & Hg16)] Hf Hk Hb Hbk Hnew Ho.
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _).
    split.
    - apply Forall_forall. intros o Hin.
      destruct (Ho o Hin) as [Hap | (i & Hi & ->)].
      + pose proof (proj1 (Forall_forall _ _) Hall o Hin) as Hc. cbv beta in Hc.
        pose proof (offsets_bound o Hin) as (B1 & B2 & _).
        eapply curve_ok_frame; [exact Hf|exact Hc|lia|lia|]. solve_apart.
      + replace (a + (base + 32 * i))%Z with (a + base + 32 * i)%Z by lia. apply Hnew. exact Hi.
    - exists g8, g16. split; (eapply cell64_frame; [exact Hf|eassumption|lia|lia|solve_apart]).
  Qed.

  Ltac offsets_cases Hin :=
    cbn [a2b_curve_offsets In] in Hin;
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma jseg : forall (FPI : FPState) R M sz buf ic mc,
    ADM FPI R M -> TAGC 0x6d414220 sz buf M -> (32 <= sz)%Z -> mab_cellsI ic mc M -> curves0I M -> stk buf M ->
    getr R 20 = WI buf 24 -> getr R 21 = WI buf 27 -> getr R 22 = WI buf 26 ->
    getr R 6 = WI buf 30 -> getr R 7 = WI buf 31 -> getr R 9 = Z_to_bv 64 0xff00 ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x156b8) M rom) QP.
  Proof.
    intros FPI R M sz buf ic mc HADM HTAG Hsz HMC HC0 HSTK H20 H21 H22 H16 H17 H5.
    adm_facts HADM. pose proof HMC as (C1 & C2 & C3 & Hic & Hmc).
    pose proof HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c). pose proof (u64_range buf).
    pkg_stk HADM HTAG HSTK [Z_to_bv 64 ic; Z_to_bv 64 mc]
      [KWord (SA (EVar 8) 144) 4 (EVar 90); KRange (EVar 90) 0 4; KWord (SA (EVar 8) 300) 4 (ELit 3);
       KWord (SA (EVar 8) 296) 4 (EVar 91)]
      ltac:(repeat apply Forall_cons; try apply Forall_nil;
            [ eapply (kword_intro SEGS E _ (EVar 8) A 144 4 (EVar 90) (Z_to_bv 64 ic)); [cbn [edenot]; ev_simpl E; exact A8 | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | exact (proj2 C1)]
            | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia
            | eapply (kword_intro SEGS E _ (EVar 8) A 300 4 (ELit 3%Z) (Z_to_bv 64 3)); [cbn [edenot]; ev_simpl E; exact A8 | reflexivity | lia | lia | lia | lia | exact (proj2 C2)]
            | eapply (kword_intro SEGS E _ (EVar 8) A 296 4 (EVar 91) (Z_to_bv 64 mc)); [cbn [edenot]; ev_simpl E; exact A8 | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | exact (proj2 C3)] ]).
    pin_reg HR (20%bv:reg) (EVar 81) by (cbn [edenot]; ev_simpl E; exact H20).
    pin_reg HR (21%bv:reg) (EVar 84) by (cbn [edenot]; ev_simpl E; exact H21).
    pin_reg HR (22%bv:reg) (EVar 83) by (cbn [edenot]; ev_simpl E; exact H22).
    pin_reg HR (6%bv:reg) (EVar 87) by (cbn [edenot]; ev_simpl E; exact H16).
    pin_reg HR (7%bv:reg) (EVar 88) by (cbn [edenot]; ev_simpl E; exact H17).
    pin_reg HR (9%bv:reg) (ELit 0xff00%Z) by (cbn [edenot]; exact H5).
    run_fp 60%nat [0x16914%Z; 0x15154%Z; 0x1525c%Z] noscr true.
    branch_case as Ha0.
    - (* [comment removed for export] *)
      run_fp 20%nat [0x16914%Z; 0x15154%Z; 0x1525c%Z] noscr true.
      branch_case as Hcl; [fail0 HADM|].
      run_fp 20%nat [0x16914%Z; 0x15154%Z; 0x1525c%Z] noscr true.
      branch_case as Hio; [fail0 HADM|].
      hc_lin Hio.
      run_fp 20%nat [0x16914%Z; 0x15154%Z; 0x1525c%Z] noscr true.
      (* [comment removed for export] *)
      frame_now HADM [(SA (EVar 8) 144, 4%Z)] [(Z_to_bv 64 (a + 144), 4%Z)] Hfr.
      adm_fr HADM Hfr HADM1.
      lazymatch goal with |- runs_to _ (@mkst _ _ _ ?M1 _) _ => remember M1 as Mz eqn:HMz; clear HMz end.
      assert (HC0' : curves0I Mz).
      { eapply curves0_frameI; [exact HC0 | exact Hfr | solve_apart |].
        unfold a2b_curve_offsets. repeat (apply Forall_cons; [solve_apart|]). apply Forall_nil. }
      apply (in0I _ _ _ 0%Z mc HADM1).
      kcellv (EVar 8) 144%Z 4%nat C144. kcellv (EVar 8) 296%Z 4%nat C296. kcellv (EVar 8) 300%Z 4%nat C300.
      split; [split; [lia | exact C144]|].
      split; [split; [lia | exact C296]|].
      split; [split; [lia | exact C300]|].
      split; [lia|]. split; [exact Hmc|].
      split; [exact (proj1 HC0')|].
      destruct HC0' as [_ (g8 & g16 & Hg8 & Hg16)].
      exists 0%Z, 3%Z, (@nil Z), g8, g16.
      split; [split; [lia | exact C144]|]. split; [split; [lia | exact C300]|].
      split; [lia|]. split; [reflexivity|]. split; [apply Forall_nil|].
      split; [intros i Hi; exfalso; lia|].
      split; [exact Hg8|]. split; [exact Hg16|]. split; [reflexivity|].
      intros H0; exfalso; apply H0; reflexivity.
    - (* [comment removed for export] *)
      run_fp 30%nat [0x16914%Z; 0x15154%Z; 0x1525c%Z] noscr true.
      branch_case as Hcl; [fail0 HADM|].
      run_fp 30%nat [0x16914%Z; 0x15154%Z; 0x1525c%Z] noscr true.
      adm_now HADM HADM1.
      eapply rt_call.
      { eapply (Hrc data len bs (Z_to_bv 64 (spv - 176)) buf (Z_to_bv 64 a) sz _ ic _ _ _ rom (Z_to_bv 64 0x1572c)).
        - regv HR (1%bv:reg). reflexivity.
        - apply ret_ok_even. rewrite u_small by lia. reflexivity.
        - eapply (rc_pre_at _ _ _ 0x6d414220%Z sz buf a ic);
            [ exact HADM1 | exact HTAG | lia | lia | lia | exact P2
            | regv HR (10%bv:reg); reflexivity
            | regv HR (11%bv:reg); reflexivity
            | reflexivity
            | regv HR (13%bv:reg); reflexivity
            | regv HR (14%bv:reg); rewrite A8; symmetry; apply Z_to_bv_bv_unsigned ].
      }
      cbv beta. intros FPI' R' M' (Hkeep & Hfkeep & Hpost).
      unfold rcurves_post in Hpost. cbv zeta in Hpost. change (w_rcurves_d wp2_infoub) with 128%Z in Hpost.
      rewrite (u_small (spv - 176)), (u_small a) in Hpost by lia.
      destruct Hpost as (Hfr & r & H10' & Hr01 & Hcv).
      destruct (adm_rc _ FPI' _ R' _ M' a ic HADM1 ltac:(lia) ltac:(lia) ltac:(lia) Hfr Hkeep Hfkeep) as (HADM' & HT' & HS').
      pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10 & P11 & P12 & _).
      apply (m3aI FPI' R' M' sz buf ic mc r HADM' (HT' _ _ _ HTAG)).
      + eapply mab_cells_frame; [exact HMC | exact Hfr | solve_apart | solve_apart].
      + exact H10'.
      + destruct Hr01 as [-> | ->]; [left; reflexivity | right; split; [reflexivity|]].
        eapply proj1. eapply (curves0_rc M M' 0%Z ic HC0); [ | lia | lia | lia | | ].
        * replace (a + 0)%Z with a by lia. exact Hfr.
        * intros i Hi. replace (a + 0 + 32 * i)%Z with (a + 32 * i)%Z by lia. apply Hcv; [reflexivity | exact Hi].
        * intros o Hin. offsets_cases Hin;
            first [ left; lia
                  | destruct (Z_lt_le_dec 0 ic); [right; exists 0%Z; lia | left; lia]
                  | destruct (Z_lt_le_dec 1 ic); [right; exists 1%Z; lia | left; lia]
                  | destruct (Z_lt_le_dec 2 ic); [right; exists 2%Z; lia | left; lia]
                  | destruct (Z_lt_le_dec 3 ic); [right; exists 3%Z; lia | left; lia] ].
      + rewrite (Hkeep 19%bv ltac:(in_kept)). regv HR (19%bv:reg). reflexivity.
      + rewrite (Hkeep 20%bv ltac:(in_kept)). regv HR (20%bv:reg). reflexivity.
      + rewrite (Hkeep 21%bv ltac:(in_kept)). regv HR (21%bv:reg). reflexivity.
      + rewrite (Hkeep 22%bv ltac:(in_kept)). regv HR (22%bv:reg). reflexivity.
      + rewrite (Hkeep 9%bv ltac:(in_kept)). regv HR (9%bv:reg). reflexivity.
      + destruct (HS' _ HSTK) as (_ & _ & _ & _ & _ & _ & _ & _ & Se). exact Se.
  Qed.
End RE.
End LibReadA2BUbe.

Module LibReadA2BUbf.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Lib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibRodata OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibBswap.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfKc.
Import LibReadA2BUba LibReadA2BUbb LibReadA2BUbc LibReadA2BUbd LibReadA2BUbe.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
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
(* [comment removed for export] *)
Local Ltac ev_simpl E ::=   (* [comment removed for export] *)
  lazymatch goal with |- ?G =>
    let G1 := match tt with | _ => eval unfold E in G | _ => G end in
    let G2 := eval lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in G1 in
    change G2
  end.
Local Ltac ev_simpl_in E H ::= try unfold E in H; lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in H.
#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section RF.
  Variables (FPI0 : FPState) (regs0 : bvmap 5 word) (mem0 rom : word -> option byte) (ret : word).
  Variables (data : word) (len : Z) (bs : list byte) (sp T A : word) (pcs : Z).
  Hypothesis Hra : getr regs0 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HPRE : a2b_pre SEGS wp2_infoub data len bs sp T A pcs FPI0 regs0 mem0.
  Hypothesis Hcanon : canonicalize_contract SEGS wp3_infoub.
  Hypothesis Hrc : read_curves_contract SEGS wp2_infoub.

  #[local] Abbreviation a := (bv_unsigned A).
  #[local] Abbreviation spv := (bv_unsigned sp).
  #[local] Abbreviation t := (bv_unsigned T).
  #[local] Abbreviation ADM := (adm FPI0 regs0 mem0 ret data len bs sp T A).
  #[local] Abbreviation QP := (Qpost FPI0 regs0 mem0 rom ret data len bs sp T A pcs).
  #[local] Abbreviation CI := (chain_inv data len A).
  #[local] Abbreviation TAGC := (tagc data len T).
  #[local] Abbreviation pre_factsI := (pre_facts FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation pre_tagI := (pre_tag FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation pre_spI := (pre_sp FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation kn_adm_okI := (kn_adm_ok FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation kn_tag_okI := (kn_tag_ok FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation adm_frameI := (adm_frame FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation base_valsI := (base_vals regs0 ret data len).
  #[local] Abbreviation failkI := (failk FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE).
  #[local] Abbreviation in1I := (in1 FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).
  #[local] Abbreviation eobw := (Z_to_bv 64 (bv_unsigned data + len)).
  #[local] Abbreviation bbI := (bb data bs).
  #[local] Abbreviation WI := (W data bs).
  #[local] Abbreviation curves10I := (curves10 data len A).
  #[local] Abbreviation mab_cellsI := (mab_cells A).
  #[local] Abbreviation gslI := (gsl data bs).
  #[local] Abbreviation PvalI := (Pval data bs).
  #[local] Abbreviation be4I := (be4 data bs).
  #[local] Abbreviation le4wI := (le4w data bs).
  #[local] Abbreviation vals_m3I := (vals_m3 data len bs).
  #[local] Abbreviation curves10_frame1I := (curves10_frame1 FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation kn_m3_okI := (kn_m3_ok FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation curves0I := (curves0 data len A).
  #[local] Abbreviation curves0_frameI := (curves0_frame FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation tagc_frameI := (tagc_frame FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation in0I := (in0 FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).
  #[local] Abbreviation m3aI := (m3a FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).
  #[local] Abbreviation stkI := (stk data len bs sp).
  #[local] Abbreviation kn_stk_okI := (kn_stk_ok FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation stk_frameI := (stk_frame FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation mab_cells_frameI := (mab_cells_frame FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation rc_pre_atI := (rc_pre_at FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation adm_rcI := (adm_rc FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation curves0_rcI := (curves0_rc FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation jsegI := (jseg FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon Hrc).

  (* [comment removed for export] *)
  Ltac adm_facts HADM :=
    pose proof HADM as (A2 & A3 & A4 & A8 & A18 & AF & AS & AFR & AD & ARO & AWA & AWS);
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _);
    assert (U2 : bv_unsigned (getr _ 2) = (spv - 176)%Z) by (rewrite A2, u_small by lia; lia).

  Ltac pkg HADM extra kx ktac :=
    lazymatch goal with
    | |- runs_to _ (@mkst ?FPI ?R _ ?M _) _ =>
      set (E := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++
         [ret; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20; getr regs0 21;
          getr regs0 22; getr regs0 23; getr regs0 24; getr regs0 25; getr regs0 26; getr regs0 27;
          data; Z_to_bv 64 len] ++ extra)) (blobs_ev [bs]));
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs]));
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs]));
      pose proof (HR : id _) as HR0; pose proof (HF : id _) as HF0;
      let HK1 := fresh "HK1" in let HK2 := fresh "HK2" in
      pose proof (kn_adm_okI FPI R M extra HADM) as HK1; change (know_ok SEGS E M kn_adm) in HK1;
      assert (HK2 : know_ok SEGS E M kx); [ktac|];
      pose proof (know_ok_app SEGS E M kn_adm kx HK1 HK2) as HK; clear HK1 HK2;
      cbv beta delta [kn_adm app] in HK
    end.

  Ltac pkg_tag HADM HTAG rest kx ktac :=
    lazymatch type of HTAG with tagc _ _ _ ?ty ?sz ?buf _ =>
      pkg HADM ([Z_to_bv 64 sz; buf] ++ rest) (kn_tag ty ++ kx)
        ltac:(apply know_ok_app; [exact (kn_tag_okI _ _ _ ty sz buf rest HADM HTAG) | ktac])
    end.

  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.

  Ltac subst_mems :=
    repeat match goal with H : @eq (word -> option byte) ?x _ |- _ => is_var x; subst x end.

  Ltac adm_now HADM HADM1 :=
    subst_mems;
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1, HF : fregs_ok _ ?sfr (@fp_regs ?I1), HF0 : id (fregs_ok _ ?sfr0 (@fp_regs ?I0))
      |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ ?R ?M0 =>
        assert (HADM1 : ADM I1 R1 M1);
        [ apply (adm_frameI I0 I1 R R1 M0 M1 [] HADM);
          [ apply frame_mod_refl
          | apply Forall_nil
          | apply Forall_nil
          | regv HR (2%bv:reg); reflexivity
          | regv HR (3%bv:reg); reflexivity
          | regv HR (4%bv:reg); reflexivity
          | regv HR (8%bv:reg); reflexivity
          | regv HR (18%bv:reg); reflexivity
          | exact (fregs_same_on E sfr0 sfr _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)) ]
        | ]
      end
    end.
  (* [comment removed for export] *)


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac mods_in H :=
    repeat match type of H with context [ (?x mod ?m)%Z ] =>
      lazymatch x with context [ (_ mod _)%Z ] => fail | _ => rewrite (Z.mod_small x m) in H by lia end end.
  Ltac mods_goal :=
    repeat match goal with |- context [ (?x mod ?m)%Z ] =>
      lazymatch x with context [ (_ mod _)%Z ] => fail | _ => rewrite (Z.mod_small x m) by lia end end.

  (* [comment removed for export] *)
  Ltac zbool H :=
    first [ apply Z.ltb_lt in H | apply Z.ltb_ge in H | apply Z.eqb_eq in H | apply Z.eqb_neq in H ].
  Ltac hc_lin Hc :=
    revert Hc; rewrite ?branch_taken_Z; cbv beta iota; linearize;
    cbn [edenot fop1_denot fop2_denot fop3_denot];
    lazymatch goal with HK : know_ok _ ?E _ _ |- _ => ev_simpl E end;
    rewrite ?uW, ?Z_to_bv_unsigned, ?bv_wrap64_mod; intros Hc;
    try (apply (f_equal negb) in Hc; rewrite negb_involutive in Hc; cbn [negb] in Hc);
    mods_in Hc; zbool Hc.

  Ltac regions_eq :=
    cbn [regions_denot map fst snd]; unfold adenot, v_addi; cbn [a_base a_off edenot];
    lazymatch goal with HK : know_ok _ ?E _ _ |- _ => ev_simpl E end; rewrite_getr;
    repeat (apply f_equal2; [apply f_equal2; [apply f_equal; lia | lia] | ]); reflexivity.

  (* [comment removed for export] *)
  Ltac frame_logs RS :=
    lazymatch goal with
    | |- frame_mod ?m0 ?m0 _ => apply frame_mod_refl
    | HK : know_ok _ ?E _ _ |- frame_mod ?m0 (mem_denot _ ?m1 ?log) _ =>
        apply (frame_mod_trans_same m0 m1);
        [ frame_logs RS
        | apply (frame_mod_mem_denot E m1 log RS);
          [ lazymatch goal with H : log_flat _ log |- _ => exact H end
          | repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; unfold flat, estart;
            cbn [a_base a_off edenot]; ev_simpl E; rewrite_getr; lia
          | vm_compute; reflexivity ] ]
    end.

  (* [comment removed for export] *)
  Ltac frame_now HADM RS rsZ Hfr :=
    subst_mems;
    lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ _ ?M0 =>
    lazymatch goal with HK : know_ok _ ?E ?M1 _ |- _ =>
      assert (Hfr : frame_mod M0 M1 rsZ);
      [ replace rsZ with (regions_denot E RS) by regions_eq; frame_logs RS | ]
    end end.

  (* [comment removed for export] *)
  Ltac adm_fr HADM Hfr HADM1 :=
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1, HF : fregs_ok _ ?sfr (@fp_regs ?I1), HF0 : id (fregs_ok _ ?sfr0 (@fp_regs ?I0))
      |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ ?R ?M0 =>
        assert (HADM1 : ADM I1 R1 M1);
        [ apply (adm_frameI I0 I1 R R1 M0 M1 _ HADM Hfr);
          [ solve [unfold BIG; solve_within]
          | solve [pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ? & _); solve_apart]
          | regv HR (2%bv:reg); reflexivity
          | regv HR (3%bv:reg); reflexivity
          | regv HR (4%bv:reg); reflexivity
          | regv HR (8%bv:reg); reflexivity
          | regv HR (18%bv:reg); reflexivity
          | exact (fregs_same_on E sfr0 sfr _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)) ]
        | ]
      end
    end.

  (* [comment removed for export] *)
  Ltac w_lt :=
    rewrite ?uW;
    lazymatch goal with
    | |- (bb _ _ ?b ?i < _)%Z => pose proof (bb_range data bs b i); lia
    | |- _ => rewrite ?u_small by lia; lia
    end.

  (* [comment removed for export] *)
  Ltac flat_tac := unfold flat, estart; cbn [a_base a_off edenot];
    lazymatch goal with HK : know_ok _ ?E _ _ |- _ => ev_simpl E end; rewrite_getr; lia.
  Ltac kcellv b k n H :=
    lazymatch goal with HK : know_ok _ ?E ?M ?kn |- _ =>
      let r := eval vm_compute in (kread SEGS kn b k n) in
      lazymatch r with
      | Some ?v =>
        let KR := fresh "KR" in let Hfl := fresh "Hfl" in
        kread_rdn_fast SEGS E M kn b k n v HK H;
        lazymatch type of H with ?FL -> _ => assert (Hfl : FL) by flat_tac; specialize (H Hfl); clear Hfl end;
        unfold adenot, v_addi in H; cbn [a_base a_off edenot] in H; ev_simpl_in E H; rewrite_getr_in H;
        rewrite ?ext_val_zx_id4 in H by w_lt;
        rewrite ?ext_val_zx_id1 in H by w_lt
      | _ => fail "kcellv: no knowledge at" b k n
      end
    end.


  (* [comment removed for export] *)
  Ltac fail_st HADM RS rsZ :=
    let Hfr := fresh "Hfr" in let HADM1 := fresh "HADMf" in
    frame_now HADM RS rsZ Hfr; adm_fr HADM Hfr HADM1;
    match goal with H : adm _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => apply (failkI _ _ _ H) end.
  (* [comment removed for export] *)
  Ltac in_kept := cbn; repeat (first [ left; reflexivity | right ]).

  (* [comment removed for export] *)
  Ltac fail0 HADM :=
    let HADM1 := fresh "HADMf" in adm_now HADM HADM1;
    match goal with H : adm _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => apply (failkI _ _ _ H) end.


  Ltac pkg_stk HADM HTAG HSTK rest kx ktac :=
    lazymatch type of HTAG with tagc _ _ _ ?ty ?sz ?buf _ =>
      pkg HADM ([Z_to_bv 64 sz; buf] ++ [WI buf 24; WI buf 25; WI buf 26; WI buf 27; WI buf 28; WI buf 29; WI buf 30; WI buf 31; eobw] ++ rest) (kn_tag ty ++ kn_stk ++ kx)
        ltac:(apply know_ok_app; [exact (kn_tag_okI _ _ _ ty sz buf _ HADM HTAG)
             | apply know_ok_app; [exact (kn_stk_okI _ _ _ sz buf rest HADM HSTK) | ktac]]);
      lazymatch goal with HK : know_ok _ _ _ ?kn |- _ =>
        let kn' := eval vm_compute in kn in change kn with kn' in HK end;
      match goal with Edef := Env _ _ |- _ => cbn [app] in Edef end
    end.

  Ltac offsets_cases Hin :=
    cbn [a2b_curve_offsets In] in Hin;
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]].

  Lemma pre_pcs : (pcs = 0 \/ pcs = 1)%Z.
  Proof. destruct HPRE as (_ & _ & _ & _ & _ & H & _). exact H. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma m2b : forall (FPI : FPState) R M sz buf ic mo,
    ADM FPI R M -> TAGC 0x6d414220 sz buf M -> (32 <= sz)%Z -> mab_cellsI ic 3 M -> curves0I M -> stkI buf M ->
    (0 <= mo < 4294967296)%Z -> (mo + 48 <= sz)%Z ->
    getr R 10 = Z_to_bv 64 mo -> getr R 9 = Z_to_bv 64 0xff00 ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x152c4) M rom) QP.
  Proof.
    intros FPI R M sz buf ic mo HADM HTAG Hsz HMC HC0 HSTK Hmo Hmo48 H10 H5.
    adm_facts HADM. pose proof HMC as (C1 & C2 & C3 & Hic & Hmc).
    pose proof HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c). pose proof (u64_range buf).
    pose proof AD as (Hlen & Hbs & Hdnz & Hdhi & Hblob).
    pkg_stk HADM HTAG HSTK [Z_to_bv 64 ic; Z_to_bv 64 3; Z_to_bv 64 mo; Z_to_bv 64 (bv_unsigned buf + mo)]
      [KWord (SA (EVar 8) 144) 4 (EVar 90); KRange (EVar 90) 0 4; KWord (SA (EVar 8) 300) 4 (ELit 3);
       KWord (SA (EVar 8) 296) 4 (EVar 91);
       KRange (EVar 92) 0 4294967295; KRange (EVar 93) 1 140737488355328;
       KDisj (SA (EVar 93) 0) 48 (SA (EVar 8) 0) 400;
       KBlobD (SA (EVar 77) 0) (EVar 78) 0]
      ltac:(repeat apply Forall_cons; try apply Forall_nil;
            [ eapply (kword_intro SEGS E _ (EVar 8) A 144 4 (EVar 90) (Z_to_bv 64 ic)); [cbn [edenot]; ev_simpl E; exact A8 | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | exact (proj2 C1)]
            | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia
            | eapply (kword_intro SEGS E _ (EVar 8) A 300 4 (ELit 3%Z) (Z_to_bv 64 3)); [cbn [edenot]; ev_simpl E; exact A8 | reflexivity | lia | lia | lia | lia | exact (proj2 C2)]
            | eapply (kword_intro SEGS E _ (EVar 8) A 296 4 (EVar 91) (Z_to_bv 64 3)); [cbn [edenot]; ev_simpl E; exact A8 | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | exact (proj2 C3)]
            | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia
            | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia
            | cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl E; rewrite A8; rewrite u_small by lia;
              pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P11 & _); lia
            | cbn [kentry_ok]; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; ev_simpl E;
              rewrite u_small by lia; split; [lia|]; split; [exact Hbs|]; intros i Hi; rewrite Z.add_0_r; apply Hblob; exact Hi ]).
    pin_reg HR (10%bv:reg) (EVar 92) by (cbn [edenot]; ev_simpl E; exact H10).
    pin_reg HR (9%bv:reg) (ELit 0xff00%Z) by (cbn [edenot]; exact H5).
    run_fp 30%nat [0x152e0%Z] noscr true.
    pin_reg HR (10%bv:reg) (EVar 93) by (regv_lin HR (10%bv:reg); cbn [edenot]; ev_simpl E; rewrite (u_small mo) by lia; f_equal; lia).
    run_fp 300%nat [0x156b8%Z] (dirs [false]) true hints keep_all
      by (pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P11 & _ & _ & P14); lia).
    (* [comment removed for export] *)
    frame_now HADM [(SA (EVar 8) 248, 48%Z)] [(Z_to_bv 64 (a + 248), 48%Z)] Hfr.
    adm_fr HADM Hfr HADM1.
    lazymatch goal with |- runs_to _ (@mkst _ _ _ ?M1 _) _ => remember M1 as Mz eqn:HMz; clear HMz end.
    pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10 & P11 & P12 & _).
    pose proof pre_tagI as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof (u64_range T).
    apply (jsegI _ _ _ sz buf ic 3%Z HADM1).
    - eapply tagc_frameI; [exact HTAG | exact Hfr | solve_apart].
    - exact Hsz.
    - eapply mab_cells_frameI; [exact HMC | exact Hfr | solve_apart | solve_apart].
    - eapply curves0_frameI; [exact HC0 | exact Hfr | solve_apart |].
      unfold a2b_curve_offsets. repeat (apply Forall_cons; [solve_apart|]). apply Forall_nil.
    - eapply stk_frameI; [exact HSTK | exact Hfr | solve_apart].
    - regv HR (20%bv:reg). reflexivity.
    - regv HR (21%bv:reg). reflexivity.
    - regv HR (22%bv:reg). reflexivity.
    - regv HR (6%bv:reg). reflexivity.
    - regv HR (7%bv:reg). reflexivity.
    - regv HR (9%bv:reg). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma m2a : forall (FPI : FPState) R M sz buf ic r,
    ADM FPI R M -> TAGC 0x6d414220 sz buf M -> (32 <= sz)%Z -> mab_cellsI ic 3 M -> stkI buf M ->
    getr R 10 = Z_to_bv 64 r -> (r = 0%Z \/ (r = 1%Z /\ curves0I M)) ->
    getr R 23 = le4wI buf 16 -> getr R 9 = Z_to_bv 64 0xff00 ->
    getr R 21 = WI buf 16 -> getr R 27 = WI buf 18 -> getr R 22 = WI buf 19 -> getr R 19 = Z_to_bv 64 pcs ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x15104) M rom) QP.
  Proof.
    intros FPI R M sz buf ic r HADM HTAG Hsz HMC HSTK H10 Hr H23 H20 H22 H9 H26 H19.
    adm_facts HADM. pose proof HMC as (C1 & C2 & C3 & Hic & Hmc).
    pose proof HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c). pose proof (u64_range buf).
    pose proof pre_pcs as Hpcs.
    pose proof (bb_range data bs buf 16) as R16. pose proof (bb_range data bs buf 17) as R17.
    pose proof (bb_range data bs buf 18) as R18. pose proof (bb_range data bs buf 19) as R19.
    destruct Hr as [-> | [-> HC0]].
    - pkg_tag HADM HTAG (@nil word) (@nil kentry) ltac:(constructor).
      pin_reg HR (10%bv:reg) (ELit 0%Z) by (cbn [edenot]; exact H10).
      run_fp 10%nat [0x1525c%Z] noscr true. fail0 HADM.
    - pose proof (be4_range data bs buf 16) as Hmo.
      pkg_tag HADM HTAG [Z_to_bv 64 ic; WI buf 16; WI buf 17; WI buf 18; WI buf 19; Z_to_bv 64 (be4I buf 16); Z_to_bv 64 pcs]
        [KWord (SA (EVar 8) 144) 4 (EVar 81); KRange (EVar 81) 0 4; KWord (SA (EVar 8) 300) 4 (ELit 3);
         KWord (SA (EVar 8) 296) 4 (ELit 3);
         KRange (EVar 82) 0 255; KRange (EVar 83) 0 255; KRange (EVar 84) 0 255; KRange (EVar 85) 0 255;
         KRange (EVar 86) 0 4294967295; KRange (EVar 87) 0 1]
        ltac:(repeat apply Forall_cons; try apply Forall_nil;
              [ eapply (kword_intro SEGS E _ (EVar 8) A 144 4 (EVar 81) (Z_to_bv 64 ic)); [cbn [edenot]; ev_simpl E; exact A8 | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | exact (proj2 C1)]
              | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia
              | eapply (kword_intro SEGS E _ (EVar 8) A 300 4 (ELit 3%Z) (Z_to_bv 64 3)); [cbn [edenot]; ev_simpl E; exact A8 | reflexivity | lia | lia | lia | lia | exact (proj2 C2)]
              | eapply (kword_intro SEGS E _ (EVar 8) A 296 4 (ELit 3%Z) (Z_to_bv 64 3)); [cbn [edenot]; ev_simpl E; exact A8 | reflexivity | lia | lia | lia | lia | exact (proj2 C3)]
              | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite uW; lia
              | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite uW; lia
              | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite uW; lia
              | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite uW; lia
              | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia
              | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia ]).
      pin_reg HR (10%bv:reg) (ELit 1%Z) by (cbn [edenot]; exact H10).
      pin_reg HR (23%bv:reg) (EAlu ALU_ADD (EVar 82) (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 83))
           (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 84)) (EMd M_MUL (ELit 16777216) (EVar 85)))))
        by (cbn [edenot]; ev_simpl E; rewrite H23; reflexivity).
      pin_reg HR (9%bv:reg) (ELit 0xff00%Z) by (cbn [edenot]; exact H20).
      pin_reg HR (21%bv:reg) (EVar 82) by (cbn [edenot]; ev_simpl E; exact H22).
      pin_reg HR (27%bv:reg) (EVar 84) by (cbn [edenot]; ev_simpl E; exact H9).
      pin_reg HR (22%bv:reg) (EVar 85) by (cbn [edenot]; ev_simpl E; exact H26).
      pin_reg HR (19%bv:reg) (EVar 87) by (cbn [edenot]; ev_simpl E; exact H19).
      run_fp 30%nat [0x1525c%Z; 0x15130%Z] noscr true.
      (* [comment removed for export] *)
      assert (Hbe : be4I buf 16 = (bbI buf 19 + 256 * bbI buf 18 + 65536 * bbI buf 17 + 16777216 * bbI buf 16)%Z) by reflexivity.
      set (nu := fun k : nat => nth k [bbI buf 16; bbI buf 17; bbI buf 18; bbI buf 19] 0%Z).
      assert (nu_range : forall k, (0 <= nu k < 256)%Z).
      { intros k. unfold nu. destruct k as [|[|[|[|k]]]]; cbn [nth]; try lia. destruct k; cbn; lia. }
      set (atoms := [(EVar 82, (false, 0%nat)); (EVar 83, (false, 1%nat)); (EVar 84, (false, 2%nat)); (EVar 85, (false, 3%nat))]).
      assert (Hat : atoms_ok E nu atoms).
      { unfold atoms, atoms_ok. repeat apply Forall_cons; try apply Forall_nil;
          unfold atom_ok; cbn [edenot]; ev_simpl E; rewrite uW; reflexivity. }
      pin_reg HR (10%bv:reg) (EVar 86) by
        (rewrite (HR (10%bv:reg));
         lazymatch goal with |- edenot _ ?e = _ =>
           apply bv_eq; rewrite (beval_bytes E nu nu_range atoms e [3; 2; 1; 0]%nat Hat ltac:(cbn; lia) ltac:(vm_compute; reflexivity))
         end;
         cbn [edenot]; ev_simpl E; rewrite u_small by lia; rewrite Hbe; unfold nu; cbn [bytes_val nth]; lia).
      run_fp 20%nat [0x1525c%Z; 0x152c4%Z] noscr true.
      branch_case as Hmo48; [fail0 HADM|].
      hc_lin Hmo48.
      run_fp 20%nat [0x1525c%Z; 0x152c4%Z] noscr true.
      (* [comment removed for export] *)
      branch_case as Hpc.
      + run_fp 20%nat [0x1525c%Z; 0x152c4%Z] noscr true.
        adm_now HADM HADM1.
        apply (m2b _ _ _ sz buf ic (be4I buf 16) HADM1 HTAG Hsz HMC HC0 HSTK Hmo ltac:(lia));
          [regv HR (10%bv:reg); reflexivity | regv HR (9%bv:reg); reflexivity].
      + run_fp 20%nat [0x1525c%Z; 0x152c4%Z] noscr true.
        adm_now HADM HADM1.
        apply (m2b _ _ _ sz buf ic (be4I buf 16) HADM1 HTAG Hsz HMC HC0 HSTK Hmo ltac:(lia));
          [regv HR (10%bv:reg); reflexivity | regv HR (9%bv:reg); reflexivity].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma m1 : forall (FPI : FPState) R M sz buf ic r,
    ADM FPI R M -> TAGC 0x6d414220 sz buf M -> (32 <= sz)%Z ->
    cell32 SEGS M (a + 144) ic -> (0 <= ic <= 4)%Z -> cell32 SEGS M (a + 300) 3 -> stkI buf M ->
    getr R 10 = Z_to_bv 64 r -> (r = 0%Z \/ (r = 1%Z /\ curves0I M)) ->
    getr R 27 = WI buf 18 -> getr R 20 = WI buf 23 -> getr R 21 = WI buf 16 -> getr R 23 = WI buf 21 ->
    getr R 24 = WI buf 20 -> getr R 25 = WI buf 22 -> getr R 26 = WI buf 17 -> getr R 22 = WI buf 19 ->
    getr R 9 = Z_to_bv 64 0xff00 -> getr R 19 = Z_to_bv 64 pcs ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x15094) M rom) QP.
  Proof.
    intros FPI R M sz buf ic r HADM HTAG Hsz C1 Hic C2 HSTK H10 Hr H9 H20 H22 H23 H24 H25 H26 H27 H21 H19.
    adm_facts HADM.
    pose proof HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c). pose proof (u64_range buf).
    pose proof pre_pcs as Hpcs.
    pose proof (bb_range data bs buf 16) as R16. pose proof (bb_range data bs buf 17) as R17.
    pose proof (bb_range data bs buf 18) as R18. pose proof (bb_range data bs buf 19) as R19.
    pose proof (bb_range data bs buf 20) as R20. pose proof (bb_range data bs buf 21) as R21.
    pose proof (bb_range data bs buf 22) as R22. pose proof (bb_range data bs buf 23) as R23.
    destruct Hr as [-> | [-> HC0]].
    - pkg_tag HADM HTAG (@nil word) (@nil kentry) ltac:(constructor).
      pin_reg HR (10%bv:reg) (ELit 0%Z) by (cbn [edenot]; exact H10).
      run_fp 10%nat [0x1525c%Z] noscr true. fail0 HADM.
    - pkg_stk HADM HTAG HSTK [Z_to_bv 64 ic; WI buf 16; WI buf 17; WI buf 18; WI buf 19; WI buf 20; WI buf 21; WI buf 22; WI buf 23; Z_to_bv 64 pcs]
        [KWord (SA (EVar 8) 144) 4 (EVar 90); KRange (EVar 90) 0 4; KWord (SA (EVar 8) 300) 4 (ELit 3);
         KRange (EVar 91) 0 255; KRange (EVar 92) 0 255; KRange (EVar 93) 0 255; KRange (EVar 94) 0 255;
         KRange (EVar 95) 0 255; KRange (EVar 96) 0 255; KRange (EVar 97) 0 255; KRange (EVar 98) 0 255;
         KRange (EVar 99) 0 1]
        ltac:(repeat apply Forall_cons; try apply Forall_nil;
              [ eapply (kword_intro SEGS E _ (EVar 8) A 144 4 (EVar 90) (Z_to_bv 64 ic)); [cbn [edenot]; ev_simpl E; exact A8 | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | exact (proj2 C1)]
              | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia
              | eapply (kword_intro SEGS E _ (EVar 8) A 300 4 (ELit 3%Z) (Z_to_bv 64 3)); [cbn [edenot]; ev_simpl E; exact A8 | reflexivity | lia | lia | lia | lia | exact (proj2 C2)]
              | .. ];
              apply krange_intro; cbn [edenot]; ev_simpl E; rewrite ?uW; try lia; rewrite u_small by lia; lia).
      pin_reg HR (10%bv:reg) (ELit 1%Z) by (cbn [edenot]; exact H10).
      pin_reg HR (27%bv:reg) (EVar 93) by (cbn [edenot]; ev_simpl E; exact H9).
      pin_reg HR (20%bv:reg) (EVar 98) by (cbn [edenot]; ev_simpl E; exact H20).
      pin_reg HR (21%bv:reg) (EVar 91) by (cbn [edenot]; ev_simpl E; exact H22).
      pin_reg HR (23%bv:reg) (EVar 96) by (cbn [edenot]; ev_simpl E; exact H23).
      pin_reg HR (24%bv:reg) (EVar 95) by (cbn [edenot]; ev_simpl E; exact H24).
      pin_reg HR (25%bv:reg) (EVar 97) by (cbn [edenot]; ev_simpl E; exact H25).
      pin_reg HR (26%bv:reg) (EVar 92) by (cbn [edenot]; ev_simpl E; exact H26).
      pin_reg HR (22%bv:reg) (EVar 94) by (cbn [edenot]; ev_simpl E; exact H27).
      pin_reg HR (9%bv:reg) (ELit 0xff00%Z) by (cbn [edenot]; exact H21).
      pin_reg HR (19%bv:reg) (EVar 99) by (cbn [edenot]; ev_simpl E; exact H19).
      run_fp 40%nat [0x1525c%Z; 0x16914%Z; 0x156b8%Z] noscr true.
      branch_case as Hm0.
      + (* [comment removed for export] *)
        branch_case as Hmx0.
        * run_fp 20%nat [0x1525c%Z; 0x16914%Z; 0x156b8%Z] noscr true.
          frame_now HADM [(SA (EVar 8) 296, 4%Z)] [(Z_to_bv 64 (a + 296), 4%Z)] Hfr.
          adm_fr HADM Hfr HADM1.
          lazymatch goal with |- runs_to _ (@mkst _ _ _ ?M1 _) _ => remember M1 as Mz eqn:HMz; clear HMz end.
          pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10 & P11 & P12 & _).
          pose proof pre_tagI as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof (u64_range T).
          kcellv (EVar 8) 144%Z 4%nat C144. kcellv (EVar 8) 296%Z 4%nat C296. kcellv (EVar 8) 300%Z 4%nat C300.
          apply (jsegI _ _ _ sz buf ic 0%Z HADM1).
          -- eapply tagc_frameI; [exact HTAG | exact Hfr | solve_apart].
          -- exact Hsz.
          -- split; [split; [lia|exact C144]|]. split; [split; [lia|exact C300]|]. split; [split; [lia|exact C296]|].
             split; [exact Hic | left; reflexivity].
          -- eapply curves0_frameI; [exact HC0 | exact Hfr | solve_apart |].
             unfold a2b_curve_offsets. repeat (apply Forall_cons; [solve_apart|]). apply Forall_nil.
          -- eapply stk_frameI; [exact HSTK | exact Hfr | solve_apart].
          -- regv HR (20%bv:reg). reflexivity.
          -- regv HR (21%bv:reg). reflexivity.
          -- regv HR (22%bv:reg). reflexivity.
          -- regv HR (6%bv:reg). reflexivity.
          -- regv HR (7%bv:reg). reflexivity.
          -- regv HR (9%bv:reg). reflexivity.
        * fail0 HADM.
      + branch_case as Hmx0; [fail0 HADM|].
        run_fp 40%nat [0x1525c%Z; 0x16914%Z; 0x156b8%Z] noscr true.
        (* [comment removed for export] *)
        frame_now HADM [(SA (EVar 8) 296, 4%Z)] [(Z_to_bv 64 (a + 296), 4%Z)] Hfr.
        adm_fr HADM Hfr HADM1.
        lazymatch goal with |- runs_to _ (@mkst _ _ _ ?M1 _) _ => remember M1 as Mz eqn:HMz in *; clear HMz end.
        pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10 & P11 & P12 & _).
        pose proof pre_tagI as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof (u64_range T).
        lazymatch goal with |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
          assert (HTAG1 : TAGC 0x6d414220 sz buf M1) by (eapply tagc_frameI; [exact HTAG | exact Hfr | solve_apart]);
          assert (HC01 : curves0I M1) by
            (eapply curves0_frameI; [exact HC0 | exact Hfr | solve_apart |];
             unfold a2b_curve_offsets; repeat (apply Forall_cons; [solve_apart|]); apply Forall_nil);
          assert (HSTK1 : stkI buf M1) by (eapply stk_frameI; [exact HSTK | exact Hfr | solve_apart])
        end.
        kcellv (EVar 8) 144%Z 4%nat C144. kcellv (EVar 8) 296%Z 4%nat C296. kcellv (EVar 8) 300%Z 4%nat C300.
        eapply rt_call.
        { eapply (Hrc data len bs (Z_to_bv 64 (spv - 176)) buf (Z_to_bv 64 (a + 152)) sz _ 3%Z _ _ _ rom (Z_to_bv 64 0x15104)).
          - regv HR (1%bv:reg). reflexivity.
          - apply ret_ok_even. rewrite u_small by lia. reflexivity.
          - eapply (rc_pre_atI _ _ _ 0x6d414220%Z sz buf (a + 152)%Z 3%Z);
              [ exact HADM1 | exact HTAG1 | lia | lia | lia | apply mod8_add; [exact P2 | reflexivity]
              | regv HR (10%bv:reg); reflexivity
              | regv HR (11%bv:reg); reflexivity
              | reflexivity
              | regv HR (13%bv:reg); reflexivity
              | regv_lin HR (14%bv:reg); rewrite A8; f_equal; lia ]. }
        cbv beta. intros FPI' R' M' (Hkeep & Hfkeep & Hpost).
        unfold rcurves_post in Hpost. cbv zeta in Hpost. change (w_rcurves_d wp2_infoub) with 128%Z in Hpost.
        rewrite (u_small (spv - 176)), (u_small (a + 152)) in Hpost by lia.
        destruct Hpost as (Hfr2 & r2 & H10' & Hr01 & Hcv).
        destruct (adm_rcI _ FPI' _ R' _ M' (a + 152)%Z 3%Z HADM1 ltac:(lia) ltac:(lia) ltac:(lia) Hfr2 Hkeep Hfkeep) as (HADM' & HT' & HS').
        apply (m2a FPI' R' M' sz buf ic r2 HADM' (HT' _ _ _ HTAG1) Hsz).
        * split; [eapply cell32_frame; [exact Hfr2 | split; [lia|exact C144] | lia | lia | solve_apart]|].
          split; [eapply cell32_frame; [exact Hfr2 | split; [lia|exact C300] | lia | lia | solve_apart]|].
          split; [eapply cell32_frame; [exact Hfr2 | split; [lia|exact C296] | lia | lia | solve_apart]|].
          split; [exact Hic | right; reflexivity].
        * apply HS'. exact HSTK1.
        * exact H10'.
        * destruct Hr01 as [-> | ->]; [left; reflexivity | right; split; [reflexivity|]].
          eapply (curves0_rcI _ M' 152%Z 3%Z HC01 Hfr2); [lia | lia | lia | |].
          -- intros i Hi. apply Hcv; [reflexivity | exact Hi].
          -- intros o Hin. offsets_cases Hin;
               first [ left; lia | right; exists 0%Z; lia | right; exists 1%Z; lia | right; exists 2%Z; lia ].
        * rewrite (Hkeep 23%bv ltac:(in_kept)). regv HR (23%bv:reg). reflexivity.
        * rewrite (Hkeep 9%bv ltac:(in_kept)). regv HR (9%bv:reg). reflexivity.
        * rewrite (Hkeep 21%bv ltac:(in_kept)). regv HR (21%bv:reg). reflexivity.
        * rewrite (Hkeep 27%bv ltac:(in_kept)). regv HR (27%bv:reg). reflexivity.
        * rewrite (Hkeep 22%bv ltac:(in_kept)). regv HR (22%bv:reg). reflexivity.
        * rewrite (Hkeep 19%bv ltac:(in_kept)). regv HR (19%bv:reg). reflexivity.
  Qed.
End RF.
End LibReadA2BUbf.

Module LibReadA2BUbg.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Lib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibRodata OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibBswap.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfKc.
Import LibReadA2BUba LibReadA2BUbb LibReadA2BUbc LibReadA2BUbd LibReadA2BUbe LibReadA2BUbf.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
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
(* [comment removed for export] *)
Local Ltac ev_simpl E ::=   (* [comment removed for export] *)
  lazymatch goal with |- ?G =>
    let G1 := match tt with | _ => eval unfold E in G | _ => G end in
    let G2 := eval lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in G1 in
    change G2
  end.
Local Ltac ev_simpl_in E H ::= try unfold E in H; lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in H.
#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section RG.
  Variables (FPI0 : FPState) (regs0 : bvmap 5 word) (mem0 rom : word -> option byte) (ret : word).
  Variables (data : word) (len : Z) (bs : list byte) (sp T A : word) (pcs : Z).
  Hypothesis Hra : getr regs0 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HPRE : a2b_pre SEGS wp2_infoub data len bs sp T A pcs FPI0 regs0 mem0.
  Hypothesis Hcanon : canonicalize_contract SEGS wp3_infoub.
  Hypothesis Hrc : read_curves_contract SEGS wp2_infoub.

  #[local] Abbreviation a := (bv_unsigned A).
  #[local] Abbreviation spv := (bv_unsigned sp).
  #[local] Abbreviation t := (bv_unsigned T).
  #[local] Abbreviation ADM := (adm FPI0 regs0 mem0 ret data len bs sp T A).
  #[local] Abbreviation QP := (Qpost FPI0 regs0 mem0 rom ret data len bs sp T A pcs).
  #[local] Abbreviation CI := (chain_inv data len A).
  #[local] Abbreviation TAGC := (tagc data len T).
  #[local] Abbreviation pre_factsI := (pre_facts FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation pre_tagI := (pre_tag FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation pre_spI := (pre_sp FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation kn_adm_okI := (kn_adm_ok FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation kn_tag_okI := (kn_tag_ok FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation adm_frameI := (adm_frame FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation base_valsI := (base_vals regs0 ret data len).
  #[local] Abbreviation failkI := (failk FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE).
  #[local] Abbreviation in1I := (in1 FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).
  #[local] Abbreviation eobw := (Z_to_bv 64 (bv_unsigned data + len)).
  #[local] Abbreviation bbI := (bb data bs).
  #[local] Abbreviation WI := (W data bs).
  #[local] Abbreviation curves10I := (curves10 data len A).
  #[local] Abbreviation mab_cellsI := (mab_cells A).
  #[local] Abbreviation gslI := (gsl data bs).
  #[local] Abbreviation PvalI := (Pval data bs).
  #[local] Abbreviation be4I := (be4 data bs).
  #[local] Abbreviation le4wI := (le4w data bs).
  #[local] Abbreviation vals_m3I := (vals_m3 data len bs).
  #[local] Abbreviation curves10_frame1I := (curves10_frame1 FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation kn_m3_okI := (kn_m3_ok FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation curves0I := (curves0 data len A).
  #[local] Abbreviation curves0_frameI := (curves0_frame FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation tagc_frameI := (tagc_frame FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation in0I := (in0 FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).
  #[local] Abbreviation m3aI := (m3a FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).
  #[local] Abbreviation stkI := (stk data len bs sp).
  #[local] Abbreviation kn_stk_okI := (kn_stk_ok FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation stk_frameI := (stk_frame FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation mab_cells_frameI := (mab_cells_frame FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation rc_pre_atI := (rc_pre_at FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation adm_rcI := (adm_rc FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation curves0_rcI := (curves0_rc FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation jsegI := (jseg FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon Hrc).
  #[local] Abbreviation m1I := (m1 FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon Hrc).
  #[local] Abbreviation failk'I := (failk' FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE).

  (* [comment removed for export] *)
  Ltac adm_facts HADM :=
    pose proof HADM as (A2 & A3 & A4 & A8 & A18 & AF & AS & AFR & AD & ARO & AWA & AWS);
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _);
    assert (U2 : bv_unsigned (getr _ 2) = (spv - 176)%Z) by (rewrite A2, u_small by lia; lia).

  Ltac pkg HADM extra kx ktac :=
    lazymatch goal with
    | |- runs_to _ (@mkst ?FPI ?R _ ?M _) _ =>
      set (E := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++
         [ret; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20; getr regs0 21;
          getr regs0 22; getr regs0 23; getr regs0 24; getr regs0 25; getr regs0 26; getr regs0 27;
          data; Z_to_bv 64 len] ++ extra)) (blobs_ev [bs]));
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs]));
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs]));
      pose proof (HR : id _) as HR0; pose proof (HF : id _) as HF0;
      let HK1 := fresh "HK1" in let HK2 := fresh "HK2" in
      pose proof (kn_adm_okI FPI R M extra HADM) as HK1; change (know_ok SEGS E M kn_adm) in HK1;
      assert (HK2 : know_ok SEGS E M kx); [ktac|];
      pose proof (know_ok_app SEGS E M kn_adm kx HK1 HK2) as HK; clear HK1 HK2;
      cbv beta delta [kn_adm app] in HK
    end.

  Ltac pkg_tag HADM HTAG rest kx ktac :=
    lazymatch type of HTAG with tagc _ _ _ ?ty ?sz ?buf _ =>
      pkg HADM ([Z_to_bv 64 sz; buf] ++ rest) (kn_tag ty ++ kx)
        ltac:(apply know_ok_app; [exact (kn_tag_okI _ _ _ ty sz buf rest HADM HTAG) | ktac])
    end.

  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.

  Ltac subst_mems :=
    repeat match goal with H : @eq (word -> option byte) ?x _ |- _ => is_var x; subst x end.

  Ltac adm_now HADM HADM1 :=
    subst_mems;
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1, HF : fregs_ok _ ?sfr (@fp_regs ?I1), HF0 : id (fregs_ok _ ?sfr0 (@fp_regs ?I0))
      |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ ?R ?M0 =>
        assert (HADM1 : ADM I1 R1 M1);
        [ apply (adm_frameI I0 I1 R R1 M0 M1 [] HADM);
          [ apply frame_mod_refl
          | apply Forall_nil
          | apply Forall_nil
          | regv HR (2%bv:reg); reflexivity
          | regv HR (3%bv:reg); reflexivity
          | regv HR (4%bv:reg); reflexivity
          | regv HR (8%bv:reg); reflexivity
          | regv HR (18%bv:reg); reflexivity
          | exact (fregs_same_on E sfr0 sfr _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)) ]
        | ]
      end
    end.
  (* [comment removed for export] *)


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac mods_in H :=
    repeat match type of H with context [ (?x mod ?m)%Z ] =>
      lazymatch x with context [ (_ mod _)%Z ] => fail | _ => rewrite (Z.mod_small x m) in H by lia end end.
  Ltac mods_goal :=
    repeat match goal with |- context [ (?x mod ?m)%Z ] =>
      lazymatch x with context [ (_ mod _)%Z ] => fail | _ => rewrite (Z.mod_small x m) by lia end end.

  (* [comment removed for export] *)
  Ltac zbool H :=
    first [ apply Z.ltb_lt in H | apply Z.ltb_ge in H | apply Z.eqb_eq in H | apply Z.eqb_neq in H ].
  Ltac hc_lin Hc :=
    revert Hc; rewrite ?branch_taken_Z; cbv beta iota; linearize;
    cbn [edenot fop1_denot fop2_denot fop3_denot];
    lazymatch goal with HK : know_ok _ ?E _ _ |- _ => ev_simpl E end;
    rewrite ?uW, ?Z_to_bv_unsigned, ?bv_wrap64_mod; intros Hc;
    try (apply (f_equal negb) in Hc; rewrite negb_involutive in Hc; cbn [negb] in Hc);
    mods_in Hc; zbool Hc.

  Ltac regions_eq :=
    cbn [regions_denot map fst snd]; unfold adenot, v_addi; cbn [a_base a_off edenot];
    lazymatch goal with HK : know_ok _ ?E _ _ |- _ => ev_simpl E end; rewrite_getr; rewrite ?u_small_frame by lia;
    repeat (apply f_equal2; [apply f_equal2; [apply f_equal; lia | lia] | ]); reflexivity.

  (* [comment removed for export] *)
  Ltac frame_logs RS :=
    lazymatch goal with
    | |- frame_mod ?m0 ?m0 _ => apply frame_mod_refl
    | HK : know_ok _ ?E _ _ |- frame_mod ?m0 (mem_denot _ ?m1 ?log) _ =>
        apply (frame_mod_trans_same m0 m1);
        [ frame_logs RS
        | apply (frame_mod_mem_denot E m1 log RS);
          [ lazymatch goal with H : log_flat _ log |- _ => exact H end
          | repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; unfold flat, estart;
            cbn [a_base a_off edenot]; ev_simpl E; rewrite_getr; rewrite ?u_small_frame by lia; lia
          | vm_compute; reflexivity ] ]
    end.

  (* [comment removed for export] *)
  Ltac frame_now HADM RS rsZ Hfr :=
    subst_mems;
    lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ _ ?M0 =>
    lazymatch goal with HK : know_ok _ ?E ?M1 _ |- _ =>
      assert (Hfr : frame_mod M0 M1 rsZ);
      [ replace rsZ with (regions_denot E RS) by regions_eq; frame_logs RS | ]
    end end.

  (* [comment removed for export] *)
  Ltac adm_fr HADM Hfr HADM1 :=
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1, HF : fregs_ok _ ?sfr (@fp_regs ?I1), HF0 : id (fregs_ok _ ?sfr0 (@fp_regs ?I0))
      |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ ?R ?M0 =>
        assert (HADM1 : ADM I1 R1 M1);
        [ apply (adm_frameI I0 I1 R R1 M0 M1 _ HADM Hfr);
          [ solve [unfold BIG; solve_within]
          | solve [pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ? & _); solve_apart]
          | regv HR (2%bv:reg); reflexivity
          | regv HR (3%bv:reg); reflexivity
          | regv HR (4%bv:reg); reflexivity
          | regv HR (8%bv:reg); reflexivity
          | regv HR (18%bv:reg); reflexivity
          | exact (fregs_same_on E sfr0 sfr _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)) ]
        | ]
      end
    end.

  (* [comment removed for export] *)
  Ltac w_lt :=
    rewrite ?uW;
    lazymatch goal with
    | |- (bb _ _ ?b ?i < _)%Z => pose proof (bb_range data bs b i); lia
    | |- _ => rewrite ?u_small by lia; lia
    end.

  (* [comment removed for export] *)
  Ltac flat_tac := unfold flat, estart; cbn [a_base a_off edenot];
    lazymatch goal with HK : know_ok _ ?E _ _ |- _ => ev_simpl E end; rewrite_getr; rewrite ?u_small_frame by lia; lia.
  Ltac kcellv b k n H :=
    lazymatch goal with HK : know_ok _ ?E ?M ?kn |- _ =>
      let r := eval vm_compute in (kread SEGS kn b k n) in
      lazymatch r with
      | Some ?v =>
        let KR := fresh "KR" in let Hfl := fresh "Hfl" in
        kread_rdn_fast SEGS E M kn b k n v HK H;
        lazymatch type of H with ?FL -> _ => assert (Hfl : FL) by flat_tac; specialize (H Hfl); clear Hfl end;
        unfold adenot, v_addi in H; cbn [a_base a_off edenot] in H; ev_simpl_in E H; rewrite_getr_in H;
        rewrite ?u_small_frame in H by lia;
        rewrite ?ext_val_zx_id4 in H by w_lt;
        rewrite ?ext_val_zx_id1 in H by w_lt
      | _ => fail "kcellv: no knowledge at" b k n
      end
    end.


  (* [comment removed for export] *)
  Ltac fail_st HADM RS rsZ :=
    let Hfr := fresh "Hfr" in let HADM1 := fresh "HADMf" in
    frame_now HADM RS rsZ Hfr; adm_fr HADM Hfr HADM1;
    match goal with H : adm _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => apply (failkI _ _ _ H) end.
  (* [comment removed for export] *)
  Ltac in_kept := cbn; repeat (first [ left; reflexivity | right ]).

  (* [comment removed for export] *)
  Ltac fail0 HADM :=
    let HADM1 := fresh "HADMf" in adm_now HADM HADM1;
    match goal with H : adm _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => apply (failkI _ _ _ H) end.


  Ltac pkg_stk HADM HTAG HSTK rest kx ktac :=
    lazymatch type of HTAG with tagc _ _ _ ?ty ?sz ?buf _ =>
      pkg HADM ([Z_to_bv 64 sz; buf] ++ [WI buf 24; WI buf 25; WI buf 26; WI buf 27; WI buf 28; WI buf 29; WI buf 30; WI buf 31; eobw] ++ rest) (kn_tag ty ++ kn_stk ++ kx)
        ltac:(apply know_ok_app; [exact (kn_tag_okI _ _ _ ty sz buf _ HADM HTAG)
             | apply know_ok_app; [exact (kn_stk_okI _ _ _ sz buf rest HADM HSTK) | ktac]]);
      lazymatch goal with HK : know_ok _ _ _ ?kn |- _ =>
        let kn' := eval vm_compute in kn in change kn with kn' in HK end;
      match goal with Edef := Env _ _ |- _ => cbn [app] in Edef end
    end.

  Ltac offsets_cases Hin :=
    cbn [a2b_curve_offsets In] in Hin;
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]].


  (* [comment removed for export] *)
  Ltac fail_st' HADM RS rsZ :=
    let Hfr := fresh "Hfr" in let HADM1 := fresh "HADMf" in
    frame_now HADM RS rsZ Hfr; adm_fr HADM Hfr HADM1;
    match goal with H : adm _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      apply (failk'I _ _ _ H); lazymatch goal with HR : regs_ok _ _ _ |- _ => regv HR (20%bv:reg); reflexivity end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition kn_m0 : list kentry :=
    [KWord (SA (EVar 80) 8) 1 (EVar 81);
     KWord (SA (EVar 80) 9) 1 (EVar 82);
     KWord (SA (EVar 80) 12) 1 (EVar 83);
     KWord (SA (EVar 80) 13) 1 (EVar 84);
     KWord (SA (EVar 80) 14) 1 (EVar 85);
     KWord (SA (EVar 80) 15) 1 (EVar 86);
     KWord (SA (EVar 80) 16) 1 (EVar 87);
     KWord (SA (EVar 80) 17) 1 (EVar 88);
     KWord (SA (EVar 80) 18) 1 (EVar 89);
     KWord (SA (EVar 80) 19) 1 (EVar 90);
     KWord (SA (EVar 80) 20) 1 (EVar 91);
     KWord (SA (EVar 80) 21) 1 (EVar 92);
     KWord (SA (EVar 80) 22) 1 (EVar 93);
     KWord (SA (EVar 80) 23) 1 (EVar 94);
     KWord (SA (EVar 80) 24) 1 (EVar 95);
     KWord (SA (EVar 80) 25) 1 (EVar 96);
     KWord (SA (EVar 80) 26) 1 (EVar 97);
     KWord (SA (EVar 80) 27) 1 (EVar 98);
     KWord (SA (EVar 80) 28) 1 (EVar 99);
     KWord (SA (EVar 80) 29) 1 (EVar 100);
     KWord (SA (EVar 80) 30) 1 (EVar 101);
     KWord (SA (EVar 80) 31) 1 (EVar 102);
     KRange (EVar 81) 0 255; KRange (EVar 82) 0 255; KRange (EVar 83) 0 255; KRange (EVar 84) 0 255; KRange (EVar 85) 0 255; KRange (EVar 86) 0 255; KRange (EVar 87) 0 255; KRange (EVar 88) 0 255; KRange (EVar 89) 0 255; KRange (EVar 90) 0 255; KRange (EVar 91) 0 255; KRange (EVar 92) 0 255; KRange (EVar 93) 0 255; KRange (EVar 94) 0 255; KRange (EVar 95) 0 255; KRange (EVar 96) 0 255; KRange (EVar 97) 0 255; KRange (EVar 98) 0 255; KRange (EVar 99) 0 255; KRange (EVar 100) 0 255; KRange (EVar 101) 0 255; KRange (EVar 102) 0 255;
     KDisj (SA (EVar 80) 0) 32 (SA (EVar 8) 0) 400; KDisj (SA (EVar 80) 0) 32 (SA (EVar 2) (-160)) 336].
  Definition vals_m0 (buf : word) : list word := [WI buf 8; WI buf 9; WI buf 12; WI buf 13; WI buf 14; WI buf 15; WI buf 16; WI buf 17; WI buf 18; WI buf 19; WI buf 20; WI buf 21; WI buf 22; WI buf 23; WI buf 24; WI buf 25; WI buf 26; WI buf 27; WI buf 28; WI buf 29; WI buf 30; WI buf 31].

  Lemma kn_m0_ok : forall (FPI : FPState) R M sz buf,
    ADM FPI R M -> TAGC 0x6d414220 sz buf M -> (32 <= sz)%Z ->
    know_ok SEGS (Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ base_valsI ++
                                  ([Z_to_bv 64 sz; buf] ++ vals_m0 buf))) (blobs_ev [bs])) M kn_m0.
  Proof.
    intros FPI R M sz buf HADM HTAG Hsz. adm_facts HADM.
    pose proof HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c). pose proof (u64_range buf).
    pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P11 & P12 & _).
    set (E := Env _ _). unfold base_vals, vals_m0, W in E. unfold kn_m0.
    repeat apply Forall_cons; try apply Forall_nil.
    - eapply (kword_intro SEGS E _ (EVar 80) buf 8 1 (EVar 81)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 80) buf 9 1 (EVar 82)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 80) buf 12 1 (EVar 83)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 80) buf 13 1 (EVar 84)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 80) buf 14 1 (EVar 85)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 80) buf 15 1 (EVar 86)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 80) buf 16 1 (EVar 87)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 80) buf 17 1 (EVar 88)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 80) buf 18 1 (EVar 89)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 80) buf 19 1 (EVar 90)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 80) buf 20 1 (EVar 91)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 80) buf 21 1 (EVar 92)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 80) buf 22 1 (EVar 93)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 80) buf 23 1 (EVar 94)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 80) buf 24 1 (EVar 95)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 80) buf 25 1 (EVar 96)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 80) buf 26 1 (EVar 97)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 80) buf 27 1 (EVar 98)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 80) buf 28 1 (EVar 99)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 80) buf 29 1 (EVar 100)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 80) buf 30 1 (EVar 101)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - eapply (kword_intro SEGS E _ (EVar 80) buf 31 1 (EVar 102)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply (data_byte data len bs); [exact AD|lia|lia]].
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 8); rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 9); rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 12); rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 13); rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 14); rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 15); rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 16); rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 17); rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 18); rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 19); rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 20); rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 21); rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 22); rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 23); rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 24); rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 25); rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 26); rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 27); rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 28); rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 29); rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 30); rewrite u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; pose proof (bb_range data bs buf 31); rewrite u_small by lia; lia.
    - cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl E; rewrite A8; lia.
    - cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl E; rewrite U2; lia.
  Qed.

  Ltac pkg_m0 HADM HTAG Hsz :=
    lazymatch type of HTAG with tagc _ _ _ ?ty ?sz ?buf _ =>
      pkg HADM ([Z_to_bv 64 sz; buf] ++ vals_m0 buf) (kn_tag ty ++ kn_m0)
        ltac:(apply know_ok_app; [exact (kn_tag_okI _ _ _ ty sz buf _ HADM HTAG) | exact (kn_m0_ok _ _ _ sz buf HADM HTAG Hsz)]);
      lazymatch goal with HK : know_ok _ _ _ ?kn |- _ =>
        let kn' := eval vm_compute in kn in change kn with kn' in HK end;
      match goal with Edef := Env _ _ |- _ => cbv beta delta [vals_m0 app] in Edef end
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma m0b : forall (FPI : FPState) R M sz buf,
    ADM FPI R M -> TAGC 0x6d414220 sz buf M -> (32 <= sz)%Z -> curves0I M ->
    getr R 11 = Z_to_bv 64 sz -> getr R 9 = eobw -> getr R 19 = Z_to_bv 64 pcs ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x14f98) M rom) QP.
  Proof.
    intros FPI R M sz buf HADM HTAG Hsz HC0 H11 H9 H19.
    adm_facts HADM.
    pose proof HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c). pose proof (u64_range buf).
    pose proof (bb_range data bs buf 8) as R8. pose proof (bb_range data bs buf 9) as R9.
    pkg_m0 HADM HTAG Hsz.
    pin_reg HR (11%bv:reg) (EVar 79) by (cbn [edenot]; ev_simpl E; exact H11).
    run_fp 30%nat [0x1525c%Z; 0x15260%Z; 0x16914%Z] noscr true.
    (* [comment removed for export] *)
    branch_case as Hoc.
    { fail_st' HADM [(SA (EVar 8) 144, 4%Z); (SA (EVar 8) 300, 4%Z)] [(Z_to_bv 64 (a + 144), 4%Z); (Z_to_bv 64 (a + 300), 4%Z)]. }
    hc_lin Hoc.
    run_fp 30%nat [0x1525c%Z; 0x15260%Z; 0x16914%Z] noscr true.
    (* [comment removed for export] *)
    branch_case as Hic.
    { fail_st' HADM [(SA (EVar 8) 144, 4%Z); (SA (EVar 8) 300, 4%Z)] [(Z_to_bv 64 (a + 144), 4%Z); (Z_to_bv 64 (a + 300), 4%Z)]. }
    hc_lin Hic.
    run_fp 30%nat [0x1525c%Z; 0x15260%Z; 0x16914%Z] noscr true.
    (* [comment removed for export] *)
    branch_case as Hb0.
    { fail_st HADM [(SA (EVar 8) 144, 4%Z); (SA (EVar 8) 300, 4%Z)] [(Z_to_bv 64 (a + 144), 4%Z); (Z_to_bv 64 (a + 300), 4%Z)]. }
    run_fp 60%nat [0x1525c%Z; 0x15260%Z; 0x16914%Z] noscr true.
    (* [comment removed for export] *)
    frame_now HADM [(SA (EVar 8) 144, 4%Z); (SA (EVar 8) 300, 4%Z); (SA (EVar 2) 0, 72%Z)]
                   [(Z_to_bv 64 (a + 144), 4%Z); (Z_to_bv 64 (a + 300), 4%Z); (Z_to_bv 64 (spv - 176), 72%Z)] Hfr.
    adm_fr HADM Hfr HADM1.
    lazymatch goal with |- runs_to _ (@mkst _ _ _ ?M1 _) _ => remember M1 as Mz eqn:HMz in *; clear HMz end.
    pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10 & P11 & P12 & _).
    pose proof pre_tagI as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof (u64_range T).
    assert (HTAG1 : TAGC 0x6d414220 sz buf Mz) by (eapply tagc_frameI; [exact HTAG | exact Hfr | solve_apart]).
    assert (HC01 : curves0I Mz).
    { eapply curves0_frameI; [exact HC0 | exact Hfr | solve_apart |].
      unfold a2b_curve_offsets; repeat (apply Forall_cons; [solve_apart|]); apply Forall_nil. }
    kcellv (EVar 8) 144%Z 4%nat C144. kcellv (EVar 8) 300%Z 4%nat C300.
    kcellv (EVar 2) 64%Z 8%nat S64. kcellv (EVar 2) 16%Z 8%nat S16. kcellv (EVar 2) 48%Z 8%nat S48.
    kcellv (EVar 2) 56%Z 8%nat S56. kcellv (EVar 2) 40%Z 8%nat S40. kcellv (EVar 2) 8%Z 8%nat S8.
    kcellv (EVar 2) 32%Z 8%nat S32. kcellv (EVar 2) 24%Z 8%nat S24. kcellv (EVar 2) 0%Z 8%nat S0.
    assert (HSTK1 : stkI buf Mz).
    { unfold stk.
      repeat match goal with |- _ /\ _ => split end; unfold cell64, cell;
      first [ exact S64 | exact S56 | exact S48 | exact S40 | exact S32 | exact S24 | exact S16 | exact S8 | exact S0 ]. }
    eapply rt_call.
    { eapply (Hrc data len bs (Z_to_bv 64 (spv - 176)) buf (Z_to_bv 64 (a + 304)) sz _ 3%Z _ _ _ rom (Z_to_bv 64 0x15094)).
      - regv HR (1%bv:reg). reflexivity.
      - apply ret_ok_even. rewrite u_small by lia. reflexivity.
      - eapply (rc_pre_atI _ _ _ 0x6d414220%Z sz buf (a + 304)%Z 3%Z);
          [ exact HADM1 | exact HTAG1 | lia | lia | lia | apply mod8_add; [exact P2 | reflexivity]
          | regv HR (10%bv:reg); reflexivity
          | regv HR (11%bv:reg); reflexivity
          | reflexivity
          | regv HR (13%bv:reg); unfold W; rewrite Hoc; reflexivity
          | regv_lin HR (14%bv:reg); rewrite A8; f_equal; lia ]. }
    cbv beta. intros FPI' R' M' (Hkeep & Hfkeep & Hpost).
    unfold rcurves_post in Hpost. cbv zeta in Hpost. change (w_rcurves_d wp2_infoub) with 128%Z in Hpost.
    rewrite (u_small (spv - 176)), (u_small (a + 304)) in Hpost by lia.
    destruct Hpost as (Hfr2 & r2 & H10' & Hr01 & Hcv).
    destruct (adm_rcI _ FPI' _ R' _ M' (a + 304)%Z 3%Z HADM1 ltac:(lia) ltac:(lia) ltac:(lia) Hfr2 Hkeep Hfkeep) as (HADM' & HT' & HS').
    apply (m1I FPI' R' M' sz buf (bbI buf 8) r2 HADM' (HT' _ _ _ HTAG1) Hsz).
    - eapply cell32_frame; [exact Hfr2 | split; [lia | unfold W in C144; exact C144] | lia | lia | solve_apart].
    - lia.
    - eapply cell32_frame; [exact Hfr2 | split; [lia | unfold W in C300; rewrite Hoc in C300; exact C300] | lia | lia | solve_apart].
    - apply HS'. exact HSTK1.
    - exact H10'.
    - destruct Hr01 as [-> | ->]; [left; reflexivity | right; split; [reflexivity|]].
      eapply (curves0_rcI _ M' 304%Z 3%Z HC01 Hfr2); [lia | lia | lia | |].
      + intros i Hi. apply Hcv; [reflexivity | exact Hi].
      + intros o Hin. offsets_cases Hin;
          first [ left; lia | right; exists 0%Z; lia | right; exists 1%Z; lia | right; exists 2%Z; lia ].
    - rewrite (Hkeep 27%bv ltac:(in_kept)). regv HR (27%bv:reg). reflexivity.
    - rewrite (Hkeep 20%bv ltac:(in_kept)). regv HR (20%bv:reg). reflexivity.
    - rewrite (Hkeep 21%bv ltac:(in_kept)). regv HR (21%bv:reg). reflexivity.
    - rewrite (Hkeep 23%bv ltac:(in_kept)). regv HR (23%bv:reg). reflexivity.
    - rewrite (Hkeep 24%bv ltac:(in_kept)). regv HR (24%bv:reg). reflexivity.
    - rewrite (Hkeep 25%bv ltac:(in_kept)). regv HR (25%bv:reg). reflexivity.
    - rewrite (Hkeep 26%bv ltac:(in_kept)). regv HR (26%bv:reg). reflexivity.
    - rewrite (Hkeep 22%bv ltac:(in_kept)). regv HR (22%bv:reg). reflexivity.
    - rewrite (Hkeep 9%bv ltac:(in_kept)). regv HR (9%bv:reg). reflexivity.
    - rewrite (Hkeep 19%bv ltac:(in_kept)). regv HR (19%bv:reg). exact H19.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma m0a : forall (FPI : FPState) R M sz buf,
    ADM FPI R M -> TAGC 0x6d414220 sz buf M -> curves0I M ->
    getr R 9 = eobw -> getr R 19 = Z_to_bv 64 pcs ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x14f8c) M rom) QP.
  Proof.
    intros FPI R M sz buf HADM HTAG HC0 H9 H19.
    adm_facts HADM.
    pose proof HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c). pose proof (u64_range buf).
    pkg_tag HADM HTAG (@nil word) (@nil kentry) ltac:(constructor).
    run_fp 10%nat [0x1525c%Z; 0x14f98%Z] noscr true.
    branch_case as Hsz; [fail0 HADM|].
    hc_lin Hsz.
    adm_now HADM HADM1.
    apply (m0b _ _ _ sz buf HADM1 HTAG ltac:(lia) HC0).
    - regv HR (11%bv:reg). reflexivity.
    - regv HR (9%bv:reg). exact H9.
    - regv HR (19%bv:reg). exact H19.
  Qed.
End RG.
End LibReadA2BUbg.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP LibDefs LibWP2Spec LibWP2Lib LibFPSpec LibFrame LibRodata LibTagsLib LibBswap.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PerfKc.
Import LibReadA2BUba. Import LibReadA2BUbb. Import LibReadA2BUbc. Import LibReadA2BUbd. Import LibReadA2BUbe. Import LibReadA2BUbf. Import LibReadA2BUbg.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf Require Import SymDriveLB.
From Stdlib Require Import Zify.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymDriveLZ.
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
(* [comment removed for export] *)
Local Ltac ev_simpl E ::=   (* [comment removed for export] *)
  lazymatch goal with |- ?G =>
    let G1 := match tt with | _ => eval unfold E in G | _ => G end in
    let G2 := eval lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in G1 in
    change G2
  end.
Local Ltac ev_simpl_in E H ::= try unfold E in H; lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in H.
#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma sx4_hi : forall ty, (2147483648 <= ty < 4294967296)%Z ->
  bv_unsigned (ext_val true 0 4 (Z_to_bv 64 ty)) = (ty + 18446744069414584320)%Z.
Proof.
  intros ty Hty. unfold ext_val, ext_Z. rewrite (u_small ty) by lia. cbv iota. cbv beta. cbv zeta.
  replace (2 ^ (8 * Z.of_nat 0))%Z with 1%Z by reflexivity.
  replace (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z by reflexivity.
  rewrite Z.div_1_r. rewrite (Z.mod_small ty 4294967296) by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N (8 * N.of_nat 4))%Z with 4294967296%Z by reflexivity.
  replace (4294967296 `div` 2)%Z with 2147483648%Z by reflexivity.
  rewrite u_lit64a.
  replace ((ty + 2147483648) `mod` 4294967296)%Z with (ty + 2147483648 - 4294967296)%Z.
  2:{ symmetry. rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  rewrite zmod_neg by lia. lia.
Qed.

Section RH.
  Variables (FPI0 : FPState) (regs0 : bvmap 5 word) (mem0 rom : word -> option byte) (ret : word).
  Variables (data : word) (len : Z) (bs : list byte) (sp T A : word) (pcs : Z).
  Hypothesis Hra : getr regs0 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HPRE : a2b_pre SEGS wp2_infoub data len bs sp T A pcs FPI0 regs0 mem0.
  Hypothesis Hcanon : canonicalize_contract SEGS wp3_infoub.
  Hypothesis Hrc : read_curves_contract SEGS wp2_infoub.
  Hypothesis Hmftc : read_mft_common_a2b_contract SEGS wp2_infoub.

  #[local] Abbreviation a := (bv_unsigned A).
  #[local] Abbreviation spv := (bv_unsigned sp).
  #[local] Abbreviation t := (bv_unsigned T).
  #[local] Abbreviation ADM := (adm FPI0 regs0 mem0 ret data len bs sp T A).
  #[local] Abbreviation QP := (Qpost FPI0 regs0 mem0 rom ret data len bs sp T A pcs).
  #[local] Abbreviation CI := (chain_inv data len A).
  #[local] Abbreviation TAGC := (tagc data len T).
  #[local] Abbreviation pre_factsI := (pre_facts FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation pre_tagI := (pre_tag FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation pre_spI := (pre_sp FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation kn_adm_okI := (kn_adm_ok FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation kn_tag_okI := (kn_tag_ok FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation adm_frameI := (adm_frame FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation base_valsI := (base_vals regs0 ret data len).
  #[local] Abbreviation failkI := (failk FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE).
  #[local] Abbreviation in1I := (in1 FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).
  #[local] Abbreviation eobw := (Z_to_bv 64 (bv_unsigned data + len)).
  #[local] Abbreviation bbI := (bb data bs).
  #[local] Abbreviation WI := (W data bs).
  #[local] Abbreviation curves10I := (curves10 data len A).
  #[local] Abbreviation mab_cellsI := (mab_cells A).
  #[local] Abbreviation gslI := (gsl data bs).
  #[local] Abbreviation PvalI := (Pval data bs).
  #[local] Abbreviation be4I := (be4 data bs).
  #[local] Abbreviation le4wI := (le4w data bs).
  #[local] Abbreviation vals_m3I := (vals_m3 data len bs).
  #[local] Abbreviation curves10_frame1I := (curves10_frame1 FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation kn_m3_okI := (kn_m3_ok FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation curves0I := (curves0 data len A).
  #[local] Abbreviation curves0_frameI := (curves0_frame FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation tagc_frameI := (tagc_frame FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation in0I := (in0 FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).
  #[local] Abbreviation m3aI := (m3a FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).
  #[local] Abbreviation stkI := (stk data len bs sp).
  #[local] Abbreviation kn_stk_okI := (kn_stk_ok FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation stk_frameI := (stk_frame FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation mab_cells_frameI := (mab_cells_frame FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation rc_pre_atI := (rc_pre_at FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation adm_rcI := (adm_rc FPI0 regs0 mem0 ret data len bs sp T A pcs HPRE).
  #[local] Abbreviation curves0_rcI := (curves0_rc FPI0 regs0 mem0 data len bs sp T A pcs HPRE).
  #[local] Abbreviation jsegI := (jseg FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon Hrc).
  #[local] Abbreviation m1I := (m1 FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon Hrc).
  #[local] Abbreviation failk'I := (failk' FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE).
  #[local] Abbreviation m0aI := (m0a FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon Hrc).
  #[local] Abbreviation f1I := (f1 FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).
  #[local] Abbreviation f2I := (f2 FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).
  #[local] Abbreviation f1bI := (f1b FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).
  #[local] Abbreviation f2bI := (f2b FPI0 regs0 mem0 rom ret data len bs sp T A pcs Hret HPRE Hcanon).
  #[local] Abbreviation savedI := (saved regs0 ret sp).
  #[local] Abbreviation fkeptI := (fkept FPI0).
  #[local] Abbreviation BIGI := (BIG sp A).
  #[local] Abbreviation mftc_cellsI := (mftc_cells A).

  (* [comment removed for export] *)
  Ltac adm_facts HADM :=
    pose proof HADM as (A2 & A3 & A4 & A8 & A18 & AF & AS & AFR & AD & ARO & AWA & AWS);
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _);
    assert (U2 : bv_unsigned (getr _ 2) = (spv - 176)%Z) by (rewrite A2, u_small by lia; lia).

  Ltac pkg HADM extra kx ktac :=
    lazymatch goal with
    | |- runs_to _ (@mkst ?FPI ?R _ ?M _) _ =>
      set (E := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++
         [ret; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20; getr regs0 21;
          getr regs0 22; getr regs0 23; getr regs0 24; getr regs0 25; getr regs0 26; getr regs0 27;
          data; Z_to_bv 64 len] ++ extra)) (blobs_ev [bs]));
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs]));
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs]));
      pose proof (HR : id _) as HR0; pose proof (HF : id _) as HF0;
      let HK1 := fresh "HK1" in let HK2 := fresh "HK2" in
      pose proof (kn_adm_okI FPI R M extra HADM) as HK1; change (know_ok SEGS E M kn_adm) in HK1;
      assert (HK2 : know_ok SEGS E M kx); [ktac|];
      pose proof (know_ok_app SEGS E M kn_adm kx HK1 HK2) as HK; clear HK1 HK2;
      cbv beta delta [kn_adm app] in HK
    end.

  Ltac pkg_tag HADM HTAG rest kx ktac :=
    lazymatch type of HTAG with tagc _ _ _ ?ty ?sz ?buf _ =>
      pkg HADM ([Z_to_bv 64 sz; buf] ++ rest) (kn_tag ty ++ kx)
        ltac:(apply know_ok_app; [exact (kn_tag_okI _ _ _ ty sz buf rest HADM HTAG) | ktac])
    end.

  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.

  Ltac subst_mems :=
    repeat match goal with H : @eq (word -> option byte) ?x _ |- _ => is_var x; subst x end.

  Ltac adm_now HADM HADM1 :=
    subst_mems;
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1, HF : fregs_ok _ ?sfr (@fp_regs ?I1), HF0 : id (fregs_ok _ ?sfr0 (@fp_regs ?I0))
      |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ ?R ?M0 =>
        assert (HADM1 : ADM I1 R1 M1);
        [ apply (adm_frameI I0 I1 R R1 M0 M1 [] HADM);
          [ apply frame_mod_refl
          | apply Forall_nil
          | apply Forall_nil
          | regv HR (2%bv:reg); reflexivity
          | regv HR (3%bv:reg); reflexivity
          | regv HR (4%bv:reg); reflexivity
          | regv HR (8%bv:reg); reflexivity
          | regv HR (18%bv:reg); reflexivity
          | exact (fregs_same_on E sfr0 sfr _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)) ]
        | ]
      end
    end.
  (* [comment removed for export] *)


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac mods_in H :=
    repeat match type of H with context [ (?x mod ?m)%Z ] =>
      lazymatch x with context [ (_ mod _)%Z ] => fail | _ => rewrite (Z.mod_small x m) in H by lia end end.
  Ltac mods_goal :=
    repeat match goal with |- context [ (?x mod ?m)%Z ] =>
      lazymatch x with context [ (_ mod _)%Z ] => fail | _ => rewrite (Z.mod_small x m) by lia end end.

  (* [comment removed for export] *)
  Ltac zbool H :=
    first [ apply Z.ltb_lt in H | apply Z.ltb_ge in H | apply Z.eqb_eq in H | apply Z.eqb_neq in H ].
  Ltac hc_lin Hc :=
    revert Hc; rewrite ?branch_taken_Z; cbv beta iota; linearize;
    cbn [edenot fop1_denot fop2_denot fop3_denot];
    lazymatch goal with HK : know_ok _ ?E _ _ |- _ => ev_simpl E end;
    rewrite ?uW, ?Z_to_bv_unsigned, ?bv_wrap64_mod; intros Hc;
    try (apply (f_equal negb) in Hc; rewrite negb_involutive in Hc; cbn [negb] in Hc);
    mods_in Hc; zbool Hc.

  Ltac regions_eq :=
    cbn [regions_denot map fst snd]; unfold adenot, v_addi; cbn [a_base a_off edenot];
    lazymatch goal with HK : know_ok _ ?E _ _ |- _ => ev_simpl E end; rewrite_getr; rewrite ?u_small_frame by lia;
    repeat (apply f_equal2; [apply f_equal2; [apply f_equal; lia | lia] | ]); reflexivity.

  (* [comment removed for export] *)
  Ltac frame_logs RS :=
    lazymatch goal with
    | |- frame_mod ?m0 ?m0 _ => apply frame_mod_refl
    | HK : know_ok _ ?E _ _ |- frame_mod ?m0 (mem_denot _ ?m1 ?log) _ =>
        apply (frame_mod_trans_same m0 m1);
        [ frame_logs RS
        | apply (frame_mod_mem_denot E m1 log RS);
          [ lazymatch goal with H : log_flat _ log |- _ => exact H end
          | repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; unfold flat, estart;
            cbn [a_base a_off edenot]; ev_simpl E; rewrite_getr; rewrite ?u_small_frame by lia; lia
          | vm_compute; reflexivity ] ]
    end.

  (* [comment removed for export] *)
  Ltac frame_now HADM RS rsZ Hfr :=
    subst_mems;
    lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ _ ?M0 =>
    lazymatch goal with HK : know_ok _ ?E ?M1 _ |- _ =>
      assert (Hfr : frame_mod M0 M1 rsZ);
      [ replace rsZ with (regions_denot E RS) by regions_eq; frame_logs RS | ]
    end end.

  (* [comment removed for export] *)
  Ltac adm_fr HADM Hfr HADM1 :=
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1, HF : fregs_ok _ ?sfr (@fp_regs ?I1), HF0 : id (fregs_ok _ ?sfr0 (@fp_regs ?I0))
      |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ ?R ?M0 =>
        assert (HADM1 : ADM I1 R1 M1);
        [ apply (adm_frameI I0 I1 R R1 M0 M1 _ HADM Hfr);
          [ solve [unfold BIG; solve_within]
          | solve [pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ? & _); solve_apart]
          | regv HR (2%bv:reg); reflexivity
          | regv HR (3%bv:reg); reflexivity
          | regv HR (4%bv:reg); reflexivity
          | regv HR (8%bv:reg); reflexivity
          | regv HR (18%bv:reg); reflexivity
          | exact (fregs_same_on E sfr0 sfr _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)) ]
        | ]
      end
    end.

  (* [comment removed for export] *)
  Ltac w_lt :=
    rewrite ?uW;
    lazymatch goal with
    | |- (bb _ _ ?b ?i < _)%Z => pose proof (bb_range data bs b i); lia
    | |- _ => rewrite ?u_small by lia; lia
    end.

  (* [comment removed for export] *)
  Ltac flat_tac := unfold flat, estart; cbn [a_base a_off edenot];
    lazymatch goal with HK : know_ok _ ?E _ _ |- _ => ev_simpl E end; rewrite_getr; rewrite ?u_small_frame by lia; lia.
  Ltac kcellv b k n H :=
    lazymatch goal with HK : know_ok _ ?E ?M ?kn |- _ =>
      let r := eval vm_compute in (kread SEGS kn b k n) in
      lazymatch r with
      | Some ?v =>
        let KR := fresh "KR" in let Hfl := fresh "Hfl" in
        kread_rdn_fast SEGS E M kn b k n v HK H;
        lazymatch type of H with ?FL -> _ => assert (Hfl : FL) by flat_tac; specialize (H Hfl); clear Hfl end;
        unfold adenot, v_addi in H; cbn [a_base a_off edenot] in H; ev_simpl_in E H; rewrite_getr_in H;
        rewrite ?u_small_frame in H by lia;
        rewrite ?ext_val_zx_id4 in H by w_lt;
        rewrite ?ext_val_zx_id1 in H by w_lt
      | _ => fail "kcellv: no knowledge at" b k n
      end
    end.


  (* [comment removed for export] *)
  Ltac fail_st HADM RS rsZ :=
    let Hfr := fresh "Hfr" in let HADM1 := fresh "HADMf" in
    frame_now HADM RS rsZ Hfr; adm_fr HADM Hfr HADM1;
    match goal with H : adm _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => apply (failkI _ _ _ H) end.
  (* [comment removed for export] *)
  Ltac in_kept := cbn; repeat (first [ left; reflexivity | right ]).

  (* [comment removed for export] *)
  Ltac fail0 HADM :=
    let HADM1 := fresh "HADMf" in adm_now HADM HADM1;
    match goal with H : adm _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => apply (failkI _ _ _ H) end.


  Ltac pkg_stk HADM HTAG HSTK rest kx ktac :=
    lazymatch type of HTAG with tagc _ _ _ ?ty ?sz ?buf _ =>
      pkg HADM ([Z_to_bv 64 sz; buf] ++ [WI buf 24; WI buf 25; WI buf 26; WI buf 27; WI buf 28; WI buf 29; WI buf 30; WI buf 31; eobw] ++ rest) (kn_tag ty ++ kn_stk ++ kx)
        ltac:(apply know_ok_app; [exact (kn_tag_okI _ _ _ ty sz buf _ HADM HTAG)
             | apply know_ok_app; [exact (kn_stk_okI _ _ _ sz buf rest HADM HSTK) | ktac]]);
      lazymatch goal with HK : know_ok _ _ _ ?kn |- _ =>
        let kn' := eval vm_compute in kn in change kn with kn' in HK end;
      match goal with Edef := Env _ _ |- _ => cbn [app] in Edef end
    end.

  Ltac offsets_cases Hin :=
    cbn [a2b_curve_offsets In] in Hin;
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]].



  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition adm0 (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
    getr R 2 = Z_to_bv 64 (spv - 176) /\ getr R 3 = getr regs0 3 /\ getr R 4 = getr regs0 4 /\
    getr R 18 = T /\ getr R 11 = A /\ getr R 12 = Z_to_bv 64 pcs /\ getr R 13 = eobw /\
    fkeptI FPI /\ savedI M /\ frame_mod mem0 M BIGI /\
    data_ok M data len bs /\ rodata_clear M 0x103ec 0x10490 /\
    writable SEGS M a 400 /\ writable SEGS M (spv - 352) 352.

  Lemma adm0_adm : forall (FPI FPI' : FPState) R R' M,
    adm0 FPI R M ->
    getr R' 2 = getr R 2 -> getr R' 3 = getr R 3 -> getr R' 4 = getr R 4 -> getr R' 8 = A -> getr R' 18 = T ->
    (forall r, In r abi_fkept -> reg_get (fp_regs (FPState:=FPI')) r = reg_get (fp_regs (FPState:=FPI)) r) ->
    ADM FPI' R' M.
  Proof.
    intros FPI FPI' R R' M (B2 & B3 & B4 & B10 & B11 & B12 & B13 & BF & BS & BFR & BD & BRO & BWA & BWS) E2 E3 E4 E8 E18 EF.
    split; [rewrite E2; exact B2|]. split; [rewrite E3; exact B3|]. split; [rewrite E4; exact B4|].
    split; [exact E8|]. split; [exact E18|].
    split; [intros r Hr; rewrite (EF r Hr); apply BF; exact Hr|].
    repeat (split; [assumption|]). assumption.
  Qed.

  (* [comment removed for export] *)
  Definition kn_d (tye : expr) : list kentry :=
    [KWord (SA (EVar 2) 168) 8 (EVar 64); KWord (SA (EVar 2) 160) 8 (EVar 65); KWord (SA (EVar 2) 152) 8 (EVar 66);
     KWord (SA (EVar 2) 144) 8 (EVar 67); KWord (SA (EVar 2) 136) 8 (EVar 68); KWord (SA (EVar 2) 128) 8 (EVar 69);
     KWord (SA (EVar 2) 120) 8 (EVar 70); KWord (SA (EVar 2) 112) 8 (EVar 71); KWord (SA (EVar 2) 104) 8 (EVar 72);
     KWord (SA (EVar 2) 96) 8 (EVar 73); KWord (SA (EVar 2) 88) 8 (EVar 74); KWord (SA (EVar 2) 80) 8 (EVar 75);
     KWord (SA (EVar 2) 72) 8 (EVar 76);
     KImg 0x103ec 0x10490;
     KRange (EVar 2) 176 18446744073709551440; KWr (SA (EVar 2) (-176)) 352;
     KRange (EVar 11) 1 18446744073709551215; KAlign (EVar 11) 8; KWr (SA (EVar 11) 0) 400;
     KDisj (SA (EVar 2) (-176)) 352 (SA (EVar 11) 0) 400;
     KWord (SA (EVar 18) 4) 4 tye; KWord (SA (EVar 18) 8) 4 (EVar 79); KWord (SA (EVar 18) 16) 8 (EVar 80);
     KRange (EVar 79) 4 67108864; KRange (EVar 80) 1 140737488355328;
     KDisj (SA (EVar 18) 0) 24 (SA (EVar 2) (-176)) 352; KDisj (SA (EVar 18) 0) 24 (SA (EVar 11) 0) 400].

  Lemma kn_d_ok : forall (FPI : FPState) R M ty sz buf tye extra,
    adm0 FPI R M -> TAGC ty sz buf M ->
    let E := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ base_valsI ++ ([Z_to_bv 64 sz; buf] ++ extra))) (blobs_ev [bs]) in
    edenot E tye = Z_to_bv 64 ty ->
    know_ok SEGS E M (kn_d tye).
  Proof.
    intros FPI R M ty sz buf tye extra (B2 & B3 & B4 & B10 & B11 & B12 & B13 & BF & BS & BFR & BD & BRO & BWA & BWS)
           (C1 & C2 & C3 & H4 & H5) E Htye.
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14).
    pose proof pre_tagI as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof (u64_range T). pose proof (u64_range buf).
    destruct H5 as (H5a & H5b & H5c). destruct C2 as [Hsz C2].
    assert (U2 : bv_unsigned (getr R 2) = (spv - 176)%Z) by (rewrite B2, u_small by lia; lia).
    destruct BS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
    unfold base_vals in E. unfold kn_d.
    repeat apply Forall_cons; try apply Forall_nil.
    all: try (eapply (kword_intro SEGS E M (EVar 2) (getr R 2) _ 8 _ _);
           [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia |
            rewrite U2; unfold cell64, cell in *;
            match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ =>
              first [ replace x with (spv - 176 + 168)%Z by ring; eassumption
                    | replace x with (spv - 176 + 160)%Z by ring; eassumption
                    | replace x with (spv - 176 + 152)%Z by ring; eassumption
                    | replace x with (spv - 176 + 144)%Z by ring; eassumption
                    | replace x with (spv - 176 + 136)%Z by ring; eassumption
                    | replace x with (spv - 176 + 128)%Z by ring; eassumption
                    | replace x with (spv - 176 + 120)%Z by ring; eassumption
                    | replace x with (spv - 176 + 112)%Z by ring; eassumption
                    | replace x with (spv - 176 + 104)%Z by ring; eassumption
                    | replace x with (spv - 176 + 96)%Z by ring; eassumption
                    | replace x with (spv - 176 + 88)%Z by ring; eassumption
                    | replace x with (spv - 176 + 80)%Z by ring; eassumption
                    | replace x with (spv - 176 + 72)%Z by ring; eassumption ] end]).
    - apply kimg_intro; [lia|lia|exact BRO].
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite U2; lia.
    - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-176) 352); [cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia |].
      rewrite U2. replace (spv - 176 + -176)%Z with (spv - 352)%Z by lia. exact (proj2 (proj2 (proj2 BWS))).
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite B11; lia.
    - apply kalign_intro; [lia|]. cbn [edenot]; ev_simpl E. rewrite B11. exact P2.
    - apply (kwr_intro SEGS E M (EVar 11) A 0 400); [cbn [edenot]; ev_simpl E; exact B11 | lia | lia | lia |].
      rewrite Z.add_0_r. exact (proj2 (proj2 (proj2 BWA))).
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite U2, B11. lia.
    - eapply (kword_intro SEGS E M (EVar 18) T 4 4 tye (Z_to_bv 64 ty));
        [cbn [edenot]; ev_simpl E; exact B10 | exact Htye | lia | lia | lia | lia | exact (proj2 C1)].
    - eapply (kword_intro SEGS E M (EVar 18) T 8 4 (EVar 79) (Z_to_bv 64 sz));
        [cbn [edenot]; ev_simpl E; exact B10 | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | exact C2].
    - eapply (kword_intro SEGS E M (EVar 18) T 16 8 (EVar 80) buf);
        [cbn [edenot]; ev_simpl E; exact B10 | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | exact C3].
    - apply krange_intro; cbn [edenot]; ev_simpl E. rewrite u_small by lia. lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E. lia.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite U2, B10. lia.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite B11, B10. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac pkg_d HADM0 HTAG extra tye :=
    lazymatch goal with
    | |- runs_to _ (@mkst ?FPI ?R _ ?M _) _ =>
      lazymatch type of HTAG with tagc _ _ _ ?ty ?sz ?buf _ =>
      set (E := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++
         [ret; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20; getr regs0 21;
          getr regs0 22; getr regs0 23; getr regs0 24; getr regs0 25; getr regs0 26; getr regs0 27;
          data; Z_to_bv 64 len] ++ ([Z_to_bv 64 sz; buf] ++ extra))) (blobs_ev [bs]));
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs]));
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs]));
      pose proof (HR : id _) as HR0; pose proof (HF : id _) as HF0;
      pose proof (kn_d_ok FPI R M ty sz buf tye extra HADM0 HTAG ltac:(cbn [edenot]; reflexivity)) as HK;
      change (know_ok SEGS E M (kn_d tye)) in HK;
      lazymatch goal with HK : know_ok _ _ _ ?kn |- _ =>
        let kn' := eval vm_compute in kn in change kn with kn' in HK end;
      cbn [app] in E
      end
    end.

  (* [comment removed for export] *)
  Ltac adm_from0 HADM0 HADM1 :=
    subst_mems;
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1, HF : fregs_ok _ ?sfr (@fp_regs ?I1), HF0 : id (fregs_ok _ ?sfr0 (@fp_regs ?I0))
      |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      lazymatch type of HADM0 with adm0 _ ?R _ =>
        assert (HADM1 : ADM I1 R1 M1);
        [ apply (adm0_adm I0 I1 R R1 M1 HADM0);
          [ regv HR (2%bv:reg); reflexivity
          | regv HR (3%bv:reg); reflexivity
          | regv HR (4%bv:reg); reflexivity
          | regv HR (8%bv:reg); lazymatch type of HADM0 with adm0 _ _ _ => idtac end;
            match goal with H : adm0 _ _ _ |- _ => exact (proj1 (proj2 (proj2 (proj2 (proj2 H))))) end
          | regv HR (18%bv:reg);
            match goal with H : adm0 _ _ _ |- _ => exact (proj1 (proj2 (proj2 (proj2 H)))) end
          | exact (fregs_same_on E sfr0 sfr _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)) ]
        | ]
      end
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mftc_pre_at : forall (FPI : FPState) R M ty sz buf,
    ADM FPI R M -> TAGC ty sz buf M -> (48 <= sz)%Z -> getr R 10 = buf -> getr R 11 = A ->
    mftc_a2b_pre SEGS data len bs buf A FPI R M.
  Proof.
    intros FPI R M ty sz buf HADM (T1 & T2 & T3 & T4 & T5) Hsz H10 H11. adm_facts HADM.
    pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P11 & _).
    unfold mftc_a2b_pre. destruct T5 as (T5a & T5b & T5c).
    split; [exact H10|]. split; [exact H11|]. split; [exact AD|]. split; [unfold inDATA; lia|].
    split; [exact AWA|]. split; [exact P2|]. exact P11.
  Qed.

  Lemma adm_mftc : forall (FPI FPI' : FPState) R R' M M',
    ADM FPI R M ->
    frame_mod M M' [(Z_to_bv 64 (a + 144), 8%Z); (Z_to_bv 64 (a + 296), 8%Z)] ->
    regs_kept abi_kept R R' ->
    (forall r, In r abi_fkept -> reg_get (fp_regs (FPState:=FPI')) r = reg_get (fp_regs (FPState:=FPI)) r) ->
    ADM FPI' R' M' /\ (forall ty sz buf, TAGC ty sz buf M -> TAGC ty sz buf M') /\ (curves0I M -> curves0I M').
  Proof.
    intros FPI FPI' R R' M M' HADM Hf Hk Hfk.
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _).
    pose proof pre_tagI as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof (u64_range T).
    split; [|split].
    - apply (adm_frameI FPI FPI' R R' M M' _ HADM Hf).
      + unfold BIG; solve_within.
      + solve_apart.
      + apply Hk; in_kept. + apply Hk; in_kept. + apply Hk; in_kept. + apply Hk; in_kept. + apply Hk; in_kept.
      + exact Hfk.
    - intros ty sz buf HT. eapply tagc_frameI; [exact HT|exact Hf|]. solve_apart.
    - intros HC. eapply curves0_frameI; [exact HC | exact Hf | solve_apart |].
      unfold a2b_curve_offsets; repeat (apply Forall_cons; [solve_apart|]); apply Forall_nil.
  Qed.

  (* [comment removed for export] *)
  Ltac call_mftc HADM1 HTAG HC0 Hsz retpc fk :=
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1 |- runs_to _ (@mkst ?I1 _ _ ?M1 _) _ =>
      lazymatch type of HTAG with tagc _ _ _ ?ty ?sz ?buf _ =>
      eapply rt_call;
      [ eapply (Hmftc data len bs buf A I1 R1 M1 rom (Z_to_bv 64 retpc));
        [ regv HR (1%bv:reg); reflexivity
        | apply ret_ok_even; rewrite u_small by lia; reflexivity
        | eapply (mftc_pre_at I1 R1 M1 ty sz buf HADM1 HTAG Hsz); [regv HR (10%bv:reg); reflexivity | regv HR (11%bv:reg); assumption] ]
      | cbv beta;
        let I' := fresh "FPI" in let R' := fresh "R" in let M' := fresh "M" in
        let Hkeep := fresh "Hkeep" in let Hfkeep := fresh "Hfkeep" in let Hfr := fresh "Hfr" in
        let r := fresh "r" in let H10 := fresh "H10'" in let Hr01 := fresh "Hr01" in let Hcells := fresh "Hcells" in
        intros I' R' M' (Hkeep & Hfkeep & Hfr & r & H10 & Hr01 & Hcells);
        cbv zeta in Hfr;
        let HADM' := fresh "HADM'" in let HT' := fresh "HT'" in let HC' := fresh "HC'" in
        destruct (adm_mftc I1 I' R1 R' M1 M' HADM1 Hfr Hkeep Hfkeep) as (HADM' & HT' & HC');
        fk I' R' M' r HADM' HT' HC' Hkeep H10 Hr01 Hcells
      ]
      end
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dseg : forall (FPI : FPState) R M ty sz buf,
    adm0 FPI R M -> TAGC ty sz buf M -> curves0I M ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x14e48) M rom) QP.
  Proof.
    intros FPI R M ty sz buf HADM0 HTAG HC0.
    pose proof HADM0 as (B2 & B3 & B4 & B10 & B11 & B12 & B13 & BF & BS & BFR & BD & BRO & BWA & BWS).
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _).
    assert (U2 : bv_unsigned (getr R 2) = (spv - 176)%Z) by (rewrite B2, u_small by lia; lia).
    pose proof HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c). pose proof (u64_range buf).
    destruct (Z.eq_dec ty 0x6d667431) as [Ety1|Nty1];
      [| destruct (Z.eq_dec ty 0x6d667432) as [Ety2|Nty2];
         [| destruct (Z.eq_dec ty 0x6d414220) as [Ety3|Nty3] ]].
    - (* [comment removed for export] *)
      subst ty.
      pkg_d HADM0 HTAG (@nil word) (ELit 0x6d667431%Z).
      run_fp 30%nat [0x1667c%Z; 0x14eb8%Z] noscr true.
      branch_case as Hs48.
      + (* [comment removed for export] *)
        hc_lin Hs48. assert (Hsz : (48 <= sz)%Z) by lia.
        run_fp 20%nat [0x1667c%Z; 0x14eb8%Z] noscr true.
        adm_from0 HADM0 HADM1.
        call_mftc HADM1 HTAG HC0 Hsz 0x14e94%Z
          ltac:(fun I' R' M' r HADM' HT' HC' Hkeep H10 Hr01 Hcells =>
            apply (f1I I' R' M' sz buf r HADM' (HT' _ _ _ HTAG) ltac:(lia));
            [ rewrite (Hkeep 20%bv ltac:(in_kept)); regv HR (20%bv:reg); reflexivity
            | rewrite (Hkeep 21%bv ltac:(in_kept)); regv HR (21%bv:reg); reflexivity
            | exact H10
            | destruct Hr01 as [-> | ->]; [left; reflexivity | right; split; [reflexivity|]];
              destruct (Hcells eq_refl) as (ic & g & Hic & Hg & D1 & D2 & D3 & D4);
              exists ic, g; split; [exact Hic|]; split; [exact Hg|]; split; [exact D1|]; split; [exact D2|]; split; [exact D3|]; exact D4
            | apply HC'; exact HC0 ]).
      + (* [comment removed for export] *)
        run_fp 20%nat [0x1667c%Z; 0x14eb8%Z] noscr true.
        adm_from0 HADM0 HADM1.
        apply (f1bI _ _ _ sz buf 0%Z 0%Z HADM1 HTAG); [regv HR (10%bv:reg); reflexivity | regv HR (21%bv:reg); reflexivity | left; reflexivity].
    - (* [comment removed for export] *)
      subst ty.
      pkg_d HADM0 HTAG (@nil word) (ELit 0x6d667432%Z).
      run_fp 30%nat [0x1667c%Z; 0x14f7c%Z] noscr true.
      branch_case as Hs52.
      + hc_lin Hs52. assert (Hsz : (48 <= sz)%Z) by lia.
        run_fp 20%nat [0x1667c%Z; 0x14f7c%Z] noscr true.
        adm_from0 HADM0 HADM1.
        call_mftc HADM1 HTAG HC0 Hsz 0x14eec%Z
          ltac:(fun I' R' M' r HADM' HT' HC' Hkeep H10 Hr01 Hcells =>
            apply (f2I I' R' M' sz buf r HADM' (HT' _ _ _ HTAG) ltac:(lia));
            [ rewrite (Hkeep 20%bv ltac:(in_kept)); regv HR (20%bv:reg); reflexivity
            | exact H10
            | destruct Hr01 as [-> | ->]; [left; reflexivity | right; split; [reflexivity|]];
              destruct (Hcells eq_refl) as (ic & g & Hic & Hg & D1 & D2 & D3 & D4);
              exists ic, g; split; [exact Hic|]; split; [exact Hg|]; split; [exact D1|]; split; [exact D2|]; split; [exact D3|]; exact D4
            | apply HC'; exact HC0 ]).
      + run_fp 20%nat [0x1667c%Z; 0x14f7c%Z] noscr true.
        adm_from0 HADM0 HADM1.
        apply (f2bI _ _ _ sz buf 0%Z 0%Z HADM1 HTAG); [regv HR (10%bv:reg); reflexivity | left; reflexivity].
    - (* [comment removed for export] *)
      subst ty.
      pkg_d HADM0 HTAG (@nil word) (ELit 0x6d414220%Z).
      run_fp 40%nat [0x1667c%Z; 0x14f8c%Z] noscr true.
      adm_from0 HADM0 HADM1.
      apply (m0aI _ _ _ sz buf HADM1 HTAG HC0); [regv HR (9%bv:reg); exact B13 | regv HR (19%bv:reg); exact B12].
    - (* [comment removed for export] *)
      destruct T1 as [Hty _].
      destruct (Z_lt_le_dec ty 2147483648) as [Hlo|Hhi].
      + pkg_d HADM0 HTAG [Z_to_bv 64 ty] (EVar 81).
        lazymatch goal with HK : know_ok _ _ ?M ?kn |- _ =>
          assert (HK' : know_ok SEGS E M (kn ++ [KRange (EVar 81) 0 2147483647]))
            by (apply know_ok_app; [exact HK | constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia | constructor]]);
          clear HK; rename HK' into HK; cbn [app] in HK end.
        run_fp 30%nat [0x1667c%Z; 0x1525c%Z] noscr true.
        branch_case as Hc1; [| hc_lin Hc1; exfalso; lia].
        run_fp 30%nat [0x1667c%Z; 0x1525c%Z] noscr true.
        branch_case as Hc2; [| hc_lin Hc2; exfalso; lia].
        run_fp 30%nat [0x1667c%Z; 0x1525c%Z] noscr true.
        branch_case as Hc3; [| hc_lin Hc3; exfalso; lia].
        run_fp 30%nat [0x1667c%Z; 0x1525c%Z] noscr true.
        adm_from0 HADM0 HADM1. apply (failkI _ _ _ HADM1).
      + pkg_d HADM0 HTAG [Z_to_bv 64 ty] (EVar 81).
        lazymatch goal with HK : know_ok _ _ ?M ?kn |- _ =>
          assert (HK' : know_ok SEGS E M (kn ++ [KRange (EVar 81) 2147483648 4294967295]))
            by (apply know_ok_app; [exact HK | constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia | constructor]]);
          clear HK; rename HK' into HK; cbn [app] in HK end.
        run_fp 30%nat [0x1667c%Z; 0x1525c%Z] noscr true.
        branch_case as Hc1; [| hc_lin Hc1; rewrite sx4_hi in Hc1 by lia; exfalso; lia].
        run_fp 30%nat [0x1667c%Z; 0x1525c%Z] noscr true.
        branch_case as Hc2; [| hc_lin Hc2; rewrite sx4_hi in Hc2 by lia; exfalso; lia].
        run_fp 30%nat [0x1667c%Z; 0x1525c%Z] noscr true.
        branch_case as Hc3; [| hc_lin Hc3; rewrite sx4_hi in Hc3 by lia; exfalso; lia].
        run_fp 30%nat [0x1667c%Z; 0x1525c%Z] noscr true.
        adm_from0 HADM0 HADM1. apply (failkI _ _ _ HADM1).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma entry : runs_to SEGS (mkst (FP:=FPI0) regs0 (Z_to_bv 64 0x14e04) mem0 rom) QP.
  Proof.
    pose proof HPRE as (Hsp & HT & HA & Hpcs & Heob & Hpcs01 & Hdok & (ty & Hty) & (sz & buf & Hsz & Hbuf & H4 & Hin) & HTal & HT24 &
                      WA & HAal & HApos & HA400 & Hcurves & Hg & Hspal & WS & Hro & D1 & D2 & D3 & D4 & D5 & D6).
    change (w_ab_d wp2_infoub) with 352%Z in *.
    change (w_ro_lo wp2_infoub) with 0x103ec%Z in *. change (w_ro_hi wp2_infoub) with 0x10490%Z in *.
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14).
    pose proof (u64_range T) as RT.
    set (E := Env (vals_ev (junk_vals regs0 ++ fjunk_vals (fp_regs (FPState:=FPI0)) ++ [data; Z_to_bv 64 len])) (blobs_ev [bs])).
    assert (HR : regs_ok E (sr_vars 0) regs0) by exact (regs_ok_vars [] regs0 _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs0) fp_regs _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    assert (HK : know_ok SEGS E mem0 [KRange (EVar 2) 352 18446744073709551615; KWr (SA (EVar 2) (-352)) 352; KAlign (EVar 10) 8]).
    { constructor; [| constructor; [| constructor; [| constructor]]].
      - apply krange_intro; cbn [edenot]; ev_simpl E. rewrite Hsp. lia.
      - apply (kwr_intro SEGS E mem0 (EVar 2) sp (-352) 352); [cbn [edenot]; ev_simpl E; exact Hsp | lia | lia | lia |].
        replace (spv + -352)%Z with (spv - 352)%Z by lia. exact (proj2 (proj2 (proj2 WS))).
      - apply kalign_intro; [lia|]. cbn [edenot]; ev_simpl E. rewrite HT. exact HTal. }
    run_fp 30%nat [0x14e48%Z] noscr true.
    (* [comment removed for export] *)
    subst_mems.
    lazymatch goal with |- runs_to _ (@mkst ?I1 ?R1 _ ?M1 _) _ =>
      assert (Hfr : frame_mod mem0 M1 [(Z_to_bv 64 (spv - 176), 176%Z)]);
      [ replace [(Z_to_bv 64 (spv - 176), 176%Z)] with (regions_denot E [(SA (EVar 2) (-176), 176%Z)]) by regions_eq;
        frame_logs [(SA (EVar 2) (-176), 176%Z)] | ]
    end.
    lazymatch goal with |- runs_to _ (@mkst ?I1 ?R1 _ ?M1 _) _ => remember M1 as Mz eqn:HMz in *; clear HMz end.
    kcellv (EVar 2) (-8)%Z 8%nat S1. kcellv (EVar 2) (-16)%Z 8%nat S2. kcellv (EVar 2) (-24)%Z 8%nat S3.
    kcellv (EVar 2) (-32)%Z 8%nat S4. kcellv (EVar 2) (-40)%Z 8%nat S5. kcellv (EVar 2) (-48)%Z 8%nat S6.
    kcellv (EVar 2) (-56)%Z 8%nat S7. kcellv (EVar 2) (-64)%Z 8%nat S8. kcellv (EVar 2) (-72)%Z 8%nat S9.
    kcellv (EVar 2) (-80)%Z 8%nat S10. kcellv (EVar 2) (-88)%Z 8%nat S11. kcellv (EVar 2) (-96)%Z 8%nat S12.
    kcellv (EVar 2) (-104)%Z 8%nat S13.
    lazymatch goal with |- runs_to _ (@mkst ?I1 ?R1 _ ?M1 _) _ =>
      assert (HADM0 : adm0 I1 R1 M1) end.
    { unfold adm0.
      split; [regv_lin HR (2%bv:reg); rewrite Hsp; f_equal; lia|].
      split; [regv HR (3%bv:reg); reflexivity|]. split; [regv HR (4%bv:reg); reflexivity|].
      split; [regv HR (18%bv:reg); exact HT|]. split; [regv HR (11%bv:reg); exact HA|].
      split; [regv HR (12%bv:reg); exact Hpcs|]. split; [regv HR (13%bv:reg); exact Heob|].
      split; [intros r Hr; exact (fregs_same_on E _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity) r Hr)|].
      split.
      { unfold saved, cell64, cell.
        repeat match goal with |- _ /\ _ => split end;
        match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ =>
          first [ replace x with (spv + -8)%Z by ring; exact S1 | replace x with (spv + -16)%Z by ring; exact S2
                | replace x with (spv + -24)%Z by ring; exact S3 | replace x with (spv + -32)%Z by ring; exact S4
                | replace x with (spv + -40)%Z by ring; exact S5 | replace x with (spv + -48)%Z by ring; exact S6
                | replace x with (spv + -56)%Z by ring; exact S7 | replace x with (spv + -64)%Z by ring; exact S8
                | replace x with (spv + -72)%Z by ring; exact S9 | replace x with (spv + -80)%Z by ring; exact S10
                | replace x with (spv + -88)%Z by ring; exact S11 | replace x with (spv + -96)%Z by ring; exact S12
                | replace x with (spv + -104)%Z by ring; exact S13 ] end. }
      split; [eapply frame_mod_within; [| exact Hfr]; unfold BIG; solve_within|].
      split; [eapply data_ok_frame; [exact Hfr | exact Hdok | solve_apart]|].
      split; [eapply rodata_clear_frame; [exact Hfr | exact Hro | lia | lia | solve_apart]|].
      split; [eapply writable_frame; [exact Hfr | exact WA]|].
      eapply writable_frame; [exact Hfr | exact WS]. }
    apply (dseg _ _ _ ty sz buf HADM0).
    - split; [eapply cell32_frame; [exact Hfr | exact Hty | lia | lia | solve_apart]|].
      split; [eapply cell32_frame; [exact Hfr | exact Hsz | lia | lia | solve_apart]|].
      split; [eapply cell64_frame; [exact Hfr | exact Hbuf | lia | lia | solve_apart]|].
      split; [exact H4 | exact Hin].
    - eapply curves0_frameI; [| exact Hfr | solve_apart |].
      + split; [exact Hcurves | exact Hg].
      + unfold a2b_curve_offsets; repeat (apply Forall_cons; [solve_apart|]); apply Forall_nil.
  Qed.
End RH.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem read_a2b_Ub_ok :
  read_mft_common_a2b_contract SEGS wp2_infoub ->
  init_tables_a2b_contract SEGS wp2_infoub ->
  read_curves_contract SEGS wp2_infoub ->
  canonicalize_contract SEGS wp3_infoub ->
  read_a2b_contract SEGS wp2_infoub.
Proof.
  intros Hmftc _ Hrc Hcanon. unfold read_a2b_contract. intros data len bs sp T A pcs.
  unfold fn_contract. intros FPI regs mem rom ret Hra Hret HPRE.
  destruct (runs_to_contract SEGS _ ret rom _ (entry FPI regs mem rom ret data len bs sp T A pcs Hra Hret HPRE Hcanon Hrc Hmftc))
    as (FPI' & regs' & mem' & Hms & Hk & Hfk & Hpost).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk|]. split; [exact Hfk|]. exact Hpost.
Qed.
