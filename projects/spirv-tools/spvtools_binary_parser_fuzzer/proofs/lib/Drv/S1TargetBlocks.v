(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Frame SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymAux SymTac SymBranch RefPrintfLib RefMemcpyLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1TargetDefs S1PrintfBufBase S1Cells S1RwWindow.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition MEMCPY : Z := 0xe0e44.
Definition EXITPC : Z := 0xd00fc.
Definition RET_MALLOC : Z := 0x6591c.
Definition RET_MEMCPY : Z := 0x65930.
Definition RET_LLVM : Z := 0x65984.
Definition RET_EMIT : Z := 0x65994.
Definition RET_FREE : Z := 0x659b0.
Definition MAIN_JOIN : Z := 0x657dc.
Definition RET_FREE_MAIN : Z := 0x657e4.

Definition MINUS2 : Z := 0xfffffffffffffffe.

Lemma alu_add_ZZ : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. rewrite alu_add. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- Z.add_mod by (cbn; lia). reflexivity.
Qed.

Record tr_frame (sp0 : Z) (R0 : bvmap 5 word) (M : word -> option byte) : Prop := {
  tf_ra : rdn RSEGS M (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 TR_MAINRET));
  tf_s0 : rdn RSEGS M (Z_to_bv 64 (sp0 - 144)) 8 = Some (word_to_le_bytes 8 (getr R0 8));
  tf_s1 : rdn RSEGS M (Z_to_bv 64 (sp0 - 152)) 8 = Some (word_to_le_bytes 8 (getr R0 9));
  tf_s2 : rdn RSEGS M (Z_to_bv 64 (sp0 - 160)) 8 = Some (word_to_le_bytes 8 (getr R0 18));
  tf_s3 : rdn RSEGS M (Z_to_bv 64 (sp0 - 168)) 8 = Some (word_to_le_bytes 8 (getr R0 19));
  tf_s4 : rdn RSEGS M (Z_to_bv 64 (sp0 - 176)) 8 = Some (word_to_le_bytes 8 (getr R0 20));
  tf_s5 : rdn RSEGS M (Z_to_bv 64 (sp0 - 184)) 8 = Some (word_to_le_bytes 8 (getr R0 21));
  tf_s6 : rdn RSEGS M (Z_to_bv 64 (sp0 - 192)) 8 = Some (word_to_le_bytes 8 (getr R0 22));
  tf_s7 : rdn RSEGS M (Z_to_bv 64 (sp0 - 200)) 8 = Some (word_to_le_bytes 8 (getr R0 23))
}.

Lemma tr_frame_agree : forall sp0 R0 M M',
  (forall i, sp0 - 200 <= i < sp0 - 128 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  0x1000 <= sp0 <= 0x800000000000 ->
  tr_frame sp0 R0 M -> tr_frame sp0 R0 M'.
Proof.
  intros sp0 R0 M M' HS Hsp FR. destruct FR.
  constructor;
    lazymatch goal with H : rdn _ M (Z_to_bv 64 ?a) ?n = ?rhs |- rdn _ M' (Z_to_bv 64 ?a) ?n = ?rhs =>
      rewrite <- H; apply rdn_ext; [rewrite u64_lit by lia; cbn; lia|];
      intros x Hx; rewrite u64_lit in Hx by lia;
      replace x with (Z_to_bv 64 (bv_unsigned x)) by (apply bv_eq; rewrite u64_lit by (pose proof (u64_range x); lia); reflexivity);
      cbn in Hx; apply HS; lia
    end.
Qed.

Definition aef_region : list (word * Z) := [(Z_to_bv 64 AEF_CB, 1)].

Section FX.
Context {fx : FPState}.

Definition stops2 : list Z := [TR_MALLOC; TR_CALLHEAD; TR_LLVM; TR_EMIT; TR_FREE; TR_MAINRET; MEMCPY; EXITPC].

Definition tr_srf (f : nat -> option expr) : list expr :=
  map (fun i => match i with
     | 0 => ELit 0 | 2 => EAlu ALU_ADD (EVar 0) (ELit (-208)) | 3 => ELit 0x10800 | 4 => ELit 0x1006b8 | 20 => ELit INITIALIZED
     | _ => match f i with Some e => e | None => EVar (6 + i) end end)%nat (seq 0 32).

Definition main_srf (f : nat -> option expr) : list expr :=
  map (fun i => match i with
     | 0 => ELit 0 | 2 => EAlu ALU_ADD (EVar 0) (ELit (-128)) | 3 => ELit 0x10800 | 4 => ELit 0x1006b8
     | _ => match f i with Some e => e | None => EVar (6 + i) end end)%nat (seq 0 32).

Definition sr_K := Eval cbv in tr_srf (fun i => match i with 8 => Some (EVar 1) | 9 => Some (EVar 2) | 10 => Some (EVar 3) | 21 => Some (EVar 5) | _ => None end)%nat.

Definition sr_G := Eval cbv in tr_srf (fun i => match i with 8 => Some (EVar 1) | 18 => Some (EVar 3) | 21 => Some (EVar 5) | _ => None end)%nat.

Definition sr_L := Eval cbv in tr_srf (fun i => match i with 8 => Some (EVar 1) | 9 => Some (EVar 2) | 18 => Some (EVar 3) | 19 => Some (EVar 4) | 21 => Some (EVar 5)
                                                    | 22 => Some (ELit 0) | 23 => Some (ELit MINUS2) | _ => None end)%nat.

Definition sr_Q := Eval cbv in tr_srf (fun i => match i with 8 => Some (EVar 1) | 9 => Some (EVar 2) | 18 => Some (EVar 3) | 19 => Some (ELit 0) | 21 => Some (EVar 5)
                                                    | 22 => Some (ELit 0) | 23 => Some (ELit MINUS2) | _ => None end)%nat.

Definition sr_P := Eval cbv in tr_srf (fun i => match i with 8 => Some (EVar 1) | 9 => Some (EVar 2) | 10 => Some (ELit 0) | 18 => Some (EVar 3) | 19 => Some (EVar 4) | 21 => Some (EVar 5)
                                                    | 22 => Some (ELit 0) | 23 => Some (ELit MINUS2) | _ => None end)%nat.

Definition sr_X := Eval cbv in main_srf (fun i => match i with 8 => Some (EVar 1) | 9 => Some (EVar 2) | _ => None end)%nat.

Definition kn_base : list kentry := [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000; KRange (EVar 5) 0 4].

Definition kn_rw : list kentry := kn_base ++ [KWr (SA (ELit 0) 0xee000) 0x34000].
Definition kn_trf : list kentry := kn_base ++
  [KWord (SA (EVar 0) (-136)) 8 (ELit TR_MAINRET); KWord (SA (EVar 0) (-144)) 8 (EVar 38); KWord (SA (EVar 0) (-152)) 8 (EVar 39);
   KWord (SA (EVar 0) (-160)) 8 (EVar 40); KWord (SA (EVar 0) (-168)) 8 (EVar 41); KWord (SA (EVar 0) (-176)) 8 (EVar 42);
   KWord (SA (EVar 0) (-184)) 8 (EVar 43); KWord (SA (EVar 0) (-192)) 8 (EVar 44); KWord (SA (EVar 0) (-200)) 8 (EVar 45)].
Definition kn_mf : list kentry := kn_base ++
  [KWord (SA (EVar 0) (-56)) 8 (ELit 0xcfab0); KWord (SA (EVar 0) (-64)) 8 (EAlu ALU_ADD (EVar 0) (ELit 8)); KWord (SA (EVar 0) (-72)) 8 (ELit 2);
   KWord (SA (EVar 0) (-80)) 8 (ELit 0x655e8); KWord (SA (EVar 0) (-88)) 8 (EAlu ALU_ADD (EVar 0) (ELit 32)); KWord (SA (EVar 0) (-96)) 8 (ELit 0);
   KWord (SA (EVar 0) (-104)) 8 (ELit 0); KWord (SA (EVar 0) (-112)) 8 (ELit 0); KWord (SA (EVar 0) (-120)) 8 (ELit 0)].

Definition runB (dirs : list bool) (pc : Z) (sr : list expr) (kn : list kentry) :=
  sym_exec RSEGS 300 true stops2 (SCR dirs [] []) (SS pc sr [] kn 50) [].

Definition ssK := Eval vm_compute in fst (fst (runB [false] RET_MALLOC sr_K kn_base)).
Lemma rK_eq : sym_exec RSEGS 300 true stops2 (SCR [false] [] []) (SS RET_MALLOC sr_K [] kn_base 50) []
              = (ssK, [SCBr false BC_EQ (EVar 3) (ELit 0)], snd (runB [false] RET_MALLOC sr_K kn_base)).
Proof. vm_compute. reflexivity. Qed.
Definition ssG := Eval vm_compute in fst (fst (runB [] RET_MEMCPY sr_G kn_base)).
Lemma rG_eq : sym_exec RSEGS 300 true stops2 (SCR [] [] []) (SS RET_MEMCPY sr_G [] kn_base 50) []
              = (ssG, [], snd (runB [] RET_MEMCPY sr_G kn_base)).
Proof. vm_compute. reflexivity. Qed.
Definition ssL := Eval vm_compute in fst (fst (runB [] TR_CALLHEAD sr_L kn_rw)).
Lemma rL_eq : sym_exec RSEGS 300 true stops2 (SCR [] [] []) (SS TR_CALLHEAD sr_L [] kn_rw 50) []
              = (ssL, [], snd (runB [] TR_CALLHEAD sr_L kn_rw)).
Proof. vm_compute. reflexivity. Qed.
Definition knL' := Eval vm_compute in fst (fst (carry (s_log ssL) kn_rw [])).
Lemma cL_eq : carry (s_log ssL) kn_rw [] = (knL', [], snd (carry (s_log ssL) kn_rw [])). Proof. vm_compute. reflexivity. Qed.
Definition ssP := Eval vm_compute in fst (fst (runB [] RET_LLVM sr_P kn_rw)).
Lemma rP_eq : sym_exec RSEGS 300 true stops2 (SCR [] [] []) (SS RET_LLVM sr_P [] kn_rw 50) []
              = (ssP, [], snd (runB [] RET_LLVM sr_P kn_rw)).
Proof. vm_compute. reflexivity. Qed.
Definition knP' := Eval vm_compute in fst (fst (carry (s_log ssP) kn_rw [])).
Lemma cP_eq : carry (s_log ssP) kn_rw [] = (knP', [], snd (carry (s_log ssP) kn_rw [])). Proof. vm_compute. reflexivity. Qed.
Definition ssQt := Eval vm_compute in fst (fst (runB [true] RET_EMIT sr_Q kn_base)).
Lemma rQt_eq : sym_exec RSEGS 300 true stops2 (SCR [true] [] []) (SS RET_EMIT sr_Q [] kn_base 50) []
              = (ssQt, [SCBr true BC_NE (EAluw ALU_ADD (EVar 5) (ELit (-1))) (ELit 0)], snd (runB [true] RET_EMIT sr_Q kn_base)).
Proof. vm_compute. reflexivity. Qed.
Definition ssQf := Eval vm_compute in fst (fst (runB [false] RET_EMIT sr_Q kn_base)).
Lemma rQf_eq : sym_exec RSEGS 300 true stops2 (SCR [false] [] []) (SS RET_EMIT sr_Q [] kn_base 50) []
              = (ssQf, [SCBr false BC_NE (EAluw ALU_ADD (EVar 5) (ELit (-1))) (ELit 0)], snd (runB [false] RET_EMIT sr_Q kn_base)).
Proof. vm_compute. reflexivity. Qed.
Definition ssR := Eval vm_compute in fst (fst (runB [] RET_FREE sr_L kn_trf)).
Lemma rR_eq : sym_exec RSEGS 300 true stops2 (SCR [] [] []) (SS RET_FREE sr_L [] kn_trf 50) []
              = (ssR, [], snd (runB [] RET_FREE sr_L kn_trf)).
Proof. vm_compute. reflexivity. Qed.
Definition ssX := Eval vm_compute in fst (fst (runB [] MAIN_JOIN sr_X kn_base)).
Lemma rX_eq : sym_exec RSEGS 300 true stops2 (SCR [] [] []) (SS MAIN_JOIN sr_X [] kn_base 50) []
              = (ssX, [], snd (runB [] MAIN_JOIN sr_X kn_base)).
Proof. vm_compute. reflexivity. Qed.
Definition ssY := Eval vm_compute in fst (fst (runB [] RET_FREE_MAIN sr_X kn_mf)).
Lemma rY_eq : sym_exec RSEGS 300 true stops2 (SCR [] [] []) (SS RET_FREE_MAIN sr_X [] kn_mf 50) []
              = (ssY, [], snd (runB [] RET_FREE_MAIN sr_X kn_mf)).
Proof. vm_compute. reflexivity. Qed.

Lemma rK_pc : s_pc ssK = MEMCPY /\ s_log ssK = []. Proof. split; reflexivity. Qed.
Lemma rG_pc : s_pc ssG = TR_CALLHEAD /\ s_log ssG = []. Proof. split; reflexivity. Qed.
Lemma rL_pc : s_pc ssL = TR_LLVM. Proof. reflexivity. Qed.
Lemma rL_cov : log_covered [(SA (ELit 0) AEF_CB, 1)] (s_log ssL) = true. Proof. vm_compute. reflexivity. Qed.
Lemma rP_pc : s_pc ssP = TR_EMIT. Proof. reflexivity. Qed.
Lemma rP_cov : log_covered [(SA (ELit 0) AEF_CB, 1)] (s_log ssP) = true. Proof. vm_compute. reflexivity. Qed.
Lemma rQt_pc : s_pc ssQt = TR_CALLHEAD /\ s_log ssQt = []. Proof. split; reflexivity. Qed.
Lemma rQf_pc : s_pc ssQf = TR_FREE /\ s_log ssQf = []. Proof. split; reflexivity. Qed.
Lemma rR_pc : s_pc ssR = TR_MAINRET /\ s_log ssR = []. Proof. split; reflexivity. Qed.
Lemma rX_pc : s_pc ssX = TR_FREE /\ s_log ssX = []. Proof. split; reflexivity. Qed.
Lemma rY_pc : s_pc ssY = EXITPC /\ s_log ssY = []. Proof. split; reflexivity. Qed.
End FX.

Section Blocks.
  Context {fx : FPState}.
  Variables (R : bvmap 5 word) (M rom : word -> option byte).
  Variables (sp0 v1 v2 v3 v4 v5 : Z) (w38 w39 w40 w41 w42 w43 w44 w45 : word).
  Hypothesis Hsp : 0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0.
  Hypothesis Hv1 : 0 <= v1 < 2 ^ 64.
  Hypothesis Hv2 : 0 <= v2 < 2 ^ 64.
  Hypothesis Hv3 : 0 <= v3 < 2 ^ 64.
  Hypothesis Hv4 : 0 <= v4 < 2 ^ 64.
  Hypothesis Hv5 : 0 <= v5 <= 4.
  Hypothesis R3 : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis R4 : getr R 4 = Z_to_bv 64 0x1006b8.

  Definition bvals : list word :=
    [Z_to_bv 64 sp0; Z_to_bv 64 v1; Z_to_bv 64 v2; Z_to_bv 64 v3; Z_to_bv 64 v4; Z_to_bv 64 v5]
      ++ junk_vals R ++ [w38; w39; w40; w41; w42; w43; w44; w45].
  Definition bE : env := Env (vals_ev bvals) (blobs_ev []).

  Ltac evl := lazy [bE edenot ev eb vals_ev bvals junk_vals blobs_ev nth app map seq length Nat.add].
  Tactic Notation "evl" "in" hyp(H) := lazy [bE edenot ev eb vals_ev bvals junk_vals blobs_ev nth app map seq length Nat.add] in H.

  Ltac regs_ok_tac sr :=
    apply regs_ok_by_idx; intros i Hi;
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sr allregs32]; evl; unfold INITIALIZED, MINUS2;
      first [ apply getr_zero | assumption
            | rewrite alu_add_ZZ; lazymatch goal with H : getr R 2%bv = _ |- _ => rewrite H; f_equal; lia end
            | reflexivity ].

  Ltac kn_base_tac :=
    unfold kn_base; repeat apply Forall_cons; try apply Forall_nil;
    [ cbn [kentry_ok]; evl; rewrite u_small by lia; split; [lia | exact (proj2 Hsp)]
    | cbn [kentry_ok]; evl; rewrite u_small by lia; lia
    | cbn [kentry_ok]; evl; rewrite u_small by lia; lia ].

  Lemma kn_rw_ok : know_ok RSEGS bE M kn_rw.
  Proof.
    unfold kn_rw. apply Forall_app. split; [kn_base_tac|].
    apply Forall_cons; [|apply Forall_nil].
    cbn [kentry_ok a_base a_off]. unfold flat, estart. cbn [a_base a_off edenot].
    rewrite (u_small 0) by lia. split; [lia|]. intros d m Hd Hm.
    apply store_ok_of_all; [rewrite u_small by lia; lia|]. intros x Hx. rewrite u_small in Hx by lia.
    apply rw_wview_. lia.
  Qed.

  Lemma kword_frame : forall (o : Z) (e : expr) (v : word),
    o < 0 -> Z.abs o <= sp0 -> edenot bE e = v ->
    rdn RSEGS M (Z_to_bv 64 (sp0 - Z.abs o)) 8 = Some (word_to_le_bytes 8 v) ->
    kentry_ok RSEGS bE M (KWord (SA (EVar 0) o) 8 e).
  Proof.
    intros o e v Ho Ha He Hr. cbn [kentry_ok a_base a_off]. split; [lia|].
    unfold flat, estart, adenot. cbn [a_base a_off]. rewrite He.
    replace (edenot bE (EVar 0)) with (Z_to_bv 64 sp0) by (evl; reflexivity).
    rewrite (u_small sp0) by lia. split; [lia|]. unfold v_addi. rewrite (u_small sp0) by lia.
    replace (sp0 + o) with (sp0 - Z.abs o) by lia. exact Hr.
  Qed.

  Lemma kn_trf_ok : forall R0,
    tr_frame sp0 R0 M ->
    w38 = getr R0 8 -> w39 = getr R0 9 -> w40 = getr R0 18 -> w41 = getr R0 19 -> w42 = getr R0 20 -> w43 = getr R0 21 ->
    w44 = getr R0 22 -> w45 = getr R0 23 ->
    know_ok RSEGS bE M kn_trf.
  Proof.
    intros R0 FR E38 E39 E40 E41 E42 E43 E44 E45. unfold kn_trf. apply Forall_app. split; [kn_base_tac|].
    destruct FR. rewrite <- E38, <- E39, <- E40, <- E41, <- E42, <- E43, <- E44, <- E45 in *.
    repeat apply Forall_cons; try apply Forall_nil;
      (eapply kword_frame; [lia | cbn [Z.abs]; lia | evl; reflexivity | cbn [Z.abs]; assumption]).
  Qed.

  Lemma kn_mf_ok : main_frame sp0 M -> know_ok RSEGS bE M kn_mf.
  Proof.
    intros MF. unfold kn_mf. apply Forall_app. split; [kn_base_tac|].
    destruct MF as [F1 F2 F3 F4 F5 F6 F7 F8 F9]. unfold cell in *.
    repeat apply Forall_cons; try apply Forall_nil;
      (eapply kword_frame; [lia | cbn [Z.abs]; lia | evl; rewrite ?alu_add_ZZ; reflexivity | cbn [Z.abs]; assumption ]).
  Qed.

  Lemma dec_calls : 1 <= v5 -> edenot bE (EAluw ALU_ADD (EVar 5) (ELit (-1))) = Z_to_bv 64 (v5 - 1).
  Proof.
    intros Hv5a. cbn [edenot]. rewrite aluw_addi_lit. evl. apply bv_eq. rewrite v_addiw_range by (rewrite u_small by lia; lia).
    rewrite !u_small by lia. reflexivity.
  Qed.

  Ltac rv HRC := lazymatch goal with |- getr _ ?r = _ => regv HRC r end; rewrite ?dec_calls by lia; evl; unfold INITIALIZED, MINUS2, TR_MAINRET;
                 first [ reflexivity | assumption | rewrite alu_add_ZZ; f_equal; lia | f_equal; lia | idtac ].
  Ltac sames HR HRC := apply (fun Hs => same_regs_sound bE _ _ _ _ _ Hs HR HRC); vm_compute; reflexivity.

  Lemma aef_region_eq : map (rdenot bE) [(SA (ELit 0) AEF_CB, 1)] = aef_region.
  Proof. unfold aef_region, rdenot, estart. cbn [map fst snd a_base a_off]. evl. unfold AEF_CB. rewrite (u_small 0) by lia. reflexivity. Qed.
  Lemma aef_region_flat : regions_flat bE [(SA (ELit 0) AEF_CB, 1)].
  Proof. intros rg [<-|[]]. unfold flat, estart. cbn [fst snd a_base a_off]. evl. unfold AEF_CB. rewrite (u_small 0) by lia. lia. Qed.

  Lemma blk_K :
    getr R 2 = Z_to_bv 64 (sp0 - 208) -> getr R 8 = Z_to_bv 64 v1 -> getr R 9 = Z_to_bv 64 v2 ->
    getr R 10 = Z_to_bv 64 v3 -> getr R 20 = Z_to_bv 64 INITIALIZED -> getr R 21 = Z_to_bv 64 v5 ->
    v3 <> 0 ->
    exists R', msteps RSEGS (mkst R (Z_to_bv 64 RET_MALLOC) M rom) (mkst R' (Z_to_bv 64 MEMCPY) M rom)
      /\ getr R' 1 = Z_to_bv 64 RET_MEMCPY /\ getr R' 10 = Z_to_bv 64 v3 /\ getr R' 11 = Z_to_bv 64 v2
      /\ getr R' 12 = Z_to_bv 64 v1 /\ getr R' 18 = Z_to_bv 64 v3
      /\ (forall r, In r [2; 3; 4; 8; 9; 20; 21]%bv -> getr R' r = getr R r).
  Proof.
    intros R2 R8 R9 R10 R20 R21 Hnz.
    assert (HR : regs_ok bE sr_K R) by regs_ok_tac sr_K.
    assert (HK : know_ok RSEGS bE M kn_base) by kn_base_tac.
    destruct (run_sound RSEGS 300 stops2 (SCR [false] [] []) RET_MALLOC sr_K kn_base 50 ssK _ _ bE M rom R rK_eq HR HK
                ltac:(repeat apply Forall_cons; try apply Forall_nil; unfold sc_denot; evl; rewrite bt_eq0_Z by lia;
                      destruct (v3 =? 0) eqn:E3; [apply Z.eqb_eq in E3; lia | reflexivity]))
      as (RC & HRC & _ & Hms).
    rewrite (proj1 rK_pc), (proj2 rK_pc) in Hms. cbn [mem_denot] in Hms.
    exists RC. split; [exact Hms|]. repeat split; [ .. | sames HR HRC]; rv HRC.
  Qed.

  Lemma blk_G :
    getr R 2 = Z_to_bv 64 (sp0 - 208) -> getr R 8 = Z_to_bv 64 v1 -> getr R 18 = Z_to_bv 64 v3 ->
    getr R 20 = Z_to_bv 64 INITIALIZED -> getr R 21 = Z_to_bv 64 v5 ->
    exists R', msteps RSEGS (mkst R (Z_to_bv 64 RET_MEMCPY) M rom) (mkst R' (Z_to_bv 64 TR_CALLHEAD) M rom)
      /\ getr R' 9 = Z_to_bv 64 v3 /\ getr R' 22 = Z_to_bv 64 0 /\ getr R' 23 = Z_to_bv 64 MINUS2
      /\ (forall r, In r [2; 3; 4; 8; 18; 20; 21]%bv -> getr R' r = getr R r).
  Proof.
    intros R2 R8 R18 R20 R21.
    assert (HR : regs_ok bE sr_G R) by regs_ok_tac sr_G.
    assert (HK : know_ok RSEGS bE M kn_base) by kn_base_tac.
    destruct (run_sound RSEGS 300 stops2 (SCR [] [] []) RET_MEMCPY sr_G kn_base 50 ssG _ _ bE M rom R rG_eq HR HK ltac:(constructor))
      as (RC & HRC & _ & Hms).
    rewrite (proj1 rG_pc), (proj2 rG_pc) in Hms. cbn [mem_denot] in Hms.
    exists RC. split; [exact Hms|]. repeat split; [ .. | sames HR HRC]; rv HRC.
  Qed.

  Lemma blk_L :
    getr R 2 = Z_to_bv 64 (sp0 - 208) -> getr R 8 = Z_to_bv 64 v1 -> getr R 9 = Z_to_bv 64 v2 -> getr R 18 = Z_to_bv 64 v3 ->
    getr R 19 = Z_to_bv 64 v4 -> getr R 20 = Z_to_bv 64 INITIALIZED -> getr R 21 = Z_to_bv 64 v5 ->
    getr R 22 = Z_to_bv 64 0 -> getr R 23 = Z_to_bv 64 MINUS2 ->
    exists R' M', msteps RSEGS (mkst R (Z_to_bv 64 TR_CALLHEAD) M rom) (mkst R' (Z_to_bv 64 TR_LLVM) M' rom)
      /\ frame_mod M M' aef_region /\ cell M' AEF_CB 1 1
      /\ getr R' 1 = Z_to_bv 64 RET_LLVM /\ getr R' 10 = Z_to_bv 64 v2 /\ getr R' 11 = Z_to_bv 64 v1
      /\ (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R' r = getr R r).
  Proof.
    intros R2 R8 R9 R18 R19 R20 R21 R22 R23.
    assert (HR : regs_ok bE sr_L R) by regs_ok_tac sr_L.
    pose proof kn_rw_ok as HK.
    destruct (run_sound RSEGS 300 stops2 (SCR [] [] []) TR_CALLHEAD sr_L kn_rw 50 ssL _ _ bE M rom R rL_eq HR HK ltac:(constructor))
      as (RC & HRC & Hlf & Hms).
    rewrite rL_pc in Hms.
    pose proof (carry_after RSEGS bE M _ kn_rw [] _ _ _ cL_eq Hlf HK ltac:(constructor)) as HK'.
    set (M' := mem_denot bE M (s_log ssL)) in *.
    exists RC, M'. split; [exact Hms|]. split; [|split].
    - rewrite <- aef_region_eq. exact (log_covered_frame bE M _ _ rL_cov aef_region_flat Hlf).
    - unfold cell, AEF_CB. krd HK' 0xfe4f4%Z 1%nat H. exact H.
    - repeat split; [ .. | sames HR HRC]; rv HRC.
  Qed.

  Lemma blk_P :
    getr R 2 = Z_to_bv 64 (sp0 - 208) -> getr R 8 = Z_to_bv 64 v1 -> getr R 9 = Z_to_bv 64 v2 -> getr R 10 = Z_to_bv 64 0 ->
    getr R 18 = Z_to_bv 64 v3 -> getr R 19 = Z_to_bv 64 v4 -> getr R 20 = Z_to_bv 64 INITIALIZED -> getr R 21 = Z_to_bv 64 v5 ->
    getr R 22 = Z_to_bv 64 0 -> getr R 23 = Z_to_bv 64 MINUS2 ->
    exists R' M', msteps RSEGS (mkst R (Z_to_bv 64 RET_LLVM) M rom) (mkst R' (Z_to_bv 64 TR_EMIT) M' rom)
      /\ frame_mod M M' aef_region /\ cell M' AEF_CB 1 0
      /\ getr R' 1 = Z_to_bv 64 RET_EMIT /\ getr R' 10 = Z_to_bv 64 0 /\ getr R' 11 = Z_to_bv 64 0 /\ getr R' 19 = Z_to_bv 64 0
      /\ (forall r, In r [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R' r = getr R r).
  Proof.
    intros R2 R8 R9 R10 R18 R19 R20 R21 R22 R23.
    assert (HR : regs_ok bE sr_P R) by regs_ok_tac sr_P.
    pose proof kn_rw_ok as HK.
    destruct (run_sound RSEGS 300 stops2 (SCR [] [] []) RET_LLVM sr_P kn_rw 50 ssP _ _ bE M rom R rP_eq HR HK ltac:(constructor))
      as (RC & HRC & Hlf & Hms).
    rewrite rP_pc in Hms.
    pose proof (carry_after RSEGS bE M _ kn_rw [] _ _ _ cP_eq Hlf HK ltac:(constructor)) as HK'.
    set (M' := mem_denot bE M (s_log ssP)) in *.
    exists RC, M'. split; [exact Hms|]. split; [|split].
    - rewrite <- aef_region_eq. exact (log_covered_frame bE M _ _ rP_cov aef_region_flat Hlf).
    - unfold cell, AEF_CB. krd HK' 0xfe4f4%Z 1%nat H. exact H.
    - repeat split; [ .. | sames HR HRC]; rv HRC.
  Qed.

  Lemma blk_Qt :
    getr R 2 = Z_to_bv 64 (sp0 - 208) -> getr R 8 = Z_to_bv 64 v1 -> getr R 9 = Z_to_bv 64 v2 -> getr R 18 = Z_to_bv 64 v3 ->
    getr R 19 = Z_to_bv 64 0 -> getr R 20 = Z_to_bv 64 INITIALIZED -> getr R 21 = Z_to_bv 64 v5 ->
    getr R 22 = Z_to_bv 64 0 -> getr R 23 = Z_to_bv 64 MINUS2 ->
    1 < v5 ->
    exists R', msteps RSEGS (mkst R (Z_to_bv 64 RET_EMIT) M rom) (mkst R' (Z_to_bv 64 TR_CALLHEAD) M rom)
      /\ getr R' 21 = Z_to_bv 64 (v5 - 1)
      /\ (forall r, In r [2; 3; 4; 8; 9; 18; 20; 22; 23; 24; 25; 26; 27]%bv -> getr R' r = getr R r).
  Proof.
    intros R2 R8 R9 R18 R19 R20 R21 R22 R23 Hgt.
    assert (HR : regs_ok bE sr_Q R) by regs_ok_tac sr_Q.
    assert (HK : know_ok RSEGS bE M kn_base) by kn_base_tac.
    destruct (run_sound RSEGS 300 stops2 (SCR [true] [] []) RET_EMIT sr_Q kn_base 50 ssQt _ _ bE M rom R rQt_eq HR HK
                ltac:(repeat apply Forall_cons; try apply Forall_nil; unfold sc_denot; rewrite dec_calls by lia; cbn [edenot]; rewrite bt_ne0_Z by lia;
                      destruct (v5 - 1 =? 0) eqn:E5; [apply Z.eqb_eq in E5; lia | reflexivity]))
      as (RC & HRC & _ & Hms).
    rewrite (proj1 rQt_pc), (proj2 rQt_pc) in Hms. cbn [mem_denot] in Hms.
    exists RC. split; [exact Hms|]. repeat split; [ .. | sames HR HRC]; rv HRC.
  Qed.

  Lemma blk_Qf :
    getr R 2 = Z_to_bv 64 (sp0 - 208) -> getr R 8 = Z_to_bv 64 v1 -> getr R 9 = Z_to_bv 64 v2 -> getr R 18 = Z_to_bv 64 v3 ->
    getr R 19 = Z_to_bv 64 0 -> getr R 20 = Z_to_bv 64 INITIALIZED -> getr R 21 = Z_to_bv 64 v5 ->
    getr R 22 = Z_to_bv 64 0 -> getr R 23 = Z_to_bv 64 MINUS2 ->
    v5 = 1 ->
    exists R', msteps RSEGS (mkst R (Z_to_bv 64 RET_EMIT) M rom) (mkst R' (Z_to_bv 64 TR_FREE) M rom)
      /\ getr R' 1 = Z_to_bv 64 RET_FREE /\ getr R' 10 = Z_to_bv 64 v3 /\ getr R' 21 = Z_to_bv 64 0
      /\ (forall r, In r [2; 3; 4; 8; 9; 18; 20; 22; 23; 24; 25; 26; 27]%bv -> getr R' r = getr R r).
  Proof.
    intros R2 R8 R9 R18 R19 R20 R21 R22 R23 H1.
    assert (HR : regs_ok bE sr_Q R) by regs_ok_tac sr_Q.
    assert (HK : know_ok RSEGS bE M kn_base) by kn_base_tac.
    destruct (run_sound RSEGS 300 stops2 (SCR [false] [] []) RET_EMIT sr_Q kn_base 50 ssQf _ _ bE M rom R rQf_eq HR HK
                ltac:(repeat apply Forall_cons; try apply Forall_nil; unfold sc_denot; rewrite dec_calls by lia; cbn [edenot]; rewrite bt_ne0_Z by lia;
                      rewrite H1; reflexivity))
      as (RC & HRC & _ & Hms).
    rewrite (proj1 rQf_pc), (proj2 rQf_pc) in Hms. cbn [mem_denot] in Hms.
    exists RC. split; [exact Hms|]. repeat split; [ .. | sames HR HRC]; rv HRC.
  Qed.

  Lemma blk_R : forall R0,
    getr R 2 = Z_to_bv 64 (sp0 - 208) -> getr R 8 = Z_to_bv 64 v1 -> getr R 9 = Z_to_bv 64 v2 -> getr R 18 = Z_to_bv 64 v3 ->
    getr R 19 = Z_to_bv 64 v4 -> getr R 20 = Z_to_bv 64 INITIALIZED -> getr R 21 = Z_to_bv 64 v5 ->
    getr R 22 = Z_to_bv 64 0 -> getr R 23 = Z_to_bv 64 MINUS2 ->
    tr_frame sp0 R0 M ->
    w38 = getr R0 8 -> w39 = getr R0 9 -> w40 = getr R0 18 -> w41 = getr R0 19 -> w42 = getr R0 20 -> w43 = getr R0 21 ->
    w44 = getr R0 22 -> w45 = getr R0 23 ->
    exists R', msteps RSEGS (mkst R (Z_to_bv 64 RET_FREE) M rom) (mkst R' (Z_to_bv 64 TR_MAINRET) M rom)
      /\ getr R' 2 = Z_to_bv 64 (sp0 - 128) /\ getr R' 10 = Z_to_bv 64 0
      /\ getr R' 8 = getr R0 8 /\ getr R' 9 = getr R0 9 /\ getr R' 18 = getr R0 18 /\ getr R' 19 = getr R0 19
      /\ getr R' 20 = getr R0 20 /\ getr R' 21 = getr R0 21 /\ getr R' 22 = getr R0 22 /\ getr R' 23 = getr R0 23
      /\ (forall r, In r [3; 4; 24; 25; 26; 27]%bv -> getr R' r = getr R r).
  Proof.
    intros R0 R2 R8 R9 R18 R19 R20 R21 R22 R23 FR E38 E39 E40 E41 E42 E43 E44 E45.
    assert (HR : regs_ok bE sr_L R) by regs_ok_tac sr_L.
    pose proof (kn_trf_ok R0 FR E38 E39 E40 E41 E42 E43 E44 E45) as HK.
    destruct (run_sound RSEGS 300 stops2 (SCR [] [] []) RET_FREE sr_L kn_trf 50 ssR _ _ bE M rom R rR_eq HR HK ltac:(constructor))
      as (RC & HRC & _ & Hms).
    rewrite (proj1 rR_pc), (proj2 rR_pc) in Hms. cbn [mem_denot] in Hms.
    exists RC. split; [exact Hms|].
    repeat split; [ .. | sames HR HRC]; rv HRC; apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma blk_X :
    getr R 2 = Z_to_bv 64 (sp0 - 128) -> getr R 8 = Z_to_bv 64 v1 -> getr R 9 = Z_to_bv 64 v2 ->
    exists R', msteps RSEGS (mkst R (Z_to_bv 64 MAIN_JOIN) M rom) (mkst R' (Z_to_bv 64 TR_FREE) M rom)
      /\ getr R' 1 = Z_to_bv 64 RET_FREE_MAIN /\ getr R' 10 = Z_to_bv 64 v2
      /\ (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R' r = getr R r).
  Proof.
    intros R2 R8 R9.
    assert (HR : regs_ok bE sr_X R) by regs_ok_tac sr_X.
    assert (HK : know_ok RSEGS bE M kn_base) by kn_base_tac.
    destruct (run_sound RSEGS 300 stops2 (SCR [] [] []) MAIN_JOIN sr_X kn_base 50 ssX _ _ bE M rom R rX_eq HR HK ltac:(constructor))
      as (RC & HRC & _ & Hms).
    rewrite (proj1 rX_pc), (proj2 rX_pc) in Hms. cbn [mem_denot] in Hms.
    exists RC. split; [exact Hms|]. repeat split; [ .. | sames HR HRC]; rv HRC.
  Qed.

  Lemma blk_Y :
    getr R 2 = Z_to_bv 64 (sp0 - 128) -> getr R 8 = Z_to_bv 64 v1 -> getr R 9 = Z_to_bv 64 v2 ->
    main_frame sp0 M ->
    exists R', msteps RSEGS (mkst R (Z_to_bv 64 RET_FREE_MAIN) M rom) (mkst R' (Z_to_bv 64 EXITPC) M rom)
      /\ getr R' 2 = Z_to_bv 64 (sp0 - 48) /\ getr R' 4 = Z_to_bv 64 0x1006b8 /\ getr R' 10 = Z_to_bv 64 v1.
  Proof.
    intros R2 R8 R9 MF.
    assert (HR : regs_ok bE sr_X R) by regs_ok_tac sr_X.
    pose proof (kn_mf_ok MF) as HK.
    destruct (run_sound RSEGS 300 stops2 (SCR [] [] []) RET_FREE_MAIN sr_X kn_mf 50 ssY _ _ bE M rom R rY_eq HR HK ltac:(constructor))
      as (RC & HRC & _ & Hms).
    rewrite (proj1 rY_pc), (proj2 rY_pc) in Hms. cbn [mem_denot] in Hms.
    exists RC. split; [exact Hms|]. repeat split; rv HRC.
  Qed.
End Blocks.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
