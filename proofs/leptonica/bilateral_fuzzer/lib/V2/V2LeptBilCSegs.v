(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptRoom LeptSlots LeptExec LeptExecW LeptExecFP LeptExecX DitherLib DitherLoop LeptCmapArr LeptExecB LeptArithB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.
(* [comment removed for export] *)
#[local] Opaque RiscvSemantics.store_ok.

Section Segs.
Variable rom : word -> option byte.
#[local] Existing Instance exf_fxd | 100.

Lemma fr_keep : forall E L fr (r : reg), fr_find L (ridx r) = None -> reg_get (fr_denot E L fr) r = reg_get fr r.
Proof. intros E L fr r H. rewrite fr_get, H. reflexivity. Qed.

Lemma fr_find_none : forall L k, Forall (fun kv => ridx (fst kv) <> k) L -> fr_find L k = None.
Proof.
  induction L as [|[r e] L IH]; intros k H; [reflexivity|].
  inversion H as [|? ? H1 H2]; subst. cbn [fr_find].
  destruct (Nat.eqb (ridx r) k) eqn:E; [apply Nat.eqb_eq in E; contradiction | apply IH; exact H2].
Qed.

Ltac fr_val2 :=
  lazymatch goal with |- reg_get (fr_denot ?E ?L ?fr) ?r = reg_get ?fr ?r' =>
    let o := eval vm_compute in (fr_find L (ridx r)) in
    lazymatch o with Some ?e =>
      rewrite (fr_get_expr E L fr r e ltac:(vm_cast_no_check (eq_refl o)));
      transitivity (Z_to_bv 64 (bv_unsigned (reg_get fr r'))); [reflexivity | apply Z_to_bv_bv_unsigned] end end.

Ltac fr_keep2 :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Heq := fresh "Heq" in
  intros r Hr; apply fr_keep; apply fr_find_none;
  repeat (apply Forall_cons; [cbn [fst]; intro Heq; apply Hr; rewrite <- Heq; vm_compute; tauto |]); apply Forall_nil.

Ltac fsg_eq H :=
  rewrite fr_keep by (vm_cast_no_check (eq_refl (@None expr)));
  first [ exact H | (etransitivity; [|exact H]; f_equal; apply bv_eq; reflexivity) ].

Ltac fsg_hyp ST H1 H2 :=
  lazymatch type of ST with
  | ex_st ?segs ?E ?m ?rom ?ms0 (mkFP (fr_denot _ ?L ?fr) ?cs) ?pc ?sr ?log =>
    let F := fresh "F" in let D := fresh "D" in let ST' := fresh "ST" in
    ex_fetch segs pc F D;
    lazymatch type of D with
    | decode_any ?w = Some (Fsgnj ?op ?fmt ?rd ?rs1 ?rs2, _) =>
      lazymatch type of H1 with reg_get _ _ = Z_to_bv 64 ?z1 =>
      lazymatch type of H2 with reg_get _ _ = Z_to_bv 64 ?z2 =>
      let zr := eval vm_compute in (bv_unsigned (fpv_sgnj op fmt (Z_to_bv 64 z1) (Z_to_bv 64 z2))) in
      pose proof (exb_fsgnj segs E L fr cs m rom pc sr log ms0 w op fmt rd rs1 rs2 (Z_to_bv 64 z1) (Z_to_bv 64 z2) zr ST F (eq_refl _) D
                    ltac:(fsg_eq H1) ltac:(fsg_eq H2) ltac:(apply bv_eq; vm_cast_no_check (eq_refl zr))) as ST';
      clear F D ST; rename ST' into ST
      end end
    end
  end.

Ltac cell_goal HK Hlf regs :=
  let N := fresh "C" in
  lazymatch goal with
  | |- rdn _ _ (Z_to_bv 64 (?s - ?k)) 8 = Some (word_to_le_bytes 8 ?x) =>
      exB_cellw HK Hlf (EVar 32) (- k)%Z (s - k)%Z x N ltac:(exb_scs regs) ltac:(exB_tacA idtac) ltac:(exB_tacW); exact N
  | |- rdn _ _ (Z_to_bv 64 (?s - ?k)) ?n = Some (Z_to_le_bytes ?n ?z) =>
      exB_cell HK Hlf (EVar 32) (- k)%Z n (s - k)%Z z N ltac:(exb_scs regs) ltac:(exB_tacA idtac) ltac:(exB_tacV idtac); exact N
  end.

Ltac fr_lit := apply fr_get_lit; vm_compute; reflexivity.

#[local] Ltac exf_closed E L fr r G cont ::=
  let o := eval vm_compute in (fr_find L (ridx r)) in
  lazymatch o with
  | Some (ELit ?z) =>
      assert (G : reg_get (fr_denot E L fr) r = Z_to_bv 64 z) by (apply fr_get_lit; vm_cast_no_check (eq_refl (Some (ELit z))));
      cont z
  | None =>
      let k := eval vm_compute in (ridx r) in
      match goal with H : reg_get fr ?r' = Z_to_bv 64 ?z |- _ =>
        let k' := eval vm_compute in (ridx r') in
        constr_eq k k';
        assert (G : reg_get (fr_denot E L fr) r = Z_to_bv 64 z)
          by (rewrite (fr_keep E L fr r ltac:(vm_cast_no_check (eq_refl (@None expr)))); rewrite <- H; f_equal; apply bv_eq; vm_compute; reflexivity);
        cont z
      end
  | _ => fail 100 "exf: FP register" r "does not hold a closed value:" o
  end.

Ltac g3_frlit :=
  lazymatch goal with |- reg_get (fr_denot ?E ?L ?fr) ?r = Z_to_bv 64 ?z =>
    apply (fr_get_lit E L fr r z); vm_cast_no_check (eq_refl (Some (ELit z))) end.


Lemma ag_keep : forall (L : list reg) regs regs' (r : reg) (v : word),
  regs_agree (fun x => In x L) regs regs' -> existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = false ->
  getr regs r = v -> getr regs' r = v.
Proof.
  intros L regs regs' r v AG E H. rewrite AG; [exact H|]. intros Hin.
  assert (T : existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = true).
  { apply existsb_exists. exists r. split; [exact Hin | apply Z.eqb_refl]. }
  congruence.
Qed.

Lemma ag_comp : forall (L1 L2 L : list reg) r1 r2 r3,
  regs_agree (fun x => In x L1) r1 r2 -> regs_agree (fun x => In x L2) r2 r3 ->
  forallb (fun x => existsb (fun y => Z.eqb (bv_unsigned y) (bv_unsigned x)) L) (L1 ++ L2) = true ->
  regs_agree (fun x => In x L) r1 r3.
Proof.
  intros L1 L2 L r1 r2 r3 A1 A2 B r Hr. rewrite forallb_forall in B.
  assert (IN : forall x, In x (L1 ++ L2) -> In x L).
  { intros x Hx. specialize (B x Hx). apply existsb_exists in B. destruct B as (y & Hy & E).
    apply Z.eqb_eq in E. apply bv_eq in E. subst. exact Hy. }
  rewrite A2, A1; [reflexivity | |].
  - intros Hin. apply Hr, IN, in_or_app. left. exact Hin.
  - intros Hin. apply Hr, IN, in_or_app. right. exact Hin.
Qed.

Ltac agk AG H := apply (ag_keep _ _ _ _ _ AG); [vm_compute; reflexivity | exact H].
Ltac agc A1 A2 := eapply ag_comp; [exact A1 | exact A2 | vm_compute; reflexivity].

Lemma bc_A1 : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pixs : Z),
  frm_zero cs -> (4096 + 320 <= s <= 2 ^ 47)%Z -> (4096 <= pixs)%Z -> (pixs + 64 <= s - 320)%Z -> (pixs mod 8 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
  store_ok SEGS m (Z_to_bv 64 (s - 320)) 320 = true -> store_ok SEGS m (Z_to_bv 64 (pixs + 20)) 4 = true ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 10 -> getr regs 12 = Z_to_bv 64 1 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 -> reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x398e4) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x3995c) M' rom /\ frm_zero cs' /\
      rinv [((s - 320)%Z, 320%Z); ((pixs + 20)%Z, 4%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) /\
      rdn SEGS M' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (getr regs 21)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (getr regs 22)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (getr regs 23)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 (getr regs 24)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 (getr regs 25)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (getr regs 26)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 (getr regs 27)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 8)))) /\
      rdn SEGS M' (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 9)))) /\
      rdn SEGS M' (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 18)))) /\
      rdn SEGS M' (Z_to_bv 64 (s - 288)) 8 = Some (Z_to_le_bytes 8 10) /\ rdn SEGS M' (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pixs) /\
      getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 22 = Z_to_bv 64 1 /\ getr regs' 24 = Z_to_bv 64 pixs /\ getr regs' 10 = Z_to_bv 64 pixs /\
      regs_agree (fun r => In r [1; 2; 10; 11; 12; 22; 24]%list) regs regs' /\
      reg_get fr' 8 = Z_to_bv 64 18446744070507200512 /\ reg_get fr' 9 = Z_to_bv 64 18446744070498811904 /\ (forall r : reg, ~ In (ridx r) [8; 9]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s pixs FZ Hs Hp1 Hp2 Hal R20 SOK SOKp H2 H10 H11 H12 F10 F11.
  ex_entry regs [s; pixs; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9); bv_unsigned (reg_get fr 18)] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9); bv_unsigned (reg_get fr 18)]) m
     [KWr (SA (EVar 32) (-320)) 320; KWr (SA (EVar 33) 20) 4;
      KRange (EVar 32) 4416 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 8;
      KWord (SA (EVar 33) 20) 4 (ELit 1);
      KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-320)) 320]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 40%nat 400%nat [0x3995c%Z] [(8%nat, 34%nat); (9%nat, 35%nat); (18%nat, 36%nat)] HK ST FZ.
  first [ exb_at_stop [0x3995c%Z] ST | exb_adrive 40%nat 400%nat [0x3995c%Z] [(8%nat, 34%nat); (9%nat, 35%nat); (18%nat, 36%nat)] HK ST FZ ].
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((s - 320)%Z, 320%Z); ((pixs + 20)%Z, 4%Z)]; exB_reg_tac idtac|].
  split.
  { exB_cell HK Hlf (EVar 33) 20%Z 4%nat (pixs + 20)%Z 2%Z Hc idtac idtac idtac.
    - exB_scs regs.
    - exB_tacA idtac.
    - exB_tacV idtac.
    - exact Hc. }
  repeat match goal with |- _ /\ _ => split end.
  all: first [ cell_goal HK Hlf regs | exB_reg regs HR' | ex_agree HR HR' | fr_lit | g3_frlit | fr_keep2 ].
Qed.

Lemma bc_A1b : forall (fr : bvmap 5 word) cs regs (m : word -> option byte),
  frm_zero cs -> getr regs 22 = Z_to_bv 64 1 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3995c) m rom)
    (fun fin => exists cs', fin = @mkst (mkFP (bvmap_set 15%bv (Z_to_bv 64 0xffffffff3f800000) fr) cs') regs (Z_to_bv 64 0x39960) m rom /\ frm_zero cs').
Proof.
  intros fr cs regs m FZ H22.
  ex_fetch SEGS 0x3995c%Z F D.
  eapply reach_step; [reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F | vm_compute; reflexivity | exact D | left; split; reflexivity | left; repeat split; reflexivity | exact FZ | vm_compute; reflexivity] |].
  cbn [fp_regs fp_csr].
  lazymatch goal with
  | |- reach _ (@mkst (mkFP (bvmap_set ?rd ?v fr) ?c) regs ?pc m rom) _ =>
      apply reach_done; exists c; split; [| apply fpv_frm_acc; exact FZ];
      replace v with (Z_to_bv 64 0xffffffff3f800000)
        by (match goal with |- context [getr regs ?x] => change (getr regs x) with (getr regs 22%bv) end; rewrite H22;
            apply bv_eq; vm_compute; reflexivity);
      replace pc with (Z_to_bv 64 0x39960) by (apply bv_eq; vm_compute; reflexivity);
      replace rd with (15%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity); reflexivity
  end.
Qed.

Lemma bc_A2 : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pixs : Z),
  frm_zero cs ->
  (4096 + 320 <= s <= 2 ^ 47)%Z ->
  (0 <= pixs < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 0x127ac) 4 = Some (Z_to_le_bytes 4 0xcf000001) ->
  store_ok SEGS m (Z_to_bv 64 (s - 320)) 320 = true ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  getr regs 10 = Z_to_bv 64 pixs ->
  reg_get fr 15 = Z_to_bv 64 0xffffffff3f800000 ->
  reg_get fr 9 = Z_to_bv 64 18446744070498811904 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x39960) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 115776) M' rom /\ frm_zero cs' /\
      rinv [((s - 272)%Z, 8%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (s - 272)) 8 = Some (Z_to_le_bytes 8 11) /\
      getr regs' 1 = Z_to_bv 64 0x399b0 /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 11 /\
      getr regs' 12 = Z_to_bv 64 11 /\ getr regs' 13 = Z_to_bv 64 11 /\ getr regs' 14 = Z_to_bv 64 11 /\
      regs_agree (fun r => In r [1; 11; 12; 13; 14]%list) regs regs' /\
      reg_get fr' 9 = Z_to_bv 64 18446744070498811904 /\ (forall r : reg, ~ In (ridx r) [9; 13; 14; 15]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s pixs FZ Hs Hp RF SOK H2 H10 F15 F9.
  ex_entry regs [s; pixs] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs]) m
     [KWr (SA (EVar 32) (-320)) 320; KWord (SA (ELit 0) 0x127ac) 4 (ELit 0xcf000001); KRange (EVar 32) 4416 (2 ^ 47)]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 40%nat 400%nat [115776%Z] (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((s - 272)%Z, 8%Z)]; exB_reg_tac idtac|].
  split; [cell_goal HK Hlf regs|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ exB_reg regs HR' | ex_agree HR HR' | fr_lit | g3_frlit | fr_keep2 ].
Qed.

Lemma ridx_ne : forall (r q : reg), ridx r <> ridx q -> r <> q.
Proof. intros r q H E. subst. apply H. reflexivity. Qed.

Ltac notin_nat := let X := fresh "X" in intro X; vm_compute in X; repeat (destruct X as [X|X]; [discriminate X|]); exact X.

Ltac rd_keep RI :=
  lazymatch goal with
  | |- rdn _ ?M (Z_to_bv 64 ?z) ?n = _ =>
      rewrite (rinv_rdn SEGS _ _ M z n RI) by (lia || (intros r Hr; cbn [In] in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; lia|]); destruct Hr))
  end.

Lemma bc_A : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pixs : Z),
  frm_zero cs -> (4096 + 320 <= s <= 2 ^ 47)%Z -> (4096 <= pixs)%Z -> (pixs + 64 <= s - 320)%Z -> (pixs mod 8 = 0)%Z ->
  (forall j, (0x127ac <= j < 0x127ac + 4)%Z -> m (Z_to_bv 64 j) = None) ->
  (0x77000 <= s - 320)%Z -> (pixs + 64 <= 0x10000 \/ 0x77000 <= pixs)%Z ->
  rdn SEGS m (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
  store_ok SEGS m (Z_to_bv 64 (s - 320)) 320 = true -> store_ok SEGS m (Z_to_bv 64 (pixs + 20)) 4 = true ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 10 -> getr regs 12 = Z_to_bv 64 1 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 -> reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x398e4) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 115776) M' rom /\ frm_zero cs' /\
      rinv [((s - 320)%Z, 320%Z); ((pixs + 20)%Z, 4%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) /\
      rdn SEGS M' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (getr regs 21)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (getr regs 22)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (getr regs 23)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 (getr regs 24)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 (getr regs 25)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (getr regs 26)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 (getr regs 27)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 8)))) /\
      rdn SEGS M' (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 9)))) /\
      rdn SEGS M' (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 18)))) /\
      rdn SEGS M' (Z_to_bv 64 (s - 288)) 8 = Some (Z_to_le_bytes 8 10) /\ rdn SEGS M' (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pixs) /\
      rdn SEGS M' (Z_to_bv 64 (s - 272)) 8 = Some (Z_to_le_bytes 8 11) /\
      getr regs' 1 = Z_to_bv 64 0x399b0 /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 11 /\
      getr regs' 12 = Z_to_bv 64 11 /\ getr regs' 13 = Z_to_bv 64 11 /\ getr regs' 14 = Z_to_bv 64 11 /\
      getr regs' 22 = Z_to_bv 64 1 /\ getr regs' 24 = Z_to_bv 64 pixs /\
      regs_agree (fun r => In r [1; 2; 10; 11; 12; 13; 14; 22; 24]%list) regs regs' /\
      reg_get fr' 8 = Z_to_bv 64 18446744070507200512 /\ reg_get fr' 9 = Z_to_bv 64 18446744070498811904 /\ (forall r : reg, ~ In (ridx r) [8; 9; 13; 14; 15]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s pixs FZ Hs Hp1 Hp2 Hal HI Himg Hpi R20 SOK SOKp H2 H10 H11 H12 F10 F11.
  eapply reach_bind; [exact (bc_A1 fr cs regs m s pixs FZ Hs Hp1 Hp2 Hal R20 SOK SOKp H2 H10 H11 H12 F10 F11)|].
  intros fin1 (fr1 & cs1 & r1 & M1 & -> & FZ1 & RI1 & C20 & S1 & S8 & S9 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27
               & SF8 & SF9 & SF18 & C288 & C160 & G2 & G22 & G24 & G10 & AG1 & E8 & E9 & EK1).
  eapply reach_bind; [exact (bc_A1b fr1 cs1 r1 M1 FZ1 G22)|].
  intros fin2 (cs2 & -> & FZ2).
  assert (HI1 : forall j, (0x127ac <= j < 0x127ac + 4)%Z -> M1 (Z_to_bv 64 j) = None).
  { intros j Hj. destruct RI1 as [_ RI1']. rewrite RI1'; [apply HI; exact Hj|].
    intros r Hr. cbn [In] in Hr. unfold inreg. rewrite u_Z2bv by lia.
    repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; lia|]); destruct Hr. }
  assert (RF1 : rdn SEGS M1 (Z_to_bv 64 0x127ac) 4 = Some (Z_to_le_bytes 4 0xcf000001)).
  { rewrite (rdn_untouched SEGS M1 0x127ac 4) by (first [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact HI1]).
    vm_refl_bv. }
  assert (SOK1 : store_ok SEGS M1 (Z_to_bv 64 (s - 320)) 320 = true) by (apply (store_ok_mono SEGS 320 m M1); [exact (proj1 RI1) | exact SOK]).
  eapply reach_weaken; [|exact (bc_A2 (bvmap_set 15%bv (Z_to_bv 64 0xffffffff3f800000) fr1) cs2 r1 M1 s pixs FZ2 Hs ltac:(lia) RF1 SOK1 G2 G10
                                   (fpv_get_same fr1 15%bv _) ltac:(rewrite fpv_get_other by (apply ridx_ne; vm_compute; discriminate); exact E9))].
  intros fin (fr3 & cs3 & r3 & M3 & -> & FZ3 & RI3 & C272 & K1 & K2 & K10 & K11 & K12 & K13 & K14 & AG3 & E39 & EK3).
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ3|].
  split.
  { eapply rinv_trans; [exact RI1|]. eapply rinv_weaken; [exact RI3|].
    intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. exists ((s - 320)%Z, 320%Z). split; [left; reflexivity|]. cbn [fst snd]. lia. }
  repeat match goal with |- _ /\ _ => split end.
  all: try (rd_keep RI3; first [exact C20 | exact C288 | exact C160 | assumption]).
  all: try exact C272.
  all: try (first [exact K1 | exact K2 | exact K10 | exact K11 | exact K12 | exact K13 | exact K14]).
  all: try (first [agk AG3 G22 | agk AG3 G24]).
  - agc AG1 AG3.
  - rewrite EK3 by notin_nat. rewrite fpv_get_other by (apply ridx_ne; vm_compute; discriminate). exact E8.
  - exact E39.
  - intros r Hr. rewrite EK3 by (intro X; apply Hr; cbn [In] in *; tauto).
    rewrite fpv_get_other by (apply ridx_ne; intro X; apply Hr; rewrite X; vm_compute; repeat (first [left; reflexivity | right])).
    apply EK1. intro X; apply Hr; cbn [In] in *; tauto.
Qed.

Lemma bc_B : forall (fx : FPState) regs (m : word -> option byte) (s pixs bsc : Z),
  (4096 + 320 <= s <= 2 ^ 47)%Z ->
  (0 <= pixs < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pixs) ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  (0 <= bsc < 2 ^ 64)%Z ->
  getr regs 10 = Z_to_bv 64 bsc ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x399b0) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 125864) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 0x399d8 /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 1 /\
      getr regs' 12 = Z_to_bv 64 4 /\ getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 14 = Z_to_bv 64 0 /\ getr regs' 15 = Z_to_bv 64 0 /\
      getr regs' 16 = Z_to_bv 64 (s - 148) /\ getr regs' 9 = Z_to_bv 64 bsc /\
      regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 14; 15; 16]%list) regs regs').
Proof.
  intros fx regs m s pixs bsc Hs Hp R160 H2 Hb H10.
  ex_entry regs [s; pixs; bsc] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs; bsc]) m [KWord (SA (EVar 32) (-160)) 8 (EVar 33)]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [125864%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.

Lemma bc_C : forall (fx : FPState) regs (m : word -> option byte) (s pixs : Z),
  (4096 + 320 <= s <= 2 ^ 47)%Z ->
  (0 <= pixs < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pixs) ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x399d8) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 125864) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 0x399fc /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 1 /\
      getr regs' 12 = Z_to_bv 64 5 /\ getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 14 = Z_to_bv 64 0 /\ getr regs' 15 = Z_to_bv 64 0 /\
      getr regs' 16 = Z_to_bv 64 (s - 152) /\ getr regs' 8 = Z_to_bv 64 5 /\
      regs_agree (fun r => In r [1; 8; 10; 11; 12; 13; 14; 15; 16]%list) regs regs').
Proof.
  intros fx regs m s pixs Hs Hp R160 H2.
  ex_entry regs [s; pixs] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs]) m [KWord (SA (EVar 32) (-160)) 8 (EVar 33)]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [125864%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.

Lemma bc_D : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pixs bsc : Z),
  frm_zero cs ->
  (4096 + 320 + 32 <= s <= 2 ^ 47)%Z ->
  (s mod 16 = 0)%Z ->
  (4096 <= pixs)%Z ->
  (pixs + 64 <= s - 352)%Z ->
  (pixs mod 8 = 0)%Z ->
  (4096 <= bsc < 2 ^ 47)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pixs) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
  store_ok SEGS m (Z_to_bv 64 (s - 352)) 352 = true ->
  store_ok SEGS m (Z_to_bv 64 (pixs + 20)) 4 = true ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  getr regs 9 = Z_to_bv 64 bsc ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x399fc) m rom)
    (fun fin => exists regs' M', fin = @mkst (mkFP fr cs) regs' (Z_to_bv 64 0x3c0f8) M' rom /\
      rinv [((s - 352)%Z, 32%Z); ((s - 160)%Z, 8%Z); ((s - 296)%Z, 8%Z); ((pixs + 20)%Z, 4%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 1) /\
      rdn SEGS M' (Z_to_bv 64 (s - 296)) 8 = Some (Z_to_le_bytes 8 bsc) /\
      getr regs' 1 = Z_to_bv 64 0x39a18 /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 104 /\
      regs_agree (fun r => In r [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%list) regs regs').
Proof.
  intros fr cs regs m s pixs bsc FZ Hs Hs16 Hp1 Hp2 Hal Hb R160 R20 SOK SOKp H2 H9.
  ex_entry regs [s; pixs; bsc] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs; bsc]) m
     [KWr (SA (EVar 32) (-352)) 352; KWr (SA (EVar 33) 20) 4;
      KRange (EVar 32) 4448 (2 ^ 47); KAlign (EVar 32) 16; KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 8;
      KRange (EVar 34) 4096 (2 ^ 47);
      KWord (SA (EVar 32) (-160)) 8 (EVar 33); KWord (SA (EVar 33) 20) 4 (ELit 2);
      KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-352)) 352]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 8%nat 400%nat [0x3c0f8%Z] (@nil (nat * nat)) HK ST FZ.
  first [ exb_at_stop [0x3c0f8%Z] ST | exb_adrive 8%nat 400%nat [0x3c0f8%Z] (@nil (nat * nat)) HK ST FZ ].
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((s - 352)%Z, 32%Z); ((s - 160)%Z, 8%Z); ((s - 296)%Z, 8%Z); ((pixs + 20)%Z, 4%Z)]; exB_reg_tac idtac|].
  split.
  { exB_cell HK Hlf (EVar 33) 20%Z 4%nat (pixs + 20)%Z 1%Z Hc idtac idtac idtac.
    - exB_scs regs.
    - exB_tacA idtac.
    - exB_tacV idtac.
    - exact Hc. }
  split.
  { exB_cell HK Hlf (EVar 32) (-296)%Z 8%nat (s - 296)%Z bsc Hc idtac idtac idtac.
    - exB_scs regs.
    - exB_tacA idtac.
    - exB_tacV idtac.
    - exact Hc. }
  repeat match goal with |- _ /\ _ => split end.
  all: first [ exB_reg regs HR' | ex_agree HR HR' ].
Qed.

Lemma bc_Dn : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pixs : Z),
  frm_zero cs ->
  (4096 + 320 + 32 <= s <= 2 ^ 47)%Z ->
  (s mod 16 = 0)%Z ->
  (4096 <= pixs)%Z ->
  (pixs + 64 <= s - 352)%Z ->
  (pixs mod 8 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pixs) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
  (forall j, (0x44e98 <= j < 0x44e98 + 8)%Z -> m (Z_to_bv 64 j) = None) ->
  (forall j, (0x45f08 <= j < 0x45f08 + 4)%Z -> m (Z_to_bv 64 j) = None) ->
  (0x77000 <= s - 352)%Z ->
  (pixs + 64 <= 0x10000 \/ 0x77000 <= pixs)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 352)) 352 = true ->
  store_ok SEGS m (Z_to_bv 64 (pixs + 20)) 4 = true ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  getr regs 9 = Z_to_bv 64 0 ->
  getr regs 8 = Z_to_bv 64 5 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x399fc) m rom)
    (fun fin => exists regs' M', fin = @mkst (mkFP fr cs) regs' (Z_to_bv 64 0x17ec4) M' rom /\
      rinv [((s - 352)%Z, 32%Z); ((s - 160)%Z, 8%Z); ((s - 296)%Z, 8%Z); ((pixs + 20)%Z, 4%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 1) /\
      getr regs' 1 = Z_to_bv 64 0x39cc4 /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 10 = Z_to_bv 64 0x12528 /\ getr regs' 11 = Z_to_bv 64 0x10a26 /\
      getr regs' 12 = Z_to_bv 64 0 /\
      regs_agree (fun r => In r [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%list) regs regs').
Proof.
  intros fr cs regs m s pixs FZ Hs Hs16 Hp1 Hp2 Hal R160 R20 HG HV Himg Hpi SOK SOKp H2 H9 H8.
  ex_entry regs [s; pixs] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs]) m
     [KWr (SA (EVar 32) (-352)) 352; KWr (SA (EVar 33) 20) 4; KImg 0x44e98 (0x44e98 + 8); KImg 0x45f08 (0x45f08 + 4);
      KRange (EVar 32) 4448 (2 ^ 47); KAlign (EVar 32) 16; KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 8;
      KWord (SA (EVar 32) (-160)) 8 (EVar 33); KWord (SA (EVar 33) 20) 4 (ELit 2);
      KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-352)) 352]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 8%nat 400%nat [0x17ec4%Z] (@nil (nat * nat)) HK ST FZ.
  first [ exb_at_stop [0x17ec4%Z] ST | exb_adrive 8%nat 400%nat [0x17ec4%Z] (@nil (nat * nat)) HK ST FZ ].
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((s - 352)%Z, 32%Z); ((s - 160)%Z, 8%Z); ((s - 296)%Z, 8%Z); ((pixs + 20)%Z, 4%Z)]; exB_reg_tac idtac|].
  split.
  { exB_cell HK Hlf (EVar 33) 20%Z 4%nat (pixs + 20)%Z 1%Z Hc idtac idtac idtac.
    - exB_scs regs.
    - exB_tacA idtac.
    - exB_tacV idtac.
    - exact Hc. }
  repeat match goal with |- _ /\ _ => split end.
  all: first [ exB_reg regs HR' | ex_agree HR HR' ].
Qed.

Lemma bc_U : forall (fx : FPState) regs (m : word -> option byte) (s bil pa : Z),
  (4096 + 320 <= s <= 2 ^ 47)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 320)%Z ->
  (0 <= pa < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 304)) 8 = Some (Z_to_le_bytes 8 bil) ->
  rdn SEGS m (Z_to_bv 64 (s - 312)) 8 = Some (Z_to_le_bytes 8 pa) ->
  store_ok SEGS m (Z_to_bv 64 bil) 104 = true ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x3a528) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x18d08) M' rom /\
      rinv [((bil + 88)%Z, 8%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (bil + 88)) 8 = Some (Z_to_le_bytes 8 pa) /\
      getr regs' 1 = Z_to_bv 64 0x3a53c /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 8 = Z_to_bv 64 bil /\ getr regs' 10 = Z_to_bv 64 pa /\
      getr regs' 11 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [1; 8; 10; 11]%list) regs regs').
Proof.
  intros fx regs m s bil pa Hs Hb1 Hb2 Hpa R16 R8 SOK H2.
  ex_entry regs [s; bil; pa] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bil; pa]) m
     [KWord (SA (EVar 32) (-304)) 8 (EVar 33); KWord (SA (EVar 32) (-312)) 8 (EVar 34); KWr (SA (EVar 33) 0) 104;
      KRange (EVar 33) 4096 (2 ^ 47)]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [0x18d08%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((bil + 88)%Z, 8%Z)]; exB_reg_tac idtac|].
  split.
  { exB_cell HK Hlf (EVar 33) 88%Z 8%nat (bil + 88)%Z pa Hc idtac idtac idtac.
    - exB_scs regs.
    - exB_tacA idtac.
    - exB_tacV idtac.
    - exact Hc. }
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.

Lemma bc_V : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s bil ls : Z) (ret : word) (v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 g8 g9 g18 : word),
  frm_zero cs ->
  (4096 + 320 <= s <= 2 ^ 47)%Z ->
  ret_ok ret ->
  v1 = ret ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 320)%Z ->
  (0 <= ls < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 bil) 104 = true ->
  getr regs 8 = Z_to_bv 64 bil ->
  getr regs 10 = Z_to_bv 64 ls ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v20) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v21) ->
  rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v22) ->
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v23) ->
  rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v24) ->
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 v25) ->
  rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 v26) ->
  rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 v27) ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 g8) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 g9) ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 g18) ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a53c) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' ret M' rom /\ frm_zero cs' /\
      rinv [((bil + 96)%Z, 8%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (bil + 96)) 8 = Some (Z_to_le_bytes 8 ls) /\ getr regs' 10 = Z_to_bv 64 bil /\
      getr regs' 2 = Z_to_bv 64 s /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\ getr regs' 21 = v21 /\ getr regs' 22 = v22 /\ getr regs' 23 = v23 /\ getr regs' 24 = v24 /\ getr regs' 25 = v25 /\ getr regs' 26 = v26 /\ getr regs' 27 = v27 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs' /\
      reg_get fr' 8 = g8 /\ reg_get fr' 9 = g9 /\ reg_get fr' 18 = g18 /\ (forall r : reg, ~ In (ridx r) [8; 9; 18]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s bil ls ret v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 g8 g9 g18 FZ Hs Hok Hv1 Hb1 Hb2 Hls SOK H8 H10
    R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 RG8 RG9 RG18 H2.
  subst v1.
  ex_entryL [ret; v8; v9; v18; v19; v20; v21; v22; v23; v24; v25; v26; v27; g8; g9; g18] regs [s; bil; ls] HR.
  assert (HK : know_ok SEGS (ex_envL [ret; v8; v9; v18; v19; v20; v21; v22; v23; v24; v25; v26; v27; g8; g9; g18] regs [s; bil; ls]) m
     [KWord (SA (EVar 48) (-8)) 8 (EVar 0); KWord (SA (EVar 48) (-16)) 8 (EVar 1); KWord (SA (EVar 48) (-24)) 8 (EVar 2);
      KWord (SA (EVar 48) (-32)) 8 (EVar 3); KWord (SA (EVar 48) (-40)) 8 (EVar 4); KWord (SA (EVar 48) (-48)) 8 (EVar 5);
      KWord (SA (EVar 48) (-56)) 8 (EVar 6); KWord (SA (EVar 48) (-64)) 8 (EVar 7); KWord (SA (EVar 48) (-72)) 8 (EVar 8);
      KWord (SA (EVar 48) (-80)) 8 (EVar 9); KWord (SA (EVar 48) (-88)) 8 (EVar 10); KWord (SA (EVar 48) (-96)) 8 (EVar 11);
      KWord (SA (EVar 48) (-104)) 8 (EVar 12); KWord (SA (EVar 48) (-112)) 8 (EVar 13); KWord (SA (EVar 48) (-120)) 8 (EVar 14);
      KWord (SA (EVar 48) (-128)) 8 (EVar 15);
      KWr (SA (EVar 49) 0) 104; KRange (EVar 49) 4096 (2 ^ 47); KRange (EVar 48) 4416 (2 ^ 47);
      KDisj (SA (EVar 49) 0) 104 (SA (EVar 48) (-128)) 128]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 4%nat 400%nat [0%Z] (@nil (nat * nat)) HK ST FZ.
  exb_ret ST ret (eq_refl ret) Hok R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((bil + 96)%Z, 8%Z)]; exB_reg_tac idtac|].
  split.
  { exB_cell HK Hlf (EVar 49) 96%Z 8%nat (bil + 96)%Z ls Hc idtac idtac idtac.
    - exB_scs regs.
    - exB_tacA idtac.
    - exB_tacV idtac.
    - exact Hc. }
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR' | ex_agree HR HR' | (exB_fr_expr; reflexivity) | fr_keep2 ].
Qed.

Lemma bc_Vn : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s : Z) (ret : word) (v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 g8 g9 g18 : word),
  frm_zero cs ->
  (4096 + 320 <= s <= 2 ^ 47)%Z ->
  ret_ok ret ->
  v1 = ret ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v20) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v21) ->
  rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v22) ->
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v23) ->
  rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v24) ->
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 v25) ->
  rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 v26) ->
  rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 v27) ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 g8) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 g9) ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 g18) ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x39cc4) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' ret M' rom /\ frm_zero cs' /\
      M' = m /\
      getr regs' 2 = Z_to_bv 64 s /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\ getr regs' 21 = v21 /\ getr regs' 22 = v22 /\ getr regs' 23 = v23 /\ getr regs' 24 = v24 /\ getr regs' 25 = v25 /\ getr regs' 26 = v26 /\ getr regs' 27 = v27 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs' /\
      reg_get fr' 8 = g8 /\ reg_get fr' 9 = g9 /\ reg_get fr' 18 = g18 /\ (forall r : reg, ~ In (ridx r) [8; 9; 18]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s ret v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 g8 g9 g18 FZ Hs Hok Hv1
    R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 RG8 RG9 RG18 H2.
  subst v1.
  ex_entryL [ret; v8; v9; v18; v19; v20; v21; v22; v23; v24; v25; v26; v27; g8; g9; g18] regs [s] HR.
  assert (HK : know_ok SEGS (ex_envL [ret; v8; v9; v18; v19; v20; v21; v22; v23; v24; v25; v26; v27; g8; g9; g18] regs [s]) m
     [KWord (SA (EVar 48) (-8)) 8 (EVar 0); KWord (SA (EVar 48) (-16)) 8 (EVar 1); KWord (SA (EVar 48) (-24)) 8 (EVar 2);
      KWord (SA (EVar 48) (-32)) 8 (EVar 3); KWord (SA (EVar 48) (-40)) 8 (EVar 4); KWord (SA (EVar 48) (-48)) 8 (EVar 5);
      KWord (SA (EVar 48) (-56)) 8 (EVar 6); KWord (SA (EVar 48) (-64)) 8 (EVar 7); KWord (SA (EVar 48) (-72)) 8 (EVar 8);
      KWord (SA (EVar 48) (-80)) 8 (EVar 9); KWord (SA (EVar 48) (-88)) 8 (EVar 10); KWord (SA (EVar 48) (-96)) 8 (EVar 11);
      KWord (SA (EVar 48) (-104)) 8 (EVar 12); KWord (SA (EVar 48) (-112)) 8 (EVar 13); KWord (SA (EVar 48) (-120)) 8 (EVar 14);
      KWord (SA (EVar 48) (-128)) 8 (EVar 15)]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 4%nat 400%nat [0%Z] (@nil (nat * nat)) HK ST FZ.
  exb_ret ST ret (eq_refl ret) Hok R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR' | ex_agree HR HR' | (exB_fr_expr; reflexivity) | fr_keep2 ].
Qed.

End Segs.
