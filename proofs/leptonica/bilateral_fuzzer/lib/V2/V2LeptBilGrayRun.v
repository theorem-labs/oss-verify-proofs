(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptRoom LeptSlots LeptExec LeptExecW LeptExecFP LeptExecX DitherLib DitherLoop LeptCmapArr LeptExecB LeptArithB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2_code_leptB4_bilg.
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

Ltac fr_keep2 :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Heq := fresh "Heq" in
  intros r Hr; apply fr_keep; apply fr_find_none;
  repeat (apply Forall_cons; [cbn [fst]; intro Heq; apply Hr; rewrite <- Heq; vm_compute; tauto |]); apply Forall_nil.

Ltac cell_goal HK Hlf regs :=
  let N := fresh "C" in
  lazymatch goal with
  | |- rdn _ _ (Z_to_bv 64 (?s - ?k)) 8 = Some (word_to_le_bytes 8 ?x) =>
      exB_cellw HK Hlf (EVar 32) (- k)%Z (s - k)%Z x N ltac:(exb_scs regs) ltac:(exB_tacA idtac) ltac:(exB_tacW); exact N
  | |- rdn _ _ (Z_to_bv 64 (?s - ?k)) ?n = Some (Z_to_le_bytes ?n ?z) =>
      exB_cell HK Hlf (EVar 32) (- k)%Z n (s - k)%Z z N ltac:(exb_scs regs) ltac:(exB_tacA idtac) ltac:(exB_tacV idtac); exact N
  end.

Ltac fr_lit := apply fr_get_lit; vm_compute; reflexivity.

Ltac gr_cvt pc r H :=
  let F := fresh "F" in let D := fresh "D" in
  ex_fetch SEGS pc F D;
  eapply reach_step;
    [ first [reflexivity | vm_compute; reflexivity]
    | eapply fpv_step_fcvt_f_of_x;
        [ exact F | vm_compute; reflexivity | exact D | left; split; reflexivity
        | right; left; split; [reflexivity | split; reflexivity] | assumption | first [exact fpv_rm_dyn | reflexivity] ]
    | ];
  apply reach_done; cbn [fp_regs fp_csr];
  lazymatch goal with |- context [getr ?regs ?r0] =>
    let E := fresh "E" in assert (E : r0 = r) by bveq; rewrite E, H end;
  eexists; split;
  [ lazymatch goal with |- @mkst (mkFP (bvmap_set ?rd ?x _) _) _ ?p _ _ = @mkst (mkFP (bvmap_set ?rd' ?x' _) _) _ ?p' _ _ =>
      replace rd with rd' by bveq; replace x with x' by bveq; replace p with p' by bveq; reflexivity end
  | apply fpv_frm_acc; assumption ].

Lemma gr_A1 : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pixs : Z),
  frm_zero cs ->
  (4096 + 64 <= s <= 2 ^ 47)%Z ->
  (4096 <= pixs)%Z ->
  (pixs mod 8 = 0)%Z ->
  (pixs + 64 <= s - 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (pixs + 48)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 8) ->
  store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 pixs ->
  getr regs 11 = Z_to_bv 64 10 ->
  getr regs 12 = Z_to_bv 64 1 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 ->
  reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 235128) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 235300) M' rom /\ frm_zero cs' /\
      rinv [((s - 64)%Z, 64%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 8)))) /\
      rdn SEGS M' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 9)))) /\
      getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 8 = Z_to_bv 64 1 /\ getr regs' 9 = Z_to_bv 64 10 /\ getr regs' 18 = Z_to_bv 64 pixs /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18]%list) regs regs' /\
      reg_get fr' 8 = Z_to_bv 64 18446744070507200512 /\ reg_get fr' 9 = Z_to_bv 64 18446744070498811904 /\ (forall r : reg, ~ In (ridx r) [8; 9]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s pixs FZ Hs Hp1 Hal Hp2 Rcm Rd SOK H2 H10 H11 H12 F10 F11.
  ex_entry regs [s; pixs; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)]) m
     [KWr (SA (EVar 32) (-64)) 64; KRange (EVar 32) 4160 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 8;
      KWord (SA (EVar 33) 48) 8 (ELit 0); KWord (SA (EVar 33) 8) 4 (ELit 8);
      KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-64)) 64]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 16%nat 800%nat [235300%Z] [(8%nat, 34%nat); (9%nat, 35%nat)] HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((s - 64)%Z, 64%Z)]; exB_reg_tac idtac|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ cell_goal HK Hlf regs | exB_reg regs HR' | ex_agree HR HR' | fr_lit | fr_keep2 ].
Qed.

Lemma gr_A1b : forall (fr : bvmap 5 word) cs regs (m : word -> option byte),
  frm_zero cs -> getr regs 8 = Z_to_bv 64 1 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 235300) m rom)
    (fun fin => exists cs', fin = @mkst (mkFP (bvmap_set 15%bv (Z_to_bv 64 18446744070479937536) fr) cs') regs (Z_to_bv 64 235304) m rom /\ frm_zero cs').
Proof.
  intros fr cs regs m FZ H8.
  gr_cvt 235300%Z (8%bv : bv 5) H8.
Qed.

Lemma gr_A2b : forall (fr : bvmap 5 word) cs regs (m : word -> option byte),
  frm_zero cs -> getr regs 9 = Z_to_bv 64 10 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 235552) m rom)
    (fun fin => exists cs', fin = @mkst (mkFP (bvmap_set 15%bv (Z_to_bv 64 18446744070507200512) fr) cs') regs (Z_to_bv 64 235556) m rom /\ frm_zero cs').
Proof.
  intros fr cs regs m FZ H9.
  gr_cvt 235552%Z (9%bv : bv 5) H9.
Qed.

Lemma gr_A2 : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s : Z),
  frm_zero cs ->
  (4096 + 64 <= s <= 2 ^ 47)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 64) ->
  getr regs 9 = Z_to_bv 64 10 ->
  reg_get fr 15 = Z_to_bv 64 18446744070479937536 ->
  reg_get fr 9 = Z_to_bv 64 18446744070498811904 ->
  reg_get fr 8 = Z_to_bv 64 18446744070507200512 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 235304) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 235552) M' rom /\ frm_zero cs' /\
      M' = m /\ regs_agree (fun r => In r [10; 11]%list) regs regs' /\ (forall r : reg, ~ In (ridx r) [14; 15]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s FZ Hs H2 H9 F15 F9 F8.
  ex_entry regs [(s - 64)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 64)%Z]) m []) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 4%nat 400%nat [235552%Z] (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [reflexivity|].
  split; [ex_agree HR HR' | fr_keep2].
Qed.

Lemma gr_A3 : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pixs : Z),
  frm_zero cs ->
  (4096 + 64 <= s <= 2 ^ 47)%Z ->
  (0 <= pixs < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 64) ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 9 = Z_to_bv 64 10 ->
  getr regs 18 = Z_to_bv 64 pixs ->
  reg_get fr 15 = Z_to_bv 64 18446744070507200512 ->
  reg_get fr 9 = Z_to_bv 64 18446744070498811904 ->
  reg_get fr 8 = Z_to_bv 64 18446744070507200512 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 235556) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 235748) M' rom /\ frm_zero cs' /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 235640 /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 10 /\
      getr regs' 12 = Z_to_bv 64 1 /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs' /\
      reg_get fr' 10 = Z_to_bv 64 18446744070498811904 /\ reg_get fr' 11 = Z_to_bv 64 18446744070507200512 /\ (forall r : reg, ~ In (ridx r) [10; 11; 14; 15]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s pixs FZ Hs Hp H2 H8 H9 H18 F15 F9 F8.
  ex_entry regs [(s - 64)%Z; pixs] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 64)%Z; pixs]) m []) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 4%nat 400%nat [235748%Z] (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR' | ex_agree HR HR' | (exB_fr_expr; reflexivity) | fr_lit | fr_keep2 ].
Qed.

Lemma gr_B : forall (fx : FPState) regs (m : word -> option byte) (s bil : Z),
  (4096 + 64 <= s <= 2 ^ 47)%Z ->
  (4096 <= bil < 2 ^ 47)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
  getr regs 2 = Z_to_bv 64 (s - 64) ->
  getr regs 10 = Z_to_bv 64 bil ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 235640) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 238988) M' rom /\
      rinv [((s - 56)%Z, 8%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 bil) /\
      getr regs' 1 = Z_to_bv 64 235652 /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 10 = Z_to_bv 64 bil /\ regs_agree (fun r => In r [1]%list) regs regs').
Proof.
  intros fx regs m s bil Hs Hb SOK H2 H10.
  destruct fx as [fr cs].
  ex_entry regs [s; bil] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bil]) m
     [KWr (SA (EVar 32) (-64)) 64; KRange (EVar 32) 4160 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47)]) by (ex_know regs).
  exb_open HR HK ST.
  exb_auto 8%nat 400%nat [238988%Z] HK ST.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((s - 56)%Z, 8%Z)]; exB_reg_tac idtac|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ cell_goal HK Hlf regs | exB_reg regs HR' | ex_agree HR HR' ].
Qed.

Lemma gr_C : forall (fx : FPState) regs (m : word -> option byte) (s r : Z),
  (4096 + 64 <= s <= 2 ^ 47)%Z ->
  (0 <= r < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 64) ->
  getr regs 10 = Z_to_bv 64 r ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 235652) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 240220) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 235664 /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 8 = Z_to_bv 64 r /\ getr regs' 10 = Z_to_bv 64 (s - 56) /\
      regs_agree (fun r => In r [1; 8; 10]%list) regs regs').
Proof.
  intros fx regs m s r0 Hs Hr H2 H10.
  destruct fx as [fr cs].
  ex_entry regs [s; r0] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; r0]) m [KRange (EVar 32) 4160 (2 ^ 47)]) by (ex_know regs).
  exb_open HR HK ST.
  exb_auto 8%nat 400%nat [240220%Z] HK ST.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ exB_reg regs HR' | ex_agree HR HR' ].
Qed.

Lemma gr_D : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s : Z) (ret : word) (v1 v8 v9 v18 g8 g9 : word),
  frm_zero cs ->
  (4096 + 64 <= s <= 2 ^ 47)%Z ->
  ret_ok ret ->
  v1 = ret ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 g8) ->
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 g9) ->
  getr regs 2 = Z_to_bv 64 (s - 64) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 235664) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' ret M' rom /\ frm_zero cs' /\
      M' = m /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = getr regs 8 /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 18]%list) regs regs' /\
      reg_get fr' 8 = g8 /\ reg_get fr' 9 = g9 /\ (forall r : reg, ~ In (ridx r) [8; 9]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s ret v1 v8 v9 v18 g8 g9 FZ Hs Hok Hv1 R1 R8 R9 R18 RG8 RG9 H2.
  subst v1.
  ex_entryL [ret; v8; v9; v18; g8; g9] regs [s] HR.
  assert (HK : know_ok SEGS (ex_envL [ret; v8; v9; v18; g8; g9] regs [s]) m
     [KWord (SA (EVar 38) (-8)) 8 (EVar 0); KWord (SA (EVar 38) (-16)) 8 (EVar 1); KWord (SA (EVar 38) (-24)) 8 (EVar 2);
      KWord (SA (EVar 38) (-32)) 8 (EVar 3); KWord (SA (EVar 38) (-40)) 8 (EVar 4); KWord (SA (EVar 38) (-48)) 8 (EVar 5)]) by (ex_know regs).
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

Lemma gr_Bn : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s : Z) (v1 v8 v9 v18 g8 g9 : word),
  frm_zero cs ->
  (4096 + 64 <= s <= 2 ^ 47)%Z ->
  (487424 <= s - 64)%Z ->
  (forall j, (282176 <= j < 282336)%Z -> m (Z_to_bv 64 j) = None) ->
  (forall j, (286472 <= j < 286480)%Z -> m (Z_to_bv 64 j) = None) ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 g8) ->
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 g9) ->
  store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
  getr regs 2 = Z_to_bv 64 (s - 64) ->
  getr regs 10 = Z_to_bv 64 0 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 235640) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 97988) M' rom /\ frm_zero cs' /\
      rinv [((s - 56)%Z, 8%Z)] m M' /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 73322 /\ getr regs' 11 = Z_to_bv 64 68782 /\ getr regs' 12 = Z_to_bv 64 0 /\
      getr regs' 1 = v1 /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18]%list) regs regs' /\
      reg_get fr' 8 = g8 /\ reg_get fr' 9 = g9 /\ (forall r : reg, ~ In (ridx r) [8; 9]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s v1 v8 v9 v18 g8 g9 FZ Hs Hlo HG HV R1 R8 R9 R18 RG8 RG9 SOK H2 H10.
  ex_entryL [v1; v8; v9; v18; g8; g9] regs [s] HR.
  assert (HK : know_ok SEGS (ex_envL [v1; v8; v9; v18; g8; g9] regs [s]) m
     [KWr (SA (EVar 38) (-64)) 64; KImg 282176 282336; KImg 286472 286480;
      KWord (SA (EVar 38) (-8)) 8 (EVar 0); KWord (SA (EVar 38) (-16)) 8 (EVar 1); KWord (SA (EVar 38) (-24)) 8 (EVar 2);
      KWord (SA (EVar 38) (-32)) 8 (EVar 3); KWord (SA (EVar 38) (-40)) 8 (EVar 4); KWord (SA (EVar 38) (-48)) 8 (EVar 5)]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 8%nat 400%nat [97988%Z] (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((s - 56)%Z, 8%Z)]; exB_reg_tac idtac|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR' | ex_agree HR HR' | (exB_fr_expr; reflexivity) | fr_keep2 ].
Qed.
End Segs.
