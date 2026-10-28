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

Lemma pbl_N : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s : Z),
  frm_zero cs ->
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (487424 <= s - 112)%Z ->
  (forall j, (282176 <= j < 282336)%Z -> m (Z_to_bv 64 j) = None) ->
  (forall j, (286472 <= j < 286480)%Z -> m (Z_to_bv 64 j) = None) ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 0 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 ->
  reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 234140) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 97988) M' rom /\ frm_zero cs' /\
      rinv [((s - 112)%Z, 112%Z)] m M' /\
      getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 73294 /\ getr regs' 11 = Z_to_bv 64 72715 /\ getr regs' 12 = Z_to_bv 64 0 /\
      getr regs' 1 = getr regs 1 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20]%list) regs regs' /\
      reg_get fr' 8 = reg_get fr 8 /\ reg_get fr' 9 = reg_get fr 9 /\ (forall r : reg, ~ In (ridx r) [8; 9]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s FZ Hs Himg HG HV SOK H2 H10 F10 F11.
  ex_entry regs [s; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)]) m
     [KWr (SA (EVar 32) (-112)) 112; KImg 282176 282336; KImg 286472 286480]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 4%nat 400%nat [97988%Z] [(8%nat, 33%nat); (9%nat, 34%nat)] HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((s - 112)%Z, 112%Z)]; exB_reg_tac idtac|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR' | ex_agree HR HR' | fr_val2 | fr_keep2 ].
Qed.

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

Lemma pbl_CM : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pixs cm : Z),
  frm_zero cs ->
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (4096 <= pixs)%Z ->
  (pixs + 64 <= s - 112)%Z ->
  (pixs mod 8 = 0)%Z ->
  (1 <= cm < 2 ^ 64)%Z ->
  (487424 <= s - 112)%Z ->
  (forall j, (282176 <= j < 282336)%Z -> m (Z_to_bv 64 j) = None) ->
  (forall j, (286472 <= j < 286480)%Z -> m (Z_to_bv 64 j) = None) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 48)) 8 = Some (Z_to_le_bytes 8 cm) ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 pixs ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 ->
  reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 234140) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 97988) M' rom /\ frm_zero cs' /\
      rinv [((s - 112)%Z, 112%Z)] m M' /\
      getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 73294 /\ getr regs' 11 = Z_to_bv 64 72715 /\ getr regs' 12 = Z_to_bv 64 0 /\
      getr regs' 1 = getr regs 1 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20]%list) regs regs' /\
      reg_get fr' 8 = reg_get fr 8 /\ reg_get fr' 9 = reg_get fr 9 /\ (forall r : reg, ~ In (ridx r) [8; 9]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s pixs cm FZ Hs Hp1 Hp2 Hal Hcm Hlo HG HV Rcm SOK H2 H10 F10 F11.
  ex_entry regs [s; pixs; cm; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs; cm; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)]) m
     [KWr (SA (EVar 32) (-112)) 112; KImg 282176 282336; KImg 286472 286480;
      KRange (EVar 32) 4208 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 8;
      KWord (SA (EVar 33) 48) 8 (EVar 34); KRange (EVar 34) 1 (2 ^ 64 - 1);
      KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-112)) 112]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 4%nat 400%nat [234188%Z] [(8%nat, 35%nat); (9%nat, 36%nat)] HK ST FZ.
  fsg_hyp ST F11 F11.
  fsg_hyp ST F10 F10.
  exb_adrive 8%nat 400%nat [97988%Z] [(8%nat, 35%nat); (9%nat, 36%nat)] HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((s - 112)%Z, 112%Z)]; exB_reg_tac idtac|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR' | ex_agree HR HR' | fr_val2 | fr_keep2 ].
Qed.

Lemma pbl_D : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pixs w h d : Z),
  frm_zero cs ->
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (s mod 16 = 0)%Z ->
  (4096 <= pixs)%Z ->
  (pixs + 64 <= s - 112)%Z ->
  (pixs mod 8 = 0)%Z ->
  (0 <= w < 2 ^ 31)%Z ->
  (0 <= h < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (pixs + 48)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 d) ->
  rdn SEGS m (Z_to_bv 64 pixs) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
  (1 <= d < 2 ^ 31)%Z ->
  (d <> 8)%Z ->
  (d <> 32)%Z ->
  (487424 <= s - 112)%Z ->
  (forall j, (282176 <= j < 282336)%Z -> m (Z_to_bv 64 j) = None) ->
  (forall j, (286472 <= j < 286480)%Z -> m (Z_to_bv 64 j) = None) ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 pixs ->
  getr regs 11 = Z_to_bv 64 10 ->
  getr regs 12 = Z_to_bv 64 1 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 ->
  reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 234140) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 97988) M' rom /\ frm_zero cs' /\
      rinv [((s - 112)%Z, 112%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 8)))) /\
      rdn SEGS M' (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 9)))) /\
      rdn SEGS M' (Z_to_bv 64 (s - 68)) 4 = Some (Z_to_le_bytes 4 w) /\ rdn SEGS M' (Z_to_bv 64 (s - 72)) 4 = Some (Z_to_le_bytes 4 h) /\ rdn SEGS M' (Z_to_bv 64 (s - 76)) 4 = Some (Z_to_le_bytes 4 d) /\
      getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 8 = Z_to_bv 64 pixs /\ getr regs' 9 = Z_to_bv 64 1 /\ getr regs' 18 = Z_to_bv 64 10 /\
      getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20 /\
      getr regs' 1 = Z_to_bv 64 234768 /\ getr regs' 10 = Z_to_bv 64 71263 /\ getr regs' 11 = Z_to_bv 64 72715 /\ getr regs' 12 = Z_to_bv 64 0 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list) regs regs' /\
      reg_get fr' 8 = Z_to_bv 64 18446744070507200512 /\ reg_get fr' 9 = Z_to_bv 64 18446744070498811904 /\ (forall r : reg, ~ In (ridx r) [8; 9]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s pixs w h d FZ Hs Hs16 Hp1 Hp2 Hal Hw Hh Rcm Rd Rw Rh Hd Hd8 Hd32 Hlo HG HV SOK H2 H10 H11 H12 F10 F11.
  ex_entry regs [s; pixs; w; h; d; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs; w; h; d; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)]) m
     [KWr (SA (EVar 32) (-112)) 112; KImg 282176 282336; KImg 286472 286480;
      KRange (EVar 32) 4208 (2 ^ 47); KAlign (EVar 32) 16; KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 8;
      KWord (SA (EVar 33) 48) 8 (ELit 0); KWord (SA (EVar 33) 0) 4 (EVar 34); KWord (SA (EVar 33) 4) 4 (EVar 35);
      KWord (SA (EVar 33) 8) 4 (EVar 36);
      KRange (EVar 34) 0 (2 ^ 31 - 1); KRange (EVar 35) 0 (2 ^ 31 - 1); KRange (EVar 36) 1 (2 ^ 31 - 1);
      KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-112)) 112]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 4%nat 400%nat [234188%Z] [(8%nat, 37%nat); (9%nat, 38%nat)] HK ST FZ.
  fsg_hyp ST F11 F11.
  fsg_hyp ST F10 F10.
  exb_adrive 8%nat 400%nat [234316%Z] [(8%nat, 37%nat); (9%nat, 38%nat)] HK ST FZ.
  exb_adriveS 8%nat 400%nat [234324%Z] (SCR [false] [] []) [(8%nat, 37%nat); (9%nat, 38%nat)] HK ST FZ.
  exb_adriveS 8%nat 400%nat [97988%Z] (SCR [true] [] []) [(8%nat, 37%nat); (9%nat, 38%nat)] HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((s - 112)%Z, 112%Z)]; exB_reg_tac idtac|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ cell_goal HK Hlf regs | exB_reg regs HR' | ex_agree HR HR' | fr_val2 | fr_lit | fr_keep2 ].
Qed.

Lemma pbl_Ww_8 : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pixs w h d : Z),
  frm_zero cs ->
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (s mod 16 = 0)%Z ->
  (4096 <= pixs)%Z ->
  (pixs + 64 <= s - 112)%Z ->
  (pixs mod 8 = 0)%Z ->
  (0 <= w < 2 ^ 31)%Z ->
  (0 <= h < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (pixs + 48)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 d) ->
  rdn SEGS m (Z_to_bv 64 pixs) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
  (d = 8)%Z ->
  (0 <= w <= 21)%Z ->
  (0 <= h < 2 ^ 31)%Z ->
  (487424 <= s - 112)%Z ->
  (forall j, (282176 <= j < 282336)%Z -> m (Z_to_bv 64 j) = None) ->
  (forall j, (286472 <= j < 286480)%Z -> m (Z_to_bv 64 j) = None) ->
  (forall j, (73728 <= j < 77824)%Z -> m (Z_to_bv 64 j) = None) ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 pixs ->
  getr regs 11 = Z_to_bv 64 10 ->
  getr regs 12 = Z_to_bv 64 1 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 ->
  reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 234140) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 97832) M' rom /\ frm_zero cs' /\
      rinv [((s - 112)%Z, 112%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 8)))) /\
      rdn SEGS M' (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 9)))) /\
      rdn SEGS M' (Z_to_bv 64 (s - 68)) 4 = Some (Z_to_le_bytes 4 w) /\ rdn SEGS M' (Z_to_bv 64 (s - 72)) 4 = Some (Z_to_le_bytes 4 h) /\ rdn SEGS M' (Z_to_bv 64 (s - 76)) 4 = Some (Z_to_le_bytes 4 d) /\
      getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 8 = Z_to_bv 64 pixs /\ getr regs' 9 = Z_to_bv 64 1 /\ getr regs' 18 = Z_to_bv 64 10 /\
      getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20 /\
      getr regs' 1 = Z_to_bv 64 234600 /\ getr regs' 10 = Z_to_bv 64 69395 /\ getr regs' 11 = Z_to_bv 64 72715 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list) regs regs' /\
      reg_get fr' 8 = Z_to_bv 64 18446744070507200512 /\ reg_get fr' 9 = Z_to_bv 64 18446744070498811904 /\ (forall r : reg, ~ In (ridx r) [8; 9; 11; 12; 13; 14; 15]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s pixs w h d FZ Hs Hs16 Hp1 Hp2 Hal Hw0 Hh0 Rcm Rd Rw Rh Hd Hw Hh Hlo HI1 HI2 HI3 SOK H2 H10 H11 H12 F10 F11.
  subst d.
  ex_entry regs [s; pixs; w; h; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs; w; h; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)]) m
     [KWr (SA (EVar 32) (-112)) 112; KImg 73728 77824; KImg 282176 282336; KImg 286472 286480;
      KRange (EVar 32) 4208 (2 ^ 47); KAlign (EVar 32) 16; KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 8;
      KWord (SA (EVar 33) 48) 8 (ELit 0); KWord (SA (EVar 33) 0) 4 (EVar 34); KWord (SA (EVar 33) 4) 4 (EVar 35);
      KWord (SA (EVar 33) 8) 4 (ELit 8);
      KRange (EVar 34) 0 21; KRange (EVar 35) 0 (2 ^ 31 - 1);
      KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-112)) 112]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 4%nat 400%nat [234188%Z] [(8%nat, 36%nat); (9%nat, 37%nat)] HK ST FZ.
  fsg_hyp ST F11 F11.
  fsg_hyp ST F10 F10.
  exb_adrive 16%nat 800%nat [97832%Z] [(8%nat, 36%nat); (9%nat, 37%nat)] HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((s - 112)%Z, 112%Z)]; exB_reg_tac idtac|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ cell_goal HK Hlf regs | exB_reg regs HR' | ex_agree HR HR' | fr_val2 | fr_lit | fr_keep2 ].
Qed.

Lemma pbl_Wh_8 : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pixs w h d : Z),
  frm_zero cs ->
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (s mod 16 = 0)%Z ->
  (4096 <= pixs)%Z ->
  (pixs + 64 <= s - 112)%Z ->
  (pixs mod 8 = 0)%Z ->
  (0 <= w < 2 ^ 31)%Z ->
  (0 <= h < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (pixs + 48)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 d) ->
  rdn SEGS m (Z_to_bv 64 pixs) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
  (d = 8)%Z ->
  (22 <= w < 2 ^ 31)%Z ->
  (0 <= h <= 21)%Z ->
  (487424 <= s - 112)%Z ->
  (forall j, (282176 <= j < 282336)%Z -> m (Z_to_bv 64 j) = None) ->
  (forall j, (286472 <= j < 286480)%Z -> m (Z_to_bv 64 j) = None) ->
  (forall j, (73728 <= j < 77824)%Z -> m (Z_to_bv 64 j) = None) ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 pixs ->
  getr regs 11 = Z_to_bv 64 10 ->
  getr regs 12 = Z_to_bv 64 1 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 ->
  reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 234140) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 97832) M' rom /\ frm_zero cs' /\
      rinv [((s - 112)%Z, 112%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 8)))) /\
      rdn SEGS M' (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 9)))) /\
      rdn SEGS M' (Z_to_bv 64 (s - 68)) 4 = Some (Z_to_le_bytes 4 w) /\ rdn SEGS M' (Z_to_bv 64 (s - 72)) 4 = Some (Z_to_le_bytes 4 h) /\ rdn SEGS M' (Z_to_bv 64 (s - 76)) 4 = Some (Z_to_le_bytes 4 d) /\
      getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 8 = Z_to_bv 64 pixs /\ getr regs' 9 = Z_to_bv 64 1 /\ getr regs' 18 = Z_to_bv 64 10 /\
      getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20 /\
      getr regs' 1 = Z_to_bv 64 234600 /\ getr regs' 10 = Z_to_bv 64 69395 /\ getr regs' 11 = Z_to_bv 64 72715 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list) regs regs' /\
      reg_get fr' 8 = Z_to_bv 64 18446744070507200512 /\ reg_get fr' 9 = Z_to_bv 64 18446744070498811904 /\ (forall r : reg, ~ In (ridx r) [8; 9; 11; 12; 13; 14; 15]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s pixs w h d FZ Hs Hs16 Hp1 Hp2 Hal Hw0 Hh0 Rcm Rd Rw Rh Hd Hw Hh Hlo HI1 HI2 HI3 SOK H2 H10 H11 H12 F10 F11.
  subst d.
  ex_entry regs [s; pixs; w; h; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs; w; h; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)]) m
     [KWr (SA (EVar 32) (-112)) 112; KImg 73728 77824; KImg 282176 282336; KImg 286472 286480;
      KRange (EVar 32) 4208 (2 ^ 47); KAlign (EVar 32) 16; KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 8;
      KWord (SA (EVar 33) 48) 8 (ELit 0); KWord (SA (EVar 33) 0) 4 (EVar 34); KWord (SA (EVar 33) 4) 4 (EVar 35);
      KWord (SA (EVar 33) 8) 4 (ELit 8);
      KRange (EVar 34) 22 (2 ^ 31 - 1); KRange (EVar 35) 0 21;
      KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-112)) 112]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 4%nat 400%nat [234188%Z] [(8%nat, 36%nat); (9%nat, 37%nat)] HK ST FZ.
  fsg_hyp ST F11 F11.
  fsg_hyp ST F10 F10.
  exb_adrive 16%nat 800%nat [97832%Z] [(8%nat, 36%nat); (9%nat, 37%nat)] HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((s - 112)%Z, 112%Z)]; exB_reg_tac idtac|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ cell_goal HK Hlf regs | exB_reg regs HR' | ex_agree HR HR' | fr_val2 | fr_lit | fr_keep2 ].
Qed.

Lemma pbl_Ww_32 : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pixs w h d : Z),
  frm_zero cs ->
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (s mod 16 = 0)%Z ->
  (4096 <= pixs)%Z ->
  (pixs + 64 <= s - 112)%Z ->
  (pixs mod 8 = 0)%Z ->
  (0 <= w < 2 ^ 31)%Z ->
  (0 <= h < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (pixs + 48)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 d) ->
  rdn SEGS m (Z_to_bv 64 pixs) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
  (d = 32)%Z ->
  (0 <= w <= 21)%Z ->
  (0 <= h < 2 ^ 31)%Z ->
  (487424 <= s - 112)%Z ->
  (forall j, (282176 <= j < 282336)%Z -> m (Z_to_bv 64 j) = None) ->
  (forall j, (286472 <= j < 286480)%Z -> m (Z_to_bv 64 j) = None) ->
  (forall j, (73728 <= j < 77824)%Z -> m (Z_to_bv 64 j) = None) ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 pixs ->
  getr regs 11 = Z_to_bv 64 10 ->
  getr regs 12 = Z_to_bv 64 1 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 ->
  reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 234140) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 97832) M' rom /\ frm_zero cs' /\
      rinv [((s - 112)%Z, 112%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 8)))) /\
      rdn SEGS M' (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 9)))) /\
      rdn SEGS M' (Z_to_bv 64 (s - 68)) 4 = Some (Z_to_le_bytes 4 w) /\ rdn SEGS M' (Z_to_bv 64 (s - 72)) 4 = Some (Z_to_le_bytes 4 h) /\ rdn SEGS M' (Z_to_bv 64 (s - 76)) 4 = Some (Z_to_le_bytes 4 d) /\
      getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 8 = Z_to_bv 64 pixs /\ getr regs' 9 = Z_to_bv 64 1 /\ getr regs' 18 = Z_to_bv 64 10 /\
      getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20 /\
      getr regs' 1 = Z_to_bv 64 234600 /\ getr regs' 10 = Z_to_bv 64 69395 /\ getr regs' 11 = Z_to_bv 64 72715 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list) regs regs' /\
      reg_get fr' 8 = Z_to_bv 64 18446744070507200512 /\ reg_get fr' 9 = Z_to_bv 64 18446744070498811904 /\ (forall r : reg, ~ In (ridx r) [8; 9; 11; 12; 13; 14; 15]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s pixs w h d FZ Hs Hs16 Hp1 Hp2 Hal Hw0 Hh0 Rcm Rd Rw Rh Hd Hw Hh Hlo HI1 HI2 HI3 SOK H2 H10 H11 H12 F10 F11.
  subst d.
  ex_entry regs [s; pixs; w; h; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs; w; h; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)]) m
     [KWr (SA (EVar 32) (-112)) 112; KImg 73728 77824; KImg 282176 282336; KImg 286472 286480;
      KRange (EVar 32) 4208 (2 ^ 47); KAlign (EVar 32) 16; KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 8;
      KWord (SA (EVar 33) 48) 8 (ELit 0); KWord (SA (EVar 33) 0) 4 (EVar 34); KWord (SA (EVar 33) 4) 4 (EVar 35);
      KWord (SA (EVar 33) 8) 4 (ELit 32);
      KRange (EVar 34) 0 21; KRange (EVar 35) 0 (2 ^ 31 - 1);
      KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-112)) 112]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 4%nat 400%nat [234188%Z] [(8%nat, 36%nat); (9%nat, 37%nat)] HK ST FZ.
  fsg_hyp ST F11 F11.
  fsg_hyp ST F10 F10.
  exb_adrive 16%nat 800%nat [97832%Z] [(8%nat, 36%nat); (9%nat, 37%nat)] HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((s - 112)%Z, 112%Z)]; exB_reg_tac idtac|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ cell_goal HK Hlf regs | exB_reg regs HR' | ex_agree HR HR' | fr_val2 | fr_lit | fr_keep2 ].
Qed.

Lemma pbl_Wh_32 : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pixs w h d : Z),
  frm_zero cs ->
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (s mod 16 = 0)%Z ->
  (4096 <= pixs)%Z ->
  (pixs + 64 <= s - 112)%Z ->
  (pixs mod 8 = 0)%Z ->
  (0 <= w < 2 ^ 31)%Z ->
  (0 <= h < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (pixs + 48)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 d) ->
  rdn SEGS m (Z_to_bv 64 pixs) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
  (d = 32)%Z ->
  (22 <= w < 2 ^ 31)%Z ->
  (0 <= h <= 21)%Z ->
  (487424 <= s - 112)%Z ->
  (forall j, (282176 <= j < 282336)%Z -> m (Z_to_bv 64 j) = None) ->
  (forall j, (286472 <= j < 286480)%Z -> m (Z_to_bv 64 j) = None) ->
  (forall j, (73728 <= j < 77824)%Z -> m (Z_to_bv 64 j) = None) ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 pixs ->
  getr regs 11 = Z_to_bv 64 10 ->
  getr regs 12 = Z_to_bv 64 1 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 ->
  reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 234140) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 97832) M' rom /\ frm_zero cs' /\
      rinv [((s - 112)%Z, 112%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 8)))) /\
      rdn SEGS M' (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 9)))) /\
      rdn SEGS M' (Z_to_bv 64 (s - 68)) 4 = Some (Z_to_le_bytes 4 w) /\ rdn SEGS M' (Z_to_bv 64 (s - 72)) 4 = Some (Z_to_le_bytes 4 h) /\ rdn SEGS M' (Z_to_bv 64 (s - 76)) 4 = Some (Z_to_le_bytes 4 d) /\
      getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 8 = Z_to_bv 64 pixs /\ getr regs' 9 = Z_to_bv 64 1 /\ getr regs' 18 = Z_to_bv 64 10 /\
      getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20 /\
      getr regs' 1 = Z_to_bv 64 234600 /\ getr regs' 10 = Z_to_bv 64 69395 /\ getr regs' 11 = Z_to_bv 64 72715 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list) regs regs' /\
      reg_get fr' 8 = Z_to_bv 64 18446744070507200512 /\ reg_get fr' 9 = Z_to_bv 64 18446744070498811904 /\ (forall r : reg, ~ In (ridx r) [8; 9; 11; 12; 13; 14; 15]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s pixs w h d FZ Hs Hs16 Hp1 Hp2 Hal Hw0 Hh0 Rcm Rd Rw Rh Hd Hw Hh Hlo HI1 HI2 HI3 SOK H2 H10 H11 H12 F10 F11.
  subst d.
  ex_entry regs [s; pixs; w; h; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs; w; h; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)]) m
     [KWr (SA (EVar 32) (-112)) 112; KImg 73728 77824; KImg 282176 282336; KImg 286472 286480;
      KRange (EVar 32) 4208 (2 ^ 47); KAlign (EVar 32) 16; KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 8;
      KWord (SA (EVar 33) 48) 8 (ELit 0); KWord (SA (EVar 33) 0) 4 (EVar 34); KWord (SA (EVar 33) 4) 4 (EVar 35);
      KWord (SA (EVar 33) 8) 4 (ELit 32);
      KRange (EVar 34) 22 (2 ^ 31 - 1); KRange (EVar 35) 0 21;
      KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-112)) 112]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 4%nat 400%nat [234188%Z] [(8%nat, 36%nat); (9%nat, 37%nat)] HK ST FZ.
  fsg_hyp ST F11 F11.
  fsg_hyp ST F10 F10.
  exb_adrive 16%nat 800%nat [97832%Z] [(8%nat, 36%nat); (9%nat, 37%nat)] HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((s - 112)%Z, 112%Z)]; exB_reg_tac idtac|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ cell_goal HK Hlf regs | exB_reg regs HR' | ex_agree HR HR' | fr_val2 | fr_lit | fr_keep2 ].
Qed.

Lemma pbl_W3 : forall (fx : FPState) regs (m : word -> option byte) (s pixs : Z),
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (0 <= pixs < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  getr regs 8 = Z_to_bv 64 pixs ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 234600) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 107284) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 234612 /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 pixs /\
      regs_agree (fun r => In r [1; 10; 11]%list) regs regs').
Proof.
  intros fx regs m s pixs Hs Hp H2 H8.
  ex_entry regs [(s - 112)%Z; pixs] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 112)%Z; pixs]) m []) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 20%nat [107284%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.

Lemma pbl_A_8 : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pixs w h d : Z),
  frm_zero cs ->
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (s mod 16 = 0)%Z ->
  (4096 <= pixs)%Z ->
  (pixs + 64 <= s - 112)%Z ->
  (pixs mod 8 = 0)%Z ->
  (0 <= w < 2 ^ 31)%Z ->
  (0 <= h < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (pixs + 48)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 d) ->
  rdn SEGS m (Z_to_bv 64 pixs) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
  (d = 8)%Z ->
  (22 <= w < 2 ^ 31)%Z ->
  (22 <= h < 2 ^ 31)%Z ->
  (487424 <= s - 112)%Z ->
  (forall j, (73728 <= j < 77824)%Z -> m (Z_to_bv 64 j) = None) ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 pixs ->
  getr regs 11 = Z_to_bv 64 10 ->
  getr regs 12 = Z_to_bv 64 1 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 ->
  reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 234140) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 234456) M' rom /\ frm_zero cs' /\
      rinv [((s - 112)%Z, 112%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 8)))) /\
      rdn SEGS M' (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 9)))) /\
      rdn SEGS M' (Z_to_bv 64 (s - 68)) 4 = Some (Z_to_le_bytes 4 w) /\ rdn SEGS M' (Z_to_bv 64 (s - 72)) 4 = Some (Z_to_le_bytes 4 h) /\ rdn SEGS M' (Z_to_bv 64 (s - 76)) 4 = Some (Z_to_le_bytes 4 d) /\
      getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 8 = Z_to_bv 64 pixs /\ getr regs' 9 = Z_to_bv 64 1 /\ getr regs' 18 = Z_to_bv 64 10 /\
      getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20 /\
      getr regs' 10 = Z_to_bv 64 d /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list) regs regs' /\
      reg_get fr' 8 = Z_to_bv 64 18446744070507200512 /\ reg_get fr' 9 = Z_to_bv 64 18446744070498811904 /\ (forall r : reg, ~ In (ridx r) [8; 9; 11; 12; 13; 14; 15]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s pixs w h d FZ Hs Hs16 Hp1 Hp2 Hal Hw0 Hh0 Rcm Rd Rw Rh Hd Hw Hh Hlo HI1 SOK H2 H10 H11 H12 F10 F11.
  subst d.
  ex_entry regs [s; pixs; w; h; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs; w; h; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)]) m
     [KWr (SA (EVar 32) (-112)) 112; KImg 73728 77824;
      KRange (EVar 32) 4208 (2 ^ 47); KAlign (EVar 32) 16; KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 8;
      KWord (SA (EVar 33) 48) 8 (ELit 0); KWord (SA (EVar 33) 0) 4 (EVar 34); KWord (SA (EVar 33) 4) 4 (EVar 35);
      KWord (SA (EVar 33) 8) 4 (ELit 8);
      KRange (EVar 34) 22 (2 ^ 31 - 1); KRange (EVar 35) 22 (2 ^ 31 - 1);
      KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-112)) 112]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 4%nat 400%nat [234188%Z] [(8%nat, 36%nat); (9%nat, 37%nat)] HK ST FZ.
  fsg_hyp ST F11 F11.
  fsg_hyp ST F10 F10.
  exb_adrive 16%nat 800%nat [234456%Z] [(8%nat, 36%nat); (9%nat, 37%nat)] HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((s - 112)%Z, 112%Z)]; exB_reg_tac idtac|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ cell_goal HK Hlf regs | exB_reg regs HR' | ex_agree HR HR' | fr_val2 | fr_lit | fr_keep2 ].
Qed.

Lemma pbl_A_32 : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pixs w h d : Z),
  frm_zero cs ->
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (s mod 16 = 0)%Z ->
  (4096 <= pixs)%Z ->
  (pixs + 64 <= s - 112)%Z ->
  (pixs mod 8 = 0)%Z ->
  (0 <= w < 2 ^ 31)%Z ->
  (0 <= h < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (pixs + 48)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 d) ->
  rdn SEGS m (Z_to_bv 64 pixs) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
  (d = 32)%Z ->
  (22 <= w < 2 ^ 31)%Z ->
  (22 <= h < 2 ^ 31)%Z ->
  (487424 <= s - 112)%Z ->
  (forall j, (73728 <= j < 77824)%Z -> m (Z_to_bv 64 j) = None) ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 pixs ->
  getr regs 11 = Z_to_bv 64 10 ->
  getr regs 12 = Z_to_bv 64 1 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 ->
  reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 234140) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 234456) M' rom /\ frm_zero cs' /\
      rinv [((s - 112)%Z, 112%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 8)))) /\
      rdn SEGS M' (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 9)))) /\
      rdn SEGS M' (Z_to_bv 64 (s - 68)) 4 = Some (Z_to_le_bytes 4 w) /\ rdn SEGS M' (Z_to_bv 64 (s - 72)) 4 = Some (Z_to_le_bytes 4 h) /\ rdn SEGS M' (Z_to_bv 64 (s - 76)) 4 = Some (Z_to_le_bytes 4 d) /\
      getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 8 = Z_to_bv 64 pixs /\ getr regs' 9 = Z_to_bv 64 1 /\ getr regs' 18 = Z_to_bv 64 10 /\
      getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20 /\
      getr regs' 10 = Z_to_bv 64 d /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list) regs regs' /\
      reg_get fr' 8 = Z_to_bv 64 18446744070507200512 /\ reg_get fr' 9 = Z_to_bv 64 18446744070498811904 /\ (forall r : reg, ~ In (ridx r) [8; 9; 11; 12; 13; 14; 15]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s pixs w h d FZ Hs Hs16 Hp1 Hp2 Hal Hw0 Hh0 Rcm Rd Rw Rh Hd Hw Hh Hlo HI1 SOK H2 H10 H11 H12 F10 F11.
  subst d.
  ex_entry regs [s; pixs; w; h; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs; w; h; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)]) m
     [KWr (SA (EVar 32) (-112)) 112; KImg 73728 77824;
      KRange (EVar 32) 4208 (2 ^ 47); KAlign (EVar 32) 16; KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 8;
      KWord (SA (EVar 33) 48) 8 (ELit 0); KWord (SA (EVar 33) 0) 4 (EVar 34); KWord (SA (EVar 33) 4) 4 (EVar 35);
      KWord (SA (EVar 33) 8) 4 (ELit 32);
      KRange (EVar 34) 22 (2 ^ 31 - 1); KRange (EVar 35) 22 (2 ^ 31 - 1);
      KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-112)) 112]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 4%nat 400%nat [234188%Z] [(8%nat, 36%nat); (9%nat, 37%nat)] HK ST FZ.
  fsg_hyp ST F11 F11.
  fsg_hyp ST F10 F10.
  exb_adrive 16%nat 800%nat [234456%Z] [(8%nat, 36%nat); (9%nat, 37%nat)] HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((s - 112)%Z, 112%Z)]; exB_reg_tac idtac|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ cell_goal HK Hlf regs | exB_reg regs HR' | ex_agree HR HR' | fr_val2 | fr_lit | fr_keep2 ].
Qed.

Lemma pbl_A1b : forall (fr : bvmap 5 word) cs regs (m : word -> option byte),
  frm_zero cs -> getr regs 9 = Z_to_bv 64 1 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 234456) m rom)
    (fun fin => exists cs', fin = @mkst (mkFP (bvmap_set 15%bv (Z_to_bv 64 18446744070479937536) fr) cs') regs (Z_to_bv 64 234460) m rom /\ frm_zero cs').
Proof.
  intros fr cs regs m FZ H9.
  ex_fetch SEGS 234456%Z F D.
  eapply reach_step;
    [ first [reflexivity | vm_compute; reflexivity]
    | eapply fpv_step_fcvt_f_of_x;
        [ exact F | vm_compute; reflexivity | exact D | left; split; reflexivity
        | right; left; split; [reflexivity | split; reflexivity] | exact FZ | first [exact fpv_rm_dyn | reflexivity] ]
    | ].
  apply reach_done. cbn [fp_regs fp_csr].
  lazymatch goal with |- context [getr regs ?r] =>
    let E := fresh "E" in assert (E : r = (9%bv : bv 5)) by bveq; rewrite E, H9 end.
  lazymatch goal with |- exists _, @mkst (mkFP (bvmap_set ?rd ?x _) ?c) _ ?p _ _ = _ /\ _ =>
    replace rd with (15%bv : bv 5) by bveq;
    replace x with (Z_to_bv 64 18446744070479937536) by bveq;
    replace p with (Z_to_bv 64 234460) by bveq;
    exists c; split; [reflexivity | apply fpv_frm_acc; exact FZ] end.
Qed.

Lemma pbl_A2b : forall (fr : bvmap 5 word) cs regs (m : word -> option byte),
  frm_zero cs -> getr regs 18 = Z_to_bv 64 10 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 234772) m rom)
    (fun fin => exists cs', fin = @mkst (mkFP (bvmap_set 15%bv (Z_to_bv 64 18446744070507200512) fr) cs') regs (Z_to_bv 64 234776) m rom /\ frm_zero cs').
Proof.
  intros fr cs regs m FZ H18.
  ex_fetch SEGS 234772%Z F D.
  eapply reach_step;
    [ first [reflexivity | vm_compute; reflexivity]
    | eapply fpv_step_fcvt_f_of_x;
        [ exact F | vm_compute; reflexivity | exact D | left; split; reflexivity
        | right; left; split; [reflexivity | split; reflexivity] | exact FZ | first [exact fpv_rm_dyn | reflexivity] ]
    | ].
  apply reach_done. cbn [fp_regs fp_csr].
  lazymatch goal with |- context [getr regs ?r] =>
    let E := fresh "E" in assert (E : r = (18%bv : bv 5)) by bveq; rewrite E, H18 end.
  lazymatch goal with |- exists _, @mkst (mkFP (bvmap_set ?rd ?x _) ?c) _ ?p _ _ = _ /\ _ =>
    replace rd with (15%bv : bv 5) by bveq;
    replace x with (Z_to_bv 64 18446744070507200512) by bveq;
    replace p with (Z_to_bv 64 234776) by bveq;
    exists c; split; [reflexivity | apply fpv_frm_acc; exact FZ] end.
Qed.

Lemma pbl_A2 : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s : Z),
  frm_zero cs ->
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  getr regs 18 = Z_to_bv 64 10 ->
  reg_get fr 15 = Z_to_bv 64 18446744070479937536 ->
  reg_get fr 9 = Z_to_bv 64 18446744070498811904 ->
  reg_get fr 8 = Z_to_bv 64 18446744070507200512 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 234460) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 234772) M' rom /\ frm_zero cs' /\
      M' = m /\ regs_agree (fun r => In r [11; 12]%list) regs regs' /\ (forall r : reg, ~ In (ridx r) [14; 15]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s FZ Hs H2 H18 F15 F9 F8.
  ex_entry regs [(s - 112)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 112)%Z]) m []) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 4%nat 400%nat [234772%Z] (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [reflexivity|].
  split; [ex_agree HR HR' | fr_keep2].
Qed.

Lemma pbl_A3_8 : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pixs : Z),
  frm_zero cs ->
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (0 <= pixs < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  getr regs 8 = Z_to_bv 64 pixs ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 18 = Z_to_bv 64 10 ->
  getr regs 10 = Z_to_bv 64 8 ->
  reg_get fr 15 = Z_to_bv 64 18446744070507200512 ->
  reg_get fr 9 = Z_to_bv 64 18446744070498811904 ->
  reg_get fr 8 = Z_to_bv 64 18446744070507200512 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 234776) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 235128) M' rom /\ frm_zero cs' /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 234912 /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 10 /\ getr regs' 12 = Z_to_bv 64 1 /\
      regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs' /\
      reg_get fr' 10 = Z_to_bv 64 18446744070498811904 /\ reg_get fr' 11 = Z_to_bv 64 18446744070507200512 /\ (forall r : reg, ~ In (ridx r) [10; 11; 14; 15]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s pixs FZ Hs Hp H2 H8 H9 H18 H10 F15 F9 F8.
  ex_entry regs [(s - 112)%Z; pixs] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 112)%Z; pixs]) m []) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 4%nat 400%nat [235128%Z] (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR' | ex_agree HR HR' | (exB_fr_expr; reflexivity) | fr_keep2 ].
Qed.

Lemma pbl_A3_32 : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pixs : Z),
  frm_zero cs ->
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (0 <= pixs < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  getr regs 8 = Z_to_bv 64 pixs ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 18 = Z_to_bv 64 10 ->
  getr regs 10 = Z_to_bv 64 32 ->
  reg_get fr 15 = Z_to_bv 64 18446744070507200512 ->
  reg_get fr 9 = Z_to_bv 64 18446744070498811904 ->
  reg_get fr 8 = Z_to_bv 64 18446744070507200512 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 234776) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 112124) M' rom /\ frm_zero cs' /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 234928 /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 0 /\
      regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs' /\
      (forall r : reg, ~ In (ridx r) [14; 15]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s pixs FZ Hs Hp H2 H8 H9 H18 H10 F15 F9 F8.
  ex_entry regs [(s - 112)%Z; pixs] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 112)%Z; pixs]) m []) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 4%nat 400%nat [112124%Z] (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR' | ex_agree HR HR' | (exB_fr_expr; reflexivity) | fr_keep2 ].
Qed.

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

Lemma pbl_C1 : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pixt : Z),
  frm_zero cs ->
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (0 <= pixt < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  getr regs 10 = Z_to_bv 64 pixt ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 18 = Z_to_bv 64 10 ->
  reg_get fr 8 = Z_to_bv 64 18446744070507200512 ->
  reg_get fr 9 = Z_to_bv 64 18446744070498811904 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 234928) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 235128) M' rom /\ frm_zero cs' /\
      rinv [((s - 88)%Z, 8%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (s - 88)) 8 = Some (Z_to_le_bytes 8 pixt) /\
      getr regs' 1 = Z_to_bv 64 234952 /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 10 = Z_to_bv 64 pixt /\ getr regs' 11 = Z_to_bv 64 10 /\ getr regs' 12 = Z_to_bv 64 1 /\
      regs_agree (fun r => In r [1; 11; 12]%list) regs regs' /\
      reg_get fr' 10 = Z_to_bv 64 18446744070498811904 /\ reg_get fr' 11 = Z_to_bv 64 18446744070507200512 /\ (forall r : reg, ~ In (ridx r) [10; 11]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s pixt FZ Hs Hp SOK H2 H10 H9 H18 F8 F9.
  ex_entry regs [(s - 112)%Z; pixt] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 112)%Z; pixt]) m [KWr (SA (EVar 32) 0) 112]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 4%nat 400%nat [235128%Z] (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((s - 88)%Z, 8%Z)]; exB_reg_tac idtac|].
  split.
  { exB_cell HK Hlf (EVar 32) 24%Z 8%nat (s - 88)%Z pixt Hc idtac idtac idtac.
    - exB_scs regs.
    - exB_tacA idtac.
    - exB_tacV idtac.
    - exact Hc. }
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR' | ex_agree HR HR' | g3_frlit | fr_keep2 ].
Qed.

Lemma pbl_C4 : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pixt : Z),
  frm_zero cs ->
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (0 <= pixt < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  getr regs 10 = Z_to_bv 64 pixt ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 18 = Z_to_bv 64 10 ->
  reg_get fr 8 = Z_to_bv 64 18446744070507200512 ->
  reg_get fr 9 = Z_to_bv 64 18446744070498811904 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 234980) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 235128) M' rom /\ frm_zero cs' /\
      rinv [((s - 88)%Z, 8%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (s - 88)) 8 = Some (Z_to_le_bytes 8 pixt) /\
      getr regs' 1 = Z_to_bv 64 235004 /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 10 = Z_to_bv 64 pixt /\ getr regs' 11 = Z_to_bv 64 10 /\ getr regs' 12 = Z_to_bv 64 1 /\
      regs_agree (fun r => In r [1; 11; 12]%list) regs regs' /\
      reg_get fr' 10 = Z_to_bv 64 18446744070498811904 /\ reg_get fr' 11 = Z_to_bv 64 18446744070507200512 /\ (forall r : reg, ~ In (ridx r) [10; 11]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s pixt FZ Hs Hp SOK H2 H10 H9 H18 F8 F9.
  ex_entry regs [(s - 112)%Z; pixt] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 112)%Z; pixt]) m [KWr (SA (EVar 32) 0) 112]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 4%nat 400%nat [235128%Z] (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((s - 88)%Z, 8%Z)]; exB_reg_tac idtac|].
  split.
  { exB_cell HK Hlf (EVar 32) 24%Z 8%nat (s - 88)%Z pixt Hc idtac idtac idtac.
    - exB_scs regs.
    - exB_tacA idtac.
    - exB_tacV idtac.
    - exact Hc. }
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR' | ex_agree HR HR' | g3_frlit | fr_keep2 ].
Qed.

Lemma pbl_C7 : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pixt : Z),
  frm_zero cs ->
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (0 <= pixt < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  getr regs 10 = Z_to_bv 64 pixt ->
  getr regs 9 = Z_to_bv 64 1 ->
  getr regs 18 = Z_to_bv 64 10 ->
  reg_get fr 8 = Z_to_bv 64 18446744070507200512 ->
  reg_get fr 9 = Z_to_bv 64 18446744070498811904 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 235032) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 235128) M' rom /\ frm_zero cs' /\
      rinv [((s - 88)%Z, 8%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (s - 88)) 8 = Some (Z_to_le_bytes 8 pixt) /\
      getr regs' 1 = Z_to_bv 64 235056 /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 10 = Z_to_bv 64 pixt /\ getr regs' 11 = Z_to_bv 64 10 /\ getr regs' 12 = Z_to_bv 64 1 /\
      regs_agree (fun r => In r [1; 11; 12]%list) regs regs' /\
      reg_get fr' 10 = Z_to_bv 64 18446744070498811904 /\ reg_get fr' 11 = Z_to_bv 64 18446744070507200512 /\ (forall r : reg, ~ In (ridx r) [10; 11]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s pixt FZ Hs Hp SOK H2 H10 H9 H18 F8 F9.
  ex_entry regs [(s - 112)%Z; pixt] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 112)%Z; pixt]) m [KWr (SA (EVar 32) 0) 112]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 4%nat 400%nat [235128%Z] (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((s - 88)%Z, 8%Z)]; exB_reg_tac idtac|].
  split.
  { exB_cell HK Hlf (EVar 32) 24%Z 8%nat (s - 88)%Z pixt Hc idtac idtac idtac.
    - exB_scs regs.
    - exB_tacA idtac.
    - exB_tacV idtac.
    - exact Hc. }
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR' | ex_agree HR HR' | g3_frlit | fr_keep2 ].
Qed.

Lemma pbl_C2 : forall (fx : FPState) regs (m : word -> option byte) (s r : Z),
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (0 <= r < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  getr regs 10 = Z_to_bv 64 r ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 234952) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 104492) M' rom /\
      rinv [((s - 96)%Z, 8%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (s - 96)) 8 = Some (Z_to_le_bytes 8 r) /\
      getr regs' 1 = Z_to_bv 64 234968 /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 19 = Z_to_bv 64 r /\ getr regs' 10 = Z_to_bv 64 (s - 88) /\
      regs_agree (fun r => In r [1; 10; 19]%list) regs regs').
Proof.
  intros fx regs m s r Hs Hr SOK H2 H10.
  ex_entry regs [(s - 112)%Z; r] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 112)%Z; r]) m [KWr (SA (EVar 32) 0) 112]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [104492%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((s - 96)%Z, 8%Z)]; exB_reg_tac idtac|].
  split.
  { exB_cell HK Hlf (EVar 32) 16%Z 8%nat (s - 96)%Z r Hc idtac idtac idtac.
    - exB_scs regs.
    - exB_tacA idtac.
    - exB_tacV idtac.
    - exact Hc. }
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.

Lemma pbl_C5 : forall (fx : FPState) regs (m : word -> option byte) (s r : Z),
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (0 <= r < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  getr regs 10 = Z_to_bv 64 r ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 235004) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 104492) M' rom /\
      rinv [((s - 104)%Z, 8%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (s - 104)) 8 = Some (Z_to_le_bytes 8 r) /\
      getr regs' 1 = Z_to_bv 64 235020 /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 20 = Z_to_bv 64 r /\ getr regs' 10 = Z_to_bv 64 (s - 88) /\
      regs_agree (fun r => In r [1; 10; 20]%list) regs regs').
Proof.
  intros fx regs m s r Hs Hr SOK H2 H10.
  ex_entry regs [(s - 112)%Z; r] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 112)%Z; r]) m [KWr (SA (EVar 32) 0) 112]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [104492%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((s - 104)%Z, 8%Z)]; exB_reg_tac idtac|].
  split.
  { exB_cell HK Hlf (EVar 32) 8%Z 8%nat (s - 104)%Z r Hc idtac idtac idtac.
    - exB_scs regs.
    - exB_tacA idtac.
    - exB_tacV idtac.
    - exact Hc. }
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.

Lemma pbl_C8 : forall (fx : FPState) regs (m : word -> option byte) (s r : Z),
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (0 <= r < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  getr regs 10 = Z_to_bv 64 r ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 235056) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 104492) M' rom /\
      rinv [((s - 112)%Z, 8%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (s - 112)) 8 = Some (Z_to_le_bytes 8 r) /\
      getr regs' 1 = Z_to_bv 64 235072 /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 8 = Z_to_bv 64 r /\ getr regs' 10 = Z_to_bv 64 (s - 88) /\
      regs_agree (fun r => In r [1; 10; 8]%list) regs regs').
Proof.
  intros fx regs m s r Hs Hr SOK H2 H10.
  ex_entry regs [(s - 112)%Z; r] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 112)%Z; r]) m [KWr (SA (EVar 32) 0) 112]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [104492%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((s - 112)%Z, 8%Z)]; exB_reg_tac idtac|].
  split.
  { exB_cell HK Hlf (EVar 32) 0%Z 8%nat (s - 112)%Z r Hc idtac idtac idtac.
    - exB_scs regs.
    - exB_tacA idtac.
    - exB_tacV idtac.
    - exact Hc. }
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.

Lemma pbl_C3 : forall (fx : FPState) regs (m : word -> option byte) (s pixs : Z),
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (0 <= pixs < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  getr regs 8 = Z_to_bv 64 pixs ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 234968) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 112124) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 234980 /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 1 /\
      regs_agree (fun r => In r [1; 10; 11]%list) regs regs').
Proof.
  intros fx regs m s pixs Hs Hp H2 H8.
  ex_entry regs [(s - 112)%Z; pixs] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 112)%Z; pixs]) m []) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [112124%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.

Lemma pbl_C6 : forall (fx : FPState) regs (m : word -> option byte) (s pixs : Z),
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (0 <= pixs < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  getr regs 8 = Z_to_bv 64 pixs ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 235020) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 112124) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 235032 /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 2 /\
      regs_agree (fun r => In r [1; 10; 11]%list) regs regs').
Proof.
  intros fx regs m s pixs Hs Hp H2 H8.
  ex_entry regs [(s - 112)%Z; pixs] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 112)%Z; pixs]) m []) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [112124%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.

Lemma pbl_C9 : forall (fx : FPState) regs (m : word -> option byte) (s r g b : Z),
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (0 <= r < 2 ^ 64)%Z ->
  (0 <= g < 2 ^ 64)%Z ->
  (0 <= b < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  getr regs 19 = Z_to_bv 64 r ->
  getr regs 20 = Z_to_bv 64 g ->
  getr regs 8 = Z_to_bv 64 b ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 235072) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 117472) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 235088 /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 10 = Z_to_bv 64 r /\ getr regs' 11 = Z_to_bv 64 g /\ getr regs' 12 = Z_to_bv 64 b /\
      regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs').
Proof.
  intros fx regs m s r g b Hs Hr Hg Hb H2 H19 H20 H8.
  ex_entry regs [(s - 112)%Z; r; g; b] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 112)%Z; r; g; b]) m []) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [117472%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.

Lemma pbl_C10 : forall (fx : FPState) regs (m : word -> option byte) (s pixd : Z),
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  (0 <= pixd < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  getr regs 10 = Z_to_bv 64 pixd ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 235088) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 104492) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 235100 /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 8 = Z_to_bv 64 pixd /\ getr regs' 10 = Z_to_bv 64 (s - 96) /\
      regs_agree (fun r => In r [1; 8; 10]%list) regs regs').
Proof.
  intros fx regs m s pixd Hs Hp H2 H10.
  ex_entry regs [(s - 112)%Z; pixd] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 112)%Z; pixd]) m []) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [104492%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.

Lemma pbl_C11 : forall (fx : FPState) regs (m : word -> option byte) (s : Z),
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 235100) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 104492) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 235108 /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 10 = Z_to_bv 64 (s - 104) /\
      regs_agree (fun r => In r [1; 10]%list) regs regs').
Proof.
  intros fx regs m s Hs H2.
  ex_entry regs [(s - 112)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 112)%Z]) m []) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [104492%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.

Lemma pbl_C12 : forall (fx : FPState) regs (m : word -> option byte) (s : Z),
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 235108) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 104492) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 235116 /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 10 = Z_to_bv 64 (s - 112) /\
      regs_agree (fun r => In r [1; 10]%list) regs regs').
Proof.
  intros fx regs m s Hs H2.
  ex_entry regs [(s - 112)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 112)%Z]) m []) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [104492%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.

Lemma pbl_X_err : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s : Z) (ret : word) (v1 v8 v9 v18 v19 v20 g8 g9 : word),
  frm_zero cs ->
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  ret_ok ret ->
  v1 = ret ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v20) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 g8) ->
  rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 g9) ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 234768) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' ret M' rom /\ frm_zero cs' /\
      M' = m /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = getr regs 10 /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20]%list) regs regs' /\
      reg_get fr' 8 = g8 /\ reg_get fr' 9 = g9 /\ (forall r : reg, ~ In (ridx r) [8; 9]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s ret v1 v8 v9 v18 v19 v20 g8 g9 FZ Hs Hok Hv1 R1 R8 R9 R18 R19 R20 RG8 RG9 H2.
  subst v1.
  ex_entryL [ret; v8; v9; v18; v19; v20; g8; g9] regs [s] HR.
  assert (HK : know_ok SEGS (ex_envL [ret; v8; v9; v18; v19; v20; g8; g9] regs [s]) m
     [KWord (SA (EVar 40) (-8)) 8 (EVar 0); KWord (SA (EVar 40) (-16)) 8 (EVar 1); KWord (SA (EVar 40) (-24)) 8 (EVar 2);
      KWord (SA (EVar 40) (-32)) 8 (EVar 3); KWord (SA (EVar 40) (-40)) 8 (EVar 4); KWord (SA (EVar 40) (-48)) 8 (EVar 5);
      KWord (SA (EVar 40) (-56)) 8 (EVar 6); KWord (SA (EVar 40) (-64)) 8 (EVar 7)]) by (ex_know regs).
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

Lemma pbl_X_cp : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s : Z) (ret : word) (v1 v8 v9 v18 v19 v20 g8 g9 : word),
  frm_zero cs ->
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  ret_ok ret ->
  v1 = ret ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v20) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 g8) ->
  rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 g9) ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 234612) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' ret M' rom /\ frm_zero cs' /\
      M' = m /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = getr regs 10 /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20]%list) regs regs' /\
      reg_get fr' 8 = g8 /\ reg_get fr' 9 = g9 /\ (forall r : reg, ~ In (ridx r) [8; 9]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s ret v1 v8 v9 v18 v19 v20 g8 g9 FZ Hs Hok Hv1 R1 R8 R9 R18 R19 R20 RG8 RG9 H2.
  subst v1.
  ex_entryL [ret; v8; v9; v18; v19; v20; g8; g9] regs [s] HR.
  assert (HK : know_ok SEGS (ex_envL [ret; v8; v9; v18; v19; v20; g8; g9] regs [s]) m
     [KWord (SA (EVar 40) (-8)) 8 (EVar 0); KWord (SA (EVar 40) (-16)) 8 (EVar 1); KWord (SA (EVar 40) (-24)) 8 (EVar 2);
      KWord (SA (EVar 40) (-32)) 8 (EVar 3); KWord (SA (EVar 40) (-40)) 8 (EVar 4); KWord (SA (EVar 40) (-48)) 8 (EVar 5);
      KWord (SA (EVar 40) (-56)) 8 (EVar 6); KWord (SA (EVar 40) (-64)) 8 (EVar 7)]) by (ex_know regs).
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

Lemma pbl_X_g8 : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s : Z) (ret : word) (v1 v8 v9 v18 v19 v20 g8 g9 : word),
  frm_zero cs ->
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  ret_ok ret ->
  v1 = ret ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v20) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 g8) ->
  rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 g9) ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 234912) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' ret M' rom /\ frm_zero cs' /\
      M' = m /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = getr regs 10 /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20]%list) regs regs' /\
      reg_get fr' 8 = g8 /\ reg_get fr' 9 = g9 /\ (forall r : reg, ~ In (ridx r) [8; 9]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s ret v1 v8 v9 v18 v19 v20 g8 g9 FZ Hs Hok Hv1 R1 R8 R9 R18 R19 R20 RG8 RG9 H2.
  subst v1.
  ex_entryL [ret; v8; v9; v18; v19; v20; g8; g9] regs [s] HR.
  assert (HK : know_ok SEGS (ex_envL [ret; v8; v9; v18; v19; v20; g8; g9] regs [s]) m
     [KWord (SA (EVar 40) (-8)) 8 (EVar 0); KWord (SA (EVar 40) (-16)) 8 (EVar 1); KWord (SA (EVar 40) (-24)) 8 (EVar 2);
      KWord (SA (EVar 40) (-32)) 8 (EVar 3); KWord (SA (EVar 40) (-40)) 8 (EVar 4); KWord (SA (EVar 40) (-48)) 8 (EVar 5);
      KWord (SA (EVar 40) (-56)) 8 (EVar 6); KWord (SA (EVar 40) (-64)) 8 (EVar 7)]) by (ex_know regs).
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

Lemma pbl_XE : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s : Z) (ret : word) (v1 v8 v9 v18 v19 v20 g8 g9 : word),
  frm_zero cs ->
  (4096 + 112 <= s <= 2 ^ 47)%Z ->
  ret_ok ret ->
  v1 = ret ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v20) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 g8) ->
  rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 g9) ->
  getr regs 2 = Z_to_bv 64 (s - 112) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 235116) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' ret M' rom /\ frm_zero cs' /\
      M' = m /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = getr regs 8 /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20]%list) regs regs' /\
      reg_get fr' 8 = g8 /\ reg_get fr' 9 = g9 /\ (forall r : reg, ~ In (ridx r) [8; 9]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s ret v1 v8 v9 v18 v19 v20 g8 g9 FZ Hs Hok Hv1 R1 R8 R9 R18 R19 R20 RG8 RG9 H2.
  subst v1.
  ex_entryL [ret; v8; v9; v18; v19; v20; g8; g9] regs [s] HR.
  assert (HK : know_ok SEGS (ex_envL [ret; v8; v9; v18; v19; v20; g8; g9] regs [s]) m
     [KWord (SA (EVar 40) (-8)) 8 (EVar 0); KWord (SA (EVar 40) (-16)) 8 (EVar 1); KWord (SA (EVar 40) (-24)) 8 (EVar 2);
      KWord (SA (EVar 40) (-32)) 8 (EVar 3); KWord (SA (EVar 40) (-40)) 8 (EVar 4); KWord (SA (EVar 40) (-48)) 8 (EVar 5);
      KWord (SA (EVar 40) (-56)) 8 (EVar 6); KWord (SA (EVar 40) (-64)) 8 (EVar 7)]) by (ex_know regs).
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
