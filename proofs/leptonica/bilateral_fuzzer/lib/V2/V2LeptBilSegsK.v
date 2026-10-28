(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV FPStepsB Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptDefs LeptStructs LeptArith DitherLib DitherLoop LeptExec LeptExecX LeptExecFP LeptExecB LeptFPB LeptArithB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import FpBound FpReal FpSiteB FpSiteC.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBilSegs.
From stdpp.bitvector Require Import tactics.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.
#[local] Opaque RiscvSemantics.store_ok.

Lemma xk_lxor_ones : forall z, (0 <= z < 2 ^ 64)%Z -> Z.lxor z (Z.ones 64) = (2 ^ 64 - 1 - z)%Z.
Proof.
  intros z Hz.
  assert (L : Z.ldiff z (Z.ones 64) = 0%Z).
  { rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. apply Z.shiftl_0_l. }
  replace (2 ^ 64 - 1 - z)%Z with (Z.ones 64 - z)%Z by (rewrite Z.ones_equiv; lia).
  rewrite (Z.sub_nocarry_ldiff (Z.ones 64) z L), Z.lxor_comm.
  apply Z.bits_inj'; intros n Hn. rewrite Z.lxor_spec, Z.ldiff_spec.
  destruct (Z.testbit (Z.ones 64) n) eqn:E1, (Z.testbit z n) eqn:E2; try reflexivity.
  exfalso. pose proof (f_equal (fun x => Z.testbit x n) L) as T. cbn beta in T.
  rewrite Z.ldiff_spec, E1, E2, Z.bits_0 in T. discriminate.
Qed.
Lemma xk_not : forall z, (0 <= z < 2 ^ 64)%Z -> alu64 ALU_XOR (Z_to_bv 64 z) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - z).
Proof. intros z Hz. unfold alu64, alu. cbn. apply bv_eq. rewrite bv_xor_unsigned, !Z_to_bv_unsigned.
  replace (bv_wrap 64 (-1)) with (Z.ones 64) by reflexivity.
  rewrite (bv_wrap_small 64 z) by (unfold bv_modulus; lia).
  rewrite (bv_wrap_small 64 (2 ^ 64 - 1 - z)) by (unfold bv_modulus; lia).
  apply xk_lxor_ones; exact Hz.
Qed.
Lemma xk_rd_cvt : forall fr (r r' : reg) a, bv_unsigned r' = bv_unsigned r -> (0 <= a < 2 ^ 64)%Z ->
  fpv_read (bvmap_set r (fpv_box FMT_S (fst (fp_of_int (fp_format FMT_S) RNE true 32 (bv_unsigned (Z_to_bv 64 a))))) fr) FMT_S r' = cvS a.
Proof. intros fr r r' a E Ha. apply bv_eq in E. subst r'. unfold fpv_box. rewrite fpv_read_S_box. rewrite u_Z2bv by lia. reflexivity. Qed.
Lemma xk_rd_other : forall fr fmt (r r' : reg) v, bv_unsigned r' <> bv_unsigned r -> fpv_read (bvmap_set r v fr) fmt r' = fpv_read fr fmt r'.
Proof. intros fr fmt r r' v E. apply fpv_read_other. intros ->. apply E. reflexivity. Qed.
Lemma xk_rd_kept : forall E fr (r : reg), fpv_read (fr_denot E [] fr) FMT_S r = fpv_read fr FMT_S r.
Proof. intros E fr r. unfold fpv_read. rewrite fr_kept by (cbn; tauto). reflexivity. Qed.
Lemma xk_flt : forall i n, (0 <= i <= 256)%Z -> (0 <= n <= 256)%Z -> fst (fpv_cmp F_LT FMT_S (cvS i) (cvS n)) = (i <? n)%Z.
Proof. intros i n Hi Hn. cbn [fpv_cmp]. apply flt_small; lia. Qed.

#[local] Ltac xb_val := lazymatch goal with |- context [sr_get ?sr ?r] => let e := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with e end;
  ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; bw_norm; reflexivity.
#[local] Ltac xb_pcnorm ST := lazymatch type of ST with ex_st _ _ _ _ _ _ ?pc _ _ => let p := eval vm_compute in pc in change pc with p in ST end.
#[local] Ltac xb_cvt ST FZ rs v :=
  lazymatch type of ST with ex_st _ ?E _ _ _ _ _ ?sr _ =>
    let V := fresh "V" in assert (V : edenot E (sr_get sr rs) = Z_to_bv 64 v) by xb_val;
    let HF := fresh "HF" in let HD := fresh "HD" in xb_fd ST HF HD;
    let ST1 := fresh "ST" in
    pose proof (xb_fcvt_fx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RNE FMT_S true 32%Z v ST HF ltac:(xb_ec) HD
       (or_introl (conj eq_refl eq_refl)) (or_introl (conj eq_refl (conj eq_refl eq_refl))) FZ ltac:(reflexivity) V) as ST1;
    clear ST HF HD V; rename ST1 into ST; xb_pcnorm ST; exb_reabs ST FZ
  end.
#[local] Ltac xb_rdfp := repeat first [ rewrite xk_rd_cvt by (first [reflexivity | lia]) | rewrite xk_rd_other by (vm_compute; congruence) | rewrite xk_rd_kept ].
#[local] Ltac xb_cmp ST FZ b tacB :=
  let HF := fresh "HF" in let HD := fresh "HD" in xb_fd ST HF HD;
  let ST1 := fresh "ST" in
  pose proof (xb_fcmp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b ST HF ltac:(xb_ec) HD ltac:(xb_rdfp; tacB) eq_refl) as ST1;
  clear ST HF HD; rename ST1 into ST; xb_pcnorm ST; exb_reabs ST FZ.
#[local] Ltac xb_fprw F := lazymatch type of F with fpv_read ?fr ?fmt ?r0 = _ =>
  lazymatch goal with |- context [fpv_read fr fmt ?r] => replace r with r0 by (apply bv_eq; reflexivity); rewrite F end end.

Section BilSegsK.
Variable rom : word -> option byte.
#[local] Existing Instance exf_fxd | 100.
#[local] Ltac exB_sc_hook ::= first [ bw_hook | (bw_norm; ex_br) ].
#[local] Ltac bcell HK Hlf regs rb rk :=
  let N := fresh "C" in
  lazymatch goal with
  | |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some (Z_to_le_bytes ?n ?z) =>
      exB_cell HK Hlf rb rk n a z N ltac:(exb_scs regs) ltac:(exB_tacA idtac) ltac:(exB_tacV idtac); exact N
  end.

#[local] Ltac bcellV HK Hlf regs rb rk tacV :=
  let N := fresh "C" in
  lazymatch goal with
  | |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some (Z_to_le_bytes ?n ?z) =>
      exB_cell HK Hlf rb rk n a z N ltac:(exb_scs regs) ltac:(exB_tacA idtac) tacV; exact N
  end.
#[local] Ltac sltu1 := rewrite v_sltu_Z by lia;
  lazymatch goal with |- context [(0 <? ?b)%Z] => replace (0 <? b)%Z with true by (symmetry; apply Z.ltb_lt; lia) end;
  first [ reflexivity | (vm_compute; reflexivity) ].
#[local] Ltac kx_fin := first [ reflexivity | sltu1 | (rewrite zbv_addw_small by lia; reflexivity) | (bw_norm; reflexivity) ].

Section KX.
Variables (s nc kx minv maxv : Z).
Hypothesis Hs : (4096 + 320 <= s <= 2 ^ 47)%Z.
Hypothesis Hn1 : (4096 <= nc)%Z.
Hypothesis Hn2 : (nc + 40 <= s - 320)%Z.
Hypothesis Hk1 : (4096 <= kx)%Z.
Hypothesis Hk2 : (kx + 1024 <= s - 320)%Z.
Hypothesis ALk : (kx mod 16 = 0)%Z.
Hypothesis APnk : (kx + 1024 <= nc \/ nc + 40 <= kx)%Z.
Hypothesis Hmin : (0 <= minv <= 255)%Z.
Hypothesis Hmax : (0 <= maxv <= 255)%Z.

Definition kx_M (M : word -> option byte) : Prop :=
  rdn SEGS M (Z_to_bv 64 (s - 152)) 4 = Some (Z_to_le_bytes 4 maxv) /\
  rdn SEGS M (Z_to_bv 64 (s - 248)) 8 = Some (Z_to_le_bytes 8 nc) /\
  rdn SEGS M (Z_to_bv 64 (s - 256)) 8 = Some (Z_to_le_bytes 8 (2 ^ 64 - 1 - nc)) /\
  (forall j, (0 <= j < 10)%Z -> rdn SEGS M (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) /\
  store_ok SEGS M (Z_to_bv 64 kx) 1024 = true.

Lemma kx_bc : forall (fr : bvmap 5 word) cs regs (M : word -> option byte) (i n k : Z),
  frm_zero cs -> (0 <= i)%Z -> (i + 1 < n)%Z -> (n <= 255)%Z -> (0 <= k <= 8)%Z -> kx_M M ->
  fpv_read fr FMT_S 15 = cvS n ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 8 = Z_to_bv 64 9 -> getr regs 9 = Z_to_bv 64 nc -> getr regs 10 = Z_to_bv 64 kx ->
  getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 1 -> getr regs 13 = Z_to_bv 64 i -> getr regs 5 = Z_to_bv 64 i ->
  getr regs 14 = Z_to_bv 64 k -> getr regs 15 = Z_to_bv 64 (k + 1) ->
  getr regs 16 = Z_to_bv 64 (kx + 4 * i) -> getr regs 17 = Z_to_bv 64 (kx + 4 * i) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x39b78) M rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x39b78) M' rom /\ frm_zero cs' /\
       rinv [((kx + 4 * i)%Z, 4%Z)] M M' /\ rdn SEGS M' (Z_to_bv 64 (kx + 4 * i)) 4 = Some (Z_to_le_bytes 4 k) /\
       fpv_read fr' FMT_S 15 = cvS n /\ (forall r : reg, ~ In (ridx r) [14]%nat -> reg_get fr' r = reg_get fr r) /\
       getr regs' 13 = Z_to_bv 64 (i + 1) /\ getr regs' 5 = Z_to_bv 64 (i + 1) /\
       getr regs' 16 = Z_to_bv 64 (kx + 4 * (i + 1)) /\ getr regs' 17 = Z_to_bv 64 (kx + 4 * (i + 1)) /\
       regs_agree (fun r => In r [5; 6; 7; 13; 16; 17]%list) regs regs').
Proof.
  intros fr cs regs M i n k FZ Hi Hin Hn Hk (Cmax & Cnc & Cnn & Cv & SOKk) F15 H2 H8 H9 H10 H11 H12 H13 H5 H14 H15 H16 H17.
  ex_entry regs [(s - 320)%Z; nc; kx; maxv; i; k; (2 ^ 64 - 1 - nc)%Z; (kx + 4 * i)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 320)%Z; nc; kx; maxv; i; k; (2 ^ 64 - 1 - nc)%Z; (kx + 4 * i)%Z]) M
     [KRange (EVar 32) 4096 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KRange (EVar 34) 4096 (2 ^ 47);
      KRange (EVar 35) 0 255; KRange (EVar 36) 0 254; KRange (EVar 37) 0 8; KAlign (EVar 34) 16;
      KRange (EVar 39) 4096 (2 ^ 47);
      KWr (SA (EVar 34) 0) 1024; KWr (SA (EVar 39) 0) 4;
      KWord (SA (EVar 32) 168) 4 (EVar 35);
      KWord (SA (EVar 32) 64) 8 (EVar 38); KRange (EVar 38) (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 4096); KWord (SA (EVar 32) 72) 8 (EVar 33);
      KDisj (SA (EVar 34) 0) 1024 (SA (EVar 32) 0) 320; KDisj (SA (EVar 33) 0) 40 (SA (EVar 32) 0) 320;
      KDisj (SA (EVar 34) 0) 1024 (SA (EVar 33) 0) 40; KDisj (SA (EVar 39) 0) 4 (SA (EVar 32) 0) 320]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adriveS 8%nat 400%nat [0x39ba4%Z] (SCR (repeat false 8) [] []) (@nil (nat * nat)) HK ST FZ.
  xb_cvt ST FZ (6 : reg) (i + 1)%Z.
  exb_adriveS 8%nat 400%nat [0x39bac%Z] (SCR [] [] []) (@nil (nat * nat)) HK ST FZ.
  xb_cmp ST FZ true ltac:(xb_fprw F15; rewrite xk_flt by lia; apply Z.ltb_lt; lia).
  exb_adriveS 8%nat 400%nat [0x39b78%Z] (SCR [] [] []) (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((kx + 4 * i)%Z, 4%Z)]; exB_reg_tac idtac|].
  split; [bcell HK Hlf regs (EVar 39) 0%Z|].
  split; [xb_rdfp; xb_fprw F15; reflexivity|].
  split; [intros r Hr; rewrite fpv_get_other; [apply fr_kept; cbn; tauto | intros ->; apply Hr; vm_compute; tauto]|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_agree HR HR' | ex_reg regs HR' ].
  all: kx_fin.
Qed.

Lemma kx_bx : forall (fr : bvmap 5 word) cs regs (M : word -> option byte) (i n k : Z),
  frm_zero cs -> (0 <= i)%Z -> (i < n)%Z -> (n <= i + 1)%Z -> (n <= maxv)%Z -> (0 <= k < 8)%Z -> kx_M M ->
  fpv_read fr FMT_S 15 = cvS n ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 8 = Z_to_bv 64 9 -> getr regs 9 = Z_to_bv 64 nc -> getr regs 10 = Z_to_bv 64 kx ->
  getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 1 -> getr regs 13 = Z_to_bv 64 i -> getr regs 5 = Z_to_bv 64 i ->
  getr regs 14 = Z_to_bv 64 k -> getr regs 15 = Z_to_bv 64 (k + 1) ->
  getr regs 16 = Z_to_bv 64 (kx + 4 * i) -> getr regs 17 = Z_to_bv 64 (kx + 4 * i) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x39b78) M rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x39b3c) M' rom /\ frm_zero cs' /\
       rinv [((kx + 4 * i)%Z, 4%Z)] M M' /\ rdn SEGS M' (Z_to_bv 64 (kx + 4 * i)) 4 = Some (Z_to_le_bytes 4 k) /\
       (forall r : reg, ~ In (ridx r) [14]%nat -> reg_get fr' r = reg_get fr r) /\
       getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 8 = Z_to_bv 64 9 /\ getr regs' 9 = Z_to_bv 64 nc /\ getr regs' 10 = Z_to_bv 64 kx /\
       getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 (i + 1) /\
       getr regs' 14 = Z_to_bv 64 (k + 1) /\ getr regs' 16 = Z_to_bv 64 maxv /\
       regs_agree (fun r => In r [5; 6; 7; 13; 14; 15; 16; 17]%list) regs regs').
Proof.
  intros fr cs regs M i n k FZ Hi Hin Hni Hnm Hk (Cmax & Cnc & Cnn & Cv & SOKk) F15 H2 H8 H9 H10 H11 H12 H13 H5 H14 H15 H16 H17.
  ex_entry regs [(s - 320)%Z; nc; kx; maxv; i; k; (2 ^ 64 - 1 - nc)%Z; (kx + 4 * i)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 320)%Z; nc; kx; maxv; i; k; (2 ^ 64 - 1 - nc)%Z; (kx + 4 * i)%Z]) M
     [KRange (EVar 32) 4096 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KRange (EVar 34) 4096 (2 ^ 47);
      KRange (EVar 35) 0 255; KRange (EVar 36) 0 254; KRange (EVar 37) 0 7; KAlign (EVar 34) 16;
      KRange (EVar 39) 4096 (2 ^ 47);
      KWr (SA (EVar 34) 0) 1024; KWr (SA (EVar 39) 0) 4;
      KWord (SA (EVar 32) 168) 4 (EVar 35);
      KWord (SA (EVar 32) 64) 8 (EVar 38); KRange (EVar 38) (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 4096); KWord (SA (EVar 32) 72) 8 (EVar 33);
      KDisj (SA (EVar 34) 0) 1024 (SA (EVar 32) 0) 320; KDisj (SA (EVar 33) 0) 40 (SA (EVar 32) 0) 320;
      KDisj (SA (EVar 34) 0) 1024 (SA (EVar 33) 0) 40; KDisj (SA (EVar 39) 0) 4 (SA (EVar 32) 0) 320]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adriveS 8%nat 400%nat [0x39ba4%Z] (SCR (repeat false 8) [] []) (@nil (nat * nat)) HK ST FZ.
  xb_cvt ST FZ (6 : reg) (i + 1)%Z.
  exb_adriveS 8%nat 400%nat [0x39bac%Z] (SCR [] [] []) (@nil (nat * nat)) HK ST FZ.
  xb_cmp ST FZ false ltac:(xb_fprw F15; rewrite xk_flt by lia; apply Z.ltb_ge; lia).
  exb_adriveS 8%nat 400%nat [0x39b3c%Z] (SCR [false; true] [] []) (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((kx + 4 * i)%Z, 4%Z)]; exB_reg_tac idtac|].
  split; [bcell HK Hlf regs (EVar 39) 0%Z|].
  split; [intros r Hr; rewrite fpv_get_other; [apply fr_kept; cbn; tauto | intros ->; apply Hr; vm_compute; tauto]|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_agree HR HR' | ex_reg regs HR' ].
  all: kx_fin.
Qed.

Lemma kx_bz : forall (fr : bvmap 5 word) cs regs (M : word -> option byte) (i n : Z),
  frm_zero cs -> (0 <= i)%Z -> (i < n)%Z -> (n <= i + 1)%Z -> (n <= maxv)%Z ->  kx_M M ->
  fpv_read fr FMT_S 15 = cvS n ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 8 = Z_to_bv 64 9 -> getr regs 9 = Z_to_bv 64 nc -> getr regs 10 = Z_to_bv 64 kx ->
  getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 1 -> getr regs 13 = Z_to_bv 64 i -> getr regs 5 = Z_to_bv 64 i ->
  getr regs 14 = Z_to_bv 64 8 -> getr regs 15 = Z_to_bv 64 9 ->
  getr regs 16 = Z_to_bv 64 (kx + 4 * i) -> getr regs 17 = Z_to_bv 64 (kx + 4 * i) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x39b78) M rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x39bd4) M' rom /\ frm_zero cs' /\
       rinv [((kx + 4 * i)%Z, 4%Z)] M M' /\ rdn SEGS M' (Z_to_bv 64 (kx + 4 * i)) 4 = Some (Z_to_le_bytes 4 8) /\
       (forall r : reg, ~ In (ridx r) [14]%nat -> reg_get fr' r = reg_get fr r) /\
       getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 8 = Z_to_bv 64 9 /\ getr regs' 9 = Z_to_bv 64 nc /\ getr regs' 10 = Z_to_bv 64 kx /\
       getr regs' 16 = Z_to_bv 64 maxv /\
       regs_agree (fun r => In r [5; 6; 7; 13; 14; 15; 16; 17]%list) regs regs').
Proof.
  intros fr cs regs M i n FZ Hi Hin Hni Hnm (Cmax & Cnc & Cnn & Cv & SOKk) F15 H2 H8 H9 H10 H11 H12 H13 H5 H14 H15 H16 H17.
  ex_entry regs [(s - 320)%Z; nc; kx; maxv; i; (2 ^ 64 - 1 - nc)%Z; (kx + 4 * i)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 320)%Z; nc; kx; maxv; i; (2 ^ 64 - 1 - nc)%Z; (kx + 4 * i)%Z]) M
     [KRange (EVar 32) 4096 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KRange (EVar 34) 4096 (2 ^ 47);
      KRange (EVar 35) 0 255; KRange (EVar 36) 0 254; KAlign (EVar 34) 16;
      KRange (EVar 38) 4096 (2 ^ 47);
      KWr (SA (EVar 34) 0) 1024; KWr (SA (EVar 38) 0) 4;
      KWord (SA (EVar 32) 168) 4 (EVar 35);
      KWord (SA (EVar 32) 64) 8 (EVar 37); KRange (EVar 37) (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 4096); KWord (SA (EVar 32) 72) 8 (EVar 33);
      KDisj (SA (EVar 34) 0) 1024 (SA (EVar 32) 0) 320; KDisj (SA (EVar 33) 0) 40 (SA (EVar 32) 0) 320;
      KDisj (SA (EVar 34) 0) 1024 (SA (EVar 33) 0) 40; KDisj (SA (EVar 38) 0) 4 (SA (EVar 32) 0) 320]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adriveS 8%nat 400%nat [0x39ba4%Z] (SCR (repeat false 8) [] []) (@nil (nat * nat)) HK ST FZ.
  xb_cvt ST FZ (6 : reg) (i + 1)%Z.
  exb_adriveS 8%nat 400%nat [0x39bac%Z] (SCR [] [] []) (@nil (nat * nat)) HK ST FZ.
  xb_cmp ST FZ false ltac:(xb_fprw F15; rewrite xk_flt by lia; apply Z.ltb_ge; lia).
  exb_adriveS 8%nat 400%nat [0x39bd4%Z] (SCR [false] [] []) (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((kx + 4 * i)%Z, 4%Z)]; exB_reg_tac idtac|].
  split; [bcell HK Hlf regs (EVar 38) 0%Z|].
  split; [intros r Hr; rewrite fpv_get_other; [apply fr_kept; cbn; tauto | intros ->; apply Hr; vm_compute; tauto]|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_agree HR HR' | ex_reg regs HR' ].
  all: kx_fin.
Qed.

#[local] Ltac kx_hcase k Cn :=
  assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8)%Z as KK by lia;
  destruct KK as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; cbn [Z.add Z.mul Pos.add Pos.mul Pos.succ] in Cn.

#[local] Ltac kx_hrun regs fr i n FZ HR HK ST off b tacB stops dirs :=
  ex_entry regs [(s - 320)%Z; nc; kx; maxv; i; n; (2 ^ 64 - 1 - nc)%Z] HR;
  assert (HK : know_ok SEGS (ex_env regs [(s - 320)%Z; nc; kx; maxv; i; n; (2 ^ 64 - 1 - nc)%Z]) _
     [KRange (EVar 32) 4096 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KRange (EVar 34) 4096 (2 ^ 47);
      KRange (EVar 35) 0 255; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255; KAlign (EVar 34) 16;
      KWr (SA (EVar 34) 0) 1024;
      KWord (SA (EVar 33) off) 4 (EVar 37); KWord (SA (EVar 32) 168) 4 (EVar 35);
      KWord (SA (EVar 32) 64) 8 (EVar 38); KRange (EVar 38) (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 4096); KWord (SA (EVar 32) 72) 8 (EVar 33);
      KDisj (SA (EVar 34) 0) 1024 (SA (EVar 32) 0) 320; KDisj (SA (EVar 33) 0) 40 (SA (EVar 32) 0) 320;
      KDisj (SA (EVar 34) 0) 1024 (SA (EVar 33) 0) 40]) by (ex_know regs);
  exb_open HR HK ST;
  exb_adriveS 8%nat 400%nat [0x39b58%Z] (SCR (repeat false 4) [] []) (@nil (nat * nat)) HK ST FZ;
  xb_cvt ST FZ (17 : reg) n; xb_cvt ST FZ (13 : reg) i;
  xb_cmp ST FZ b tacB;
  exb_adriveS 8%nat 400%nat stops (SCR dirs [] []) (@nil (nat * nat)) HK ST FZ.

Lemma kx_ht : forall (fr : bvmap 5 word) cs regs (M : word -> option byte) (k i : Z),
  frm_zero cs -> (0 <= k <= 8)%Z -> (0 <= i)%Z -> (i < nc_val minv maxv (k + 1))%Z -> kx_M M ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 8 = Z_to_bv 64 9 -> getr regs 9 = Z_to_bv 64 nc -> getr regs 10 = Z_to_bv 64 kx ->
  getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 1 -> getr regs 13 = Z_to_bv 64 i -> getr regs 14 = Z_to_bv 64 k ->
  getr regs 16 = Z_to_bv 64 maxv ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x39b3c) M rom)
    (fun fin => exists fr' cs' regs', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x39b78) M rom /\ frm_zero cs' /\
       fpv_read fr' FMT_S 15 = cvS (nc_val minv maxv (k + 1)) /\
       (forall r : reg, ~ In (ridx r) [14; 15]%nat -> reg_get fr' r = reg_get fr r) /\
       getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 8 = Z_to_bv 64 9 /\ getr regs' 9 = Z_to_bv 64 nc /\ getr regs' 10 = Z_to_bv 64 kx /\
       getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 i /\ getr regs' 5 = Z_to_bv 64 i /\
       getr regs' 14 = Z_to_bv 64 k /\ getr regs' 15 = Z_to_bv 64 (k + 1) /\
       getr regs' 16 = Z_to_bv 64 (kx + 4 * i) /\ getr regs' 17 = Z_to_bv 64 (kx + 4 * i) /\
       regs_agree (fun r => In r [5; 6; 7; 15; 16; 17]%list) regs regs').
Proof.
  intros fr cs regs M k i FZ Hk Hi Hin (Cmax & Cnc & Cnn & Cv & SOKk) H2 H8 H9 H10 H11 H12 H13 H14 H16.
  pose proof (Cv (k + 1)%Z ltac:(lia)) as Cn. pose proof (nc_val_rng minv maxv (k + 1) Hmin Hmax ltac:(lia)) as Hn.
  set (n := nc_val minv maxv (k + 1)) in *. clearbody n.
  kx_hcase k Cn.
  all: lazymatch type of Cn with rdn _ _ (Z_to_bv 64 (_ + ?off)) _ = _ =>
    kx_hrun regs fr i n FZ HR HK ST off true ltac:(rewrite xk_flt by lia; apply Z.ltb_lt; lia) [0x39b78%Z] (@nil bool) end.
  all: exb_exit ST R HR' Hlf Hms.
  all: eexists; split; [exact Hms|].
  all: do 3 eexists; split; [reflexivity|].
  all: split; [exact FZ|].
  all: split; [xb_rdfp; reflexivity|].
  all: split; [intros r Hr; rewrite !fpv_get_other; [apply fr_kept; cbn; tauto | intros ->; apply Hr; vm_compute; tauto ..]|].
  all: repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_agree HR HR' | ex_reg regs HR' ].
  all: kx_fin.
Qed.


#[local] Ltac kx_hcase7 k Cn :=
  assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7)%Z as KK by lia;
  destruct KK as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; cbn [Z.add Z.mul Pos.add Pos.mul Pos.succ] in Cn.

Lemma kx_hn : forall (fr : bvmap 5 word) cs regs (M : word -> option byte) (k i : Z),
  frm_zero cs -> (0 <= k < 8)%Z -> (0 <= i <= maxv)%Z -> (nc_val minv maxv (k + 1) <= i)%Z -> kx_M M ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 8 = Z_to_bv 64 9 -> getr regs 9 = Z_to_bv 64 nc -> getr regs 10 = Z_to_bv 64 kx ->
  getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 1 -> getr regs 13 = Z_to_bv 64 i -> getr regs 14 = Z_to_bv 64 k ->
  getr regs 16 = Z_to_bv 64 maxv ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x39b3c) M rom)
    (fun fin => exists fr' cs' regs', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x39b3c) M rom /\ frm_zero cs' /\
       (forall r : reg, ~ In (ridx r) [14; 15]%nat -> reg_get fr' r = reg_get fr r) /\
       getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 8 = Z_to_bv 64 9 /\ getr regs' 9 = Z_to_bv 64 nc /\ getr regs' 10 = Z_to_bv 64 kx /\
       getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 i /\
       getr regs' 14 = Z_to_bv 64 (k + 1) /\ getr regs' 16 = Z_to_bv 64 maxv /\
       regs_agree (fun r => In r [5; 6; 7; 14; 15; 16; 17]%list) regs regs').
Proof.
  intros fr cs regs M k i FZ Hk Hi Hin (Cmax & Cnc & Cnn & Cv & SOKk) H2 H8 H9 H10 H11 H12 H13 H14 H16.
  pose proof (Cv (k + 1)%Z ltac:(lia)) as Cn. pose proof (nc_val_rng minv maxv (k + 1) Hmin Hmax ltac:(lia)) as Hn.
  set (n := nc_val minv maxv (k + 1)) in *. clearbody n.
  kx_hcase7 k Cn.
  all: lazymatch type of Cn with rdn _ _ (Z_to_bv 64 (_ + ?off)) _ = _ =>
    kx_hrun regs fr i n FZ HR HK ST off false ltac:(rewrite xk_flt by lia; apply Z.ltb_ge; lia) [0x39b3c%Z] [false] end.
  all: exb_exit ST R HR' Hlf Hms.
  all: eexists; split; [exact Hms|].
  all: do 3 eexists; split; [reflexivity|].
  all: split; [exact FZ|].
  all: split; [intros r Hr; rewrite !fpv_get_other; [apply fr_kept; cbn; tauto | intros ->; apply Hr; vm_compute; tauto ..]|].
  all: repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_agree HR HR' | ex_reg regs HR' ].
  all: kx_fin.
Qed.

Lemma kx_hz : forall (fr : bvmap 5 word) cs regs (M : word -> option byte) (i : Z),
  frm_zero cs -> (0 <= i <= maxv)%Z -> (nc_val minv maxv 9 <= i)%Z -> kx_M M ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 8 = Z_to_bv 64 9 -> getr regs 9 = Z_to_bv 64 nc -> getr regs 10 = Z_to_bv 64 kx ->
  getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 1 -> getr regs 13 = Z_to_bv 64 i -> getr regs 14 = Z_to_bv 64 8 ->
  getr regs 16 = Z_to_bv 64 maxv ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x39b3c) M rom)
    (fun fin => exists fr' cs' regs', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x39bd4) M rom /\ frm_zero cs' /\
       (forall r : reg, ~ In (ridx r) [14; 15]%nat -> reg_get fr' r = reg_get fr r) /\
       getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 8 = Z_to_bv 64 9 /\ getr regs' 9 = Z_to_bv 64 nc /\ getr regs' 10 = Z_to_bv 64 kx /\
       getr regs' 16 = Z_to_bv 64 maxv /\
       regs_agree (fun r => In r [5; 6; 7; 14; 15; 16; 17]%list) regs regs').
Proof.
  intros fr cs regs M i FZ Hi Hin (Cmax & Cnc & Cnn & Cv & SOKk) H2 H8 H9 H10 H11 H12 H13 H14 H16.
  pose proof (Cv 9%Z ltac:(lia)) as Cn. pose proof (nc_val_rng minv maxv 9 Hmin Hmax ltac:(lia)) as Hn.
  set (n := nc_val minv maxv 9) in *. clearbody n. cbn [Z.add Z.mul Pos.add Pos.mul Pos.succ] in Cn.
  kx_hrun regs fr i n FZ HR HK ST 36%Z false ltac:(rewrite xk_flt by lia; apply Z.ltb_ge; lia) [0x39bd4%Z] [false].
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 3 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [intros r Hr; rewrite !fpv_get_other; [apply fr_kept; cbn; tauto | intros ->; apply Hr; vm_compute; tauto ..]|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_agree HR HR' | ex_reg regs HR' ].
  all: kx_fin.
Qed.


#[local] Ltac kx_erun regs FZ HR HK ST d stops :=
  ex_entry regs [(s - 320)%Z; nc; kx; minv; maxv] HR;
  assert (HK : know_ok SEGS (ex_env regs [(s - 320)%Z; nc; kx; minv; maxv]) _
     [KRange (EVar 32) 4096 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KRange (EVar 34) 4096 (2 ^ 47);
      KRange (EVar 35) 0 255; KRange (EVar 36) 0 255; KAlign (EVar 34) 16;
      KWr (SA (EVar 34) 0) 1024; KWr (SA (EVar 32) 64) 8;
      KWord (SA (EVar 32) 172) 4 (EVar 35); KWord (SA (EVar 32) 168) 4 (EVar 36); KWord (SA (EVar 32) 72) 8 (EVar 33);
      KDisj (SA (EVar 34) 0) 1024 (SA (EVar 32) 0) 320; KDisj (SA (EVar 33) 0) 40 (SA (EVar 32) 0) 320;
      KDisj (SA (EVar 34) 0) 1024 (SA (EVar 33) 0) 40]) by (ex_know regs);
  exb_open HR HK ST;
  exb_adriveS 8%nat 400%nat stops (SCR [d] [] []) (@nil (nat * nat)) HK ST FZ.

Lemma kx_e1 : forall (fr : bvmap 5 word) cs regs (m : word -> option byte),
  frm_zero cs -> (minv <= maxv)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 148)) 4 = Some (Z_to_le_bytes 4 minv) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 4 = Some (Z_to_le_bytes 4 maxv) ->
  rdn SEGS m (Z_to_bv 64 (s - 248)) 8 = Some (Z_to_le_bytes 8 nc) ->
  store_ok SEGS m (Z_to_bv 64 kx) 1024 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 256)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 10 = Z_to_bv 64 kx -> getr regs 9 = Z_to_bv 64 nc -> getr regs 8 = Z_to_bv 64 9 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x39b14) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x39b3c) M' rom /\ frm_zero cs' /\
       rinv [((s - 256)%Z, 8%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (s - 256)) 8 = Some (Z_to_le_bytes 8 (2 ^ 64 - 1 - nc)) /\
       (forall r : reg, reg_get fr' r = reg_get fr r) /\
       getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 8 = Z_to_bv 64 9 /\ getr regs' 9 = Z_to_bv 64 nc /\ getr regs' 10 = Z_to_bv 64 kx /\
       getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 minv /\
       getr regs' 14 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 maxv /\
       regs_agree (fun r => In r [11; 12; 13; 14; 16]%list) regs regs').
Proof.
  intros fr cs regs m FZ Hle Cmin Cmax Cnc SOKk SOKf H2 H10 H9 H8.
  kx_erun regs FZ HR HK ST false [0x39b3c%Z].
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((s - 256)%Z, 8%Z)]; exB_reg_tac idtac|].
  split; [bcellV HK Hlf regs (EVar 32) 64%Z ltac:(ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply xk_not; lia)|].
  split; [intros r; apply fr_kept; cbn; tauto|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_agree HR HR' | ex_reg regs HR' ].
  all: kx_fin.
Qed.

Lemma kx_e0 : forall (fr : bvmap 5 word) cs regs (m : word -> option byte),
  frm_zero cs -> (maxv < minv)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 148)) 4 = Some (Z_to_le_bytes 4 minv) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 4 = Some (Z_to_le_bytes 4 maxv) ->
  rdn SEGS m (Z_to_bv 64 (s - 248)) 8 = Some (Z_to_le_bytes 8 nc) ->
  store_ok SEGS m (Z_to_bv 64 kx) 1024 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 256)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 10 = Z_to_bv 64 kx -> getr regs 9 = Z_to_bv 64 nc -> getr regs 8 = Z_to_bv 64 9 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x39b14) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x39bd4) M' rom /\ frm_zero cs' /\
       rinv [((s - 256)%Z, 8%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (s - 256)) 8 = Some (Z_to_le_bytes 8 (2 ^ 64 - 1 - nc)) /\
       (forall r : reg, reg_get fr' r = reg_get fr r) /\
       getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 8 = Z_to_bv 64 9 /\ getr regs' 9 = Z_to_bv 64 nc /\ getr regs' 10 = Z_to_bv 64 kx /\
       getr regs' 16 = Z_to_bv 64 maxv /\
       regs_agree (fun r => In r [11; 12; 13; 14; 16]%list) regs regs').
Proof.
  intros fr cs regs m FZ Hle Cmin Cmax Cnc SOKk SOKf H2 H10 H9 H8.
  kx_erun regs FZ HR HK ST true [0x39bd4%Z].
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((s - 256)%Z, 8%Z)]; exB_reg_tac idtac|].
  split; [bcellV HK Hlf regs (EVar 32) 64%Z ltac:(ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply xk_not; lia)|].
  split; [intros r; apply fr_kept; cbn; tauto|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_agree HR HR' | ex_reg regs HR' ].
  all: kx_fin.
Qed.


Lemma kx_ag_keep : forall (L : list reg) regs regs' (r : reg) (v : word),
  regs_agree (fun x => In x L) regs regs' -> existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = false ->
  getr regs r = v -> getr regs' r = v.
Proof.
  intros L regs regs' r v AG E H. rewrite AG; [exact H|]. intros Hin.
  assert (T : existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = true).
  { apply existsb_exists. exists r. split; [exact Hin | apply Z.eqb_refl]. }
  congruence.
Qed.

Lemma kx_ag_comp : forall (L1 L2 L : list reg) r1 r2 r3,
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

Lemma kx_ag_refl : forall regs, regs_agree (fun x => In x (@nil reg)) regs regs.
Proof. intros regs r _. reflexivity. Qed.

#[local] Ltac agk AG H := apply (kx_ag_keep _ _ _ _ _ AG); [vm_compute; reflexivity | exact H].
#[local] Ltac agc A1 A2 := eapply kx_ag_comp; [exact A1 | exact A2 | vm_compute; reflexivity].

Definition kx_I (m0 M : word -> option byte) : Prop := kx_M M /\ kidx_ok kx M /\ rinv [(kx, 1024%Z); ((s - 256)%Z, 8%Z)] m0 M.

Definition kx_HR (regs : bvmap 5 word) (k i : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 (s - 320) /\ getr regs 8 = Z_to_bv 64 9 /\ getr regs 9 = Z_to_bv 64 nc /\ getr regs 10 = Z_to_bv 64 kx /\
  getr regs 11 = Z_to_bv 64 1 /\ getr regs 12 = Z_to_bv 64 1 /\ getr regs 13 = Z_to_bv 64 i /\ getr regs 14 = Z_to_bv 64 k /\
  getr regs 16 = Z_to_bv 64 maxv.

Definition kx_IR (regs : bvmap 5 word) (k i : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 (s - 320) /\ getr regs 8 = Z_to_bv 64 9 /\ getr regs 9 = Z_to_bv 64 nc /\ getr regs 10 = Z_to_bv 64 kx /\
  getr regs 11 = Z_to_bv 64 1 /\ getr regs 12 = Z_to_bv 64 1 /\ getr regs 13 = Z_to_bv 64 i /\ getr regs 5 = Z_to_bv 64 i /\
  getr regs 14 = Z_to_bv 64 k /\ getr regs 15 = Z_to_bv 64 (k + 1) /\
  getr regs 16 = Z_to_bv 64 (kx + 4 * i) /\ getr regs 17 = Z_to_bv 64 (kx + 4 * i).

Definition kx_POST (m0 : word -> option byte) (fr0 regs0 : bvmap 5 word) (fin : machine_state) : Prop :=
  exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x39bd4) M' rom /\ frm_zero cs' /\
    rinv [(kx, 1024%Z); ((s - 256)%Z, 8%Z)] m0 M' /\ kidx_ok kx M' /\
    rdn SEGS M' (Z_to_bv 64 (s - 256)) 8 = Some (Z_to_le_bytes 8 (2 ^ 64 - 1 - nc)) /\
    getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 10 = Z_to_bv 64 kx /\ getr regs' 16 = Z_to_bv 64 maxv /\
    getr regs' 8 = Z_to_bv 64 9 /\ getr regs' 9 = Z_to_bv 64 nc /\
    regs_agree (fun r => In r [5; 6; 7; 11; 12; 13; 14; 15; 16; 17]%list) regs0 regs' /\
    (forall r : reg, ~ In (ridx r) [14; 15]%nat -> reg_get fr' r = reg_get fr0 r).

Lemma kx_I_store : forall m0 M M' (i k : Z), kx_I m0 M -> (0 <= i < 256)%Z -> (0 <= k <= 8)%Z ->
  rinv [((kx + 4 * i)%Z, 4%Z)] M M' -> rdn SEGS M' (Z_to_bv 64 (kx + 4 * i)) 4 = Some (Z_to_le_bytes 4 k) -> kx_I m0 M'.
Proof.
  intros m0 M M' i k ((Cmax & Cnc & Cnn & Cv & SOKk) & KO & RI) Hi Hk R C.
  assert (D : forall z (n : nat), (0 <= z)%Z -> (z + Z.of_nat n <= 2 ^ 64)%Z -> (z + Z.of_nat n <= kx + 4 * i \/ kx + 4 * i + 4 <= z)%Z ->
                rdn SEGS M' (Z_to_bv 64 z) n = rdn SEGS M (Z_to_bv 64 z) n).
  { intros z n Hz Hzn Hd. apply (rinv_rdn SEGS _ _ _ z n R Hz Hzn). intros r Hr. destruct Hr as [<-|[]]. cbn. lia. }
  split; [|split].
  - split; [rewrite D by (cbn; lia); exact Cmax|]. split; [rewrite D by (cbn; lia); exact Cnc|].
    split; [rewrite D by (cbn; lia); exact Cnn|].
    split; [intros j Hj; rewrite D by (cbn; lia); apply Cv; exact Hj|].
    eapply store_ok_mono; [exact (proj1 R)|exact SOKk].
  - intros v Hv. destruct (Z.eq_dec v i) as [->|Hne].
    + exists k. split; [exact C|lia].
    + destruct (KO v Hv) as (kv & Rv & Hkv). exists kv. split; [|exact Hkv]. rewrite D by (cbn; lia). exact Rv.
  - eapply rinv_trans; [exact RI|]. eapply rinv_weaken; [exact R|]. intros r Hr. destruct Hr as [<-|[]].
    exists (kx, 1024%Z). split; [left; reflexivity|cbn; lia].
Qed.

Lemma kx_I_entry : forall m M', kidx_ok kx m ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 4 = Some (Z_to_le_bytes 4 maxv) ->
  rdn SEGS m (Z_to_bv 64 (s - 248)) 8 = Some (Z_to_le_bytes 8 nc) ->
  (forall j, (0 <= j < 10)%Z -> rdn SEGS m (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) ->
  store_ok SEGS m (Z_to_bv 64 kx) 1024 = true ->
  rinv [((s - 256)%Z, 8%Z)] m M' -> rdn SEGS M' (Z_to_bv 64 (s - 256)) 8 = Some (Z_to_le_bytes 8 (2 ^ 64 - 1 - nc)) -> kx_I m M'.
Proof.
  intros m M' KO Cmax Cnc Cv SOKk R C.
  assert (D : forall z (n : nat), (0 <= z)%Z -> (z + Z.of_nat n <= 2 ^ 64)%Z -> (z + Z.of_nat n <= s - 256 \/ s - 248 <= z)%Z ->
                rdn SEGS M' (Z_to_bv 64 z) n = rdn SEGS m (Z_to_bv 64 z) n).
  { intros z n Hz Hzn Hd. apply (rinv_rdn SEGS _ _ _ z n R Hz Hzn). intros r Hr. destruct Hr as [<-|[]]. cbn. lia. }
  split; [|split].
  - split; [rewrite D by (cbn; lia); exact Cmax|]. split; [rewrite D by (cbn; lia); exact Cnc|].
    split; [exact C|].
    split; [intros j Hj; rewrite D by (cbn; lia); apply Cv; exact Hj|].
    eapply store_ok_mono; [exact (proj1 R)|exact SOKk].
  - intros v Hv. destruct (KO v Hv) as (kv & Rv & Hkv). exists kv. split; [|exact Hkv]. rewrite D by (cbn; lia). exact Rv.
  - eapply rinv_weaken; [exact R|]. intros r Hr. destruct Hr as [<-|[]].
    exists ((s - 256)%Z, 8%Z). split; [right; left; reflexivity|cbn; lia].
Qed.

Lemma kx_fk1 : forall (fr fr' fr0 : bvmap 5 word),
  (forall r : reg, ~ In (ridx r) [14]%nat -> reg_get fr' r = reg_get fr r) ->
  (forall r : reg, ~ In (ridx r) [14; 15]%nat -> reg_get fr r = reg_get fr0 r) ->
  (forall r : reg, ~ In (ridx r) [14; 15]%nat -> reg_get fr' r = reg_get fr0 r).
Proof. intros fr fr' fr0 A B r Hr. rewrite A; [apply B, Hr|]. intros H. apply Hr. cbn in *. tauto. Qed.

Lemma kx_fk2 : forall (fr fr' fr0 : bvmap 5 word),
  (forall r : reg, ~ In (ridx r) [14; 15]%nat -> reg_get fr' r = reg_get fr r) ->
  (forall r : reg, ~ In (ridx r) [14; 15]%nat -> reg_get fr r = reg_get fr0 r) ->
  (forall r : reg, ~ In (ridx r) [14; 15]%nat -> reg_get fr' r = reg_get fr0 r).
Proof. intros fr fr' fr0 A B r Hr. rewrite A; [apply B, Hr|exact Hr]. Qed.

(* [comment removed for export] *)
Lemma kx_inner : forall (j : nat) m0 (fr0 regs0 fr : bvmap 5 word) cs regs (M : word -> option byte) (k i n : Z),
  Z.of_nat j = (n - i)%Z -> (0 <= k <= 8)%Z -> (0 <= i < n)%Z -> (n <= maxv)%Z -> frm_zero cs -> kx_I m0 M ->
  fpv_read fr FMT_S 15 = cvS n -> kx_IR regs k i ->
  regs_agree (fun r => In r [5; 6; 7; 11; 12; 13; 14; 15; 16; 17]%list) regs0 regs ->
  (forall r : reg, ~ In (ridx r) [14; 15]%nat -> reg_get fr r = reg_get fr0 r) ->
  ((k < 8)%Z -> forall (fr1 : bvmap 5 word) cs1 regs1 (M1 : word -> option byte), frm_zero cs1 -> kx_I m0 M1 -> kx_HR regs1 (k + 1) n ->
     regs_agree (fun r => In r [5; 6; 7; 11; 12; 13; 14; 15; 16; 17]%list) regs0 regs1 ->
     (forall r : reg, ~ In (ridx r) [14; 15]%nat -> reg_get fr1 r = reg_get fr0 r) ->
     reach SEGS (@mkst (mkFP fr1 cs1) regs1 (Z_to_bv 64 0x39b3c) M1 rom) (kx_POST m0 fr0 regs0)) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x39b78) M rom) (kx_POST m0 fr0 regs0).
Proof.
  induction j as [|j IH]; intros m0 fr0 regs0 fr cs regs M k i n Hj Hk Hi Hn FZ HI F15
    (G2 & G8 & G9 & G10 & G11 & G12 & G13 & G5 & G14 & G15 & G16 & G17) AG FK CONT.
  { cbn [Z.of_nat] in Hj. lia. }
  pose proof HI as (KMM & _ & _).
  destruct (Z_lt_ge_dec (i + 1) n) as [Hc|Hc].
  - eapply reach_bind; [exact (kx_bc fr cs regs M i n k FZ ltac:(lia) Hc ltac:(lia) Hk KMM F15 G2 G8 G9 G10 G11 G12 G13 G5 G14 G15 G16 G17)|].
    intros fin (fr' & cs' & regs' & M' & -> & FZ' & R & C & F15' & FK' & K13 & K5 & K16 & K17 & AG').
    apply (IH m0 fr0 regs0 fr' cs' regs' M' k (i + 1)%Z n ltac:(lia) Hk ltac:(lia) Hn FZ'
             (kx_I_store m0 M M' i k HI ltac:(lia) Hk R C) F15'); [| agc AG AG' | exact (kx_fk1 fr fr' fr0 FK' FK) | exact CONT].
    repeat split; first [ assumption | agk AG' G2 | agk AG' G8 | agk AG' G9 | agk AG' G10 | agk AG' G11 | agk AG' G12
                        | agk AG' G14 | agk AG' G15 ].
  - destruct (Z_lt_ge_dec k 8) as [Hk8|Hk8].
    + eapply reach_bind; [exact (kx_bx fr cs regs M i n k FZ ltac:(lia) ltac:(lia) ltac:(lia) Hn ltac:(lia) KMM F15 G2 G8 G9 G10 G11 G12 G13 G5 G14 G15 G16 G17)|].
      intros fin (fr' & cs' & regs' & M' & -> & FZ' & R & C & FK' & K2 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K16 & AG').
      apply (CONT Hk8 fr' cs' regs' M' FZ' (kx_I_store m0 M M' i k HI ltac:(lia) Hk R C)); [| agc AG AG' | exact (kx_fk1 fr fr' fr0 FK' FK)].
      replace n with (i + 1)%Z by lia. repeat split; assumption.
    + assert (k = 8)%Z as -> by lia.
      eapply reach_bind; [exact (kx_bz fr cs regs M i n FZ ltac:(lia) ltac:(lia) ltac:(lia) Hn KMM F15 G2 G8 G9 G10 G11 G12 G13 G5 G14 G15 G16 G17)|].
      intros fin (fr' & cs' & regs' & M' & -> & FZ' & R & C & FK' & K2 & K8 & K9 & K10 & K16 & AG').
      pose proof (kx_I_store m0 M M' i 8 HI ltac:(lia) ltac:(lia) R C) as ((_ & _ & Cnn' & _ & _) & KO' & RI').
      apply reach_done. exists fr', cs', regs', M'. split; [reflexivity|].
      split; [exact FZ'|]. split; [exact RI'|]. split; [exact KO'|]. split; [exact Cnn'|].
      split; [exact K2|]. split; [exact K10|]. split; [exact K16|]. split; [exact K8|]. split; [exact K9|].
      split; [agc AG AG'|exact (kx_fk1 fr fr' fr0 FK' FK)].
Qed.

(* [comment removed for export] *)
Lemma kx_outer : (minv <= maxv)%Z -> forall (j : nat) m0 (fr0 regs0 fr : bvmap 5 word) cs regs (M : word -> option byte) (k i : Z),
  Z.of_nat j = (9 - k)%Z -> (0 <= k <= 8)%Z -> (0 <= i <= maxv)%Z -> frm_zero cs -> kx_I m0 M -> kx_HR regs k i ->
  regs_agree (fun r => In r [5; 6; 7; 11; 12; 13; 14; 15; 16; 17]%list) regs0 regs ->
  (forall r : reg, ~ In (ridx r) [14; 15]%nat -> reg_get fr r = reg_get fr0 r) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x39b3c) M rom) (kx_POST m0 fr0 regs0).
Proof.
  intros Hle j; induction j as [|j IH]; intros m0 fr0 regs0 fr cs regs M k i Hj Hk Hi FZ HI
    (G2 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G16) AG FK.
  { cbn [Z.of_nat] in Hj. lia. }
  pose proof HI as (KMM & _ & _).
  pose proof (nc_val_rng minv maxv (k + 1) Hmin Hmax ltac:(lia)) as Hn.
  assert (Hnm : (nc_val minv maxv (k + 1) <= maxv)%Z).
  { unfold nc_val. assert (Z.quot ((maxv - minv) * (k + 1)) 9 <= maxv - minv)%Z; [|lia].
    rewrite Z.quot_div_nonneg by nia. apply Z.div_le_upper_bound; nia. }
  destruct (Z_lt_ge_dec i (nc_val minv maxv (k + 1))) as [Hc|Hc].
  - eapply reach_bind; [exact (kx_ht fr cs regs M k i FZ Hk ltac:(lia) Hc KMM G2 G8 G9 G10 G11 G12 G13 G14 G16)|].
    intros fin (fr' & cs' & regs' & -> & FZ' & F15' & FK' & K2 & K8 & K9 & K10 & K11 & K12 & K13 & K5 & K14 & K15 & K16 & K17 & AG').
    apply (kx_inner (Z.to_nat (nc_val minv maxv (k + 1) - i)) m0 fr0 regs0 fr' cs' regs' M k i (nc_val minv maxv (k + 1))
             ltac:(lia) Hk ltac:(lia) Hnm FZ' HI F15'); [repeat split; assumption | agc AG AG' | exact (kx_fk2 fr fr' fr0 FK' FK) |].
    intros Hk8 fr1 cs1 regs1 M1 FZ1 HI1 HR1 AG1 FK1.
    exact (IH m0 fr0 regs0 fr1 cs1 regs1 M1 (k + 1)%Z (nc_val minv maxv (k + 1)) ltac:(lia) ltac:(lia) ltac:(lia) FZ1 HI1 HR1 AG1 FK1).
  - destruct (Z_lt_ge_dec k 8) as [Hk8|Hk8].
    + eapply reach_bind; [exact (kx_hn fr cs regs M k i FZ ltac:(lia) Hi ltac:(lia) KMM G2 G8 G9 G10 G11 G12 G13 G14 G16)|].
      intros fin (fr' & cs' & regs' & -> & FZ' & FK' & K2 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K16 & AG').
      exact (IH m0 fr0 regs0 fr' cs' regs' M (k + 1)%Z i ltac:(lia) ltac:(lia) Hi FZ' HI
               ltac:(repeat split; assumption) ltac:(agc AG AG') (kx_fk2 fr fr' fr0 FK' FK)).
    + assert (k = 8)%Z as -> by lia.
      eapply reach_bind; [exact (kx_hz fr cs regs M i FZ Hi ltac:(replace 9%Z with (8 + 1)%Z by reflexivity; lia) KMM G2 G8 G9 G10 G11 G12 G13 G14 G16)|].
      intros fin (fr' & cs' & regs' & -> & FZ' & FK' & K2 & K8 & K9 & K10 & K16 & AG').
      pose proof HI as ((_ & _ & Cnn' & _ & _) & KO' & RI').
      apply reach_done. exists fr', cs', regs', M. split; [reflexivity|].
      split; [exact FZ'|]. split; [exact RI'|]. split; [exact KO'|]. split; [exact Cnn'|].
      split; [exact K2|]. split; [exact K10|]. split; [exact K16|]. split; [exact K8|]. split; [exact K9|].
      split; [agc AG AG'|exact (kx_fk2 fr fr' fr0 FK' FK)].
Qed.

Lemma kx_main : forall (fr : bvmap 5 word) cs regs (m : word -> option byte),
  frm_zero cs ->
  rdn SEGS m (Z_to_bv 64 (s - 148)) 4 = Some (Z_to_le_bytes 4 minv) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 4 = Some (Z_to_le_bytes 4 maxv) ->
  rdn SEGS m (Z_to_bv 64 (s - 248)) 8 = Some (Z_to_le_bytes 8 nc) ->
  (forall j, (0 <= j < 10)%Z -> rdn SEGS m (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) ->
  store_ok SEGS m (Z_to_bv 64 kx) 1024 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 256)) 8 = true ->
  kidx_ok kx m ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 10 = Z_to_bv 64 kx -> getr regs 9 = Z_to_bv 64 nc -> getr regs 8 = Z_to_bv 64 9 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x39b14) m rom) (kx_POST m fr regs).
Proof.
  intros fr cs regs m FZ Cmin Cmax Cnc Cv SOKk SOKf KO H2 H10 H9 H8.
  destruct (Z_le_gt_dec minv maxv) as [Hle|Hgt].
  - eapply reach_bind; [exact (kx_e1 fr cs regs m FZ Hle Cmin Cmax Cnc SOKk SOKf H2 H10 H9 H8)|].
    intros fin (fr' & cs' & regs' & M' & -> & FZ' & R & C & FK' & K2 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K16 & AG').
    apply (kx_outer Hle 9 m fr regs fr' cs' regs' M' 0 minv eq_refl ltac:(lia) ltac:(lia) FZ'
             (kx_I_entry m M' KO Cmax Cnc Cv SOKk R C)); [repeat split; assumption | | intros r _; apply FK'].
    pose proof (kx_ag_refl regs) as A0. agc A0 AG'.
  - eapply reach_bind; [exact (kx_e0 fr cs regs m FZ ltac:(lia) Cmin Cmax Cnc SOKk SOKf H2 H10 H9 H8)|].
    intros fin (fr' & cs' & regs' & M' & -> & FZ' & R & C & FK' & K2 & K8 & K9 & K10 & K16 & AG').
    pose proof (kx_I_entry m M' KO Cmax Cnc Cv SOKk R C) as (_ & KO' & RI').
    apply reach_done. exists fr', cs', regs', M'. split; [reflexivity|].
    split; [exact FZ'|]. split; [exact RI'|]. split; [exact KO'|]. split; [exact C|].
    split; [exact K2|]. split; [exact K10|]. split; [exact K16|]. split; [exact K8|]. split; [exact K9|].
    split; [pose proof (kx_ag_refl regs) as A0; agc A0 AG'|intros r _; apply FK'].
Qed.

End KX.

(* [comment removed for export] *)
Lemma kidx_seg : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s nc kx minv maxv : Z),
  frm_zero cs ->
  (4096 + 320 <= s <= 2 ^ 47)%Z ->
  (4096 <= nc)%Z -> (nc + 40 <= s - 320)%Z ->
  (4096 <= kx)%Z -> (kx + 1024 <= s - 320)%Z -> (kx mod 16 = 0)%Z ->
  (kx + 1024 <= nc \/ nc + 40 <= kx)%Z ->
  (0 <= minv <= 255)%Z -> (0 <= maxv <= 255)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 148)) 4 = Some (Z_to_le_bytes 4 minv) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 4 = Some (Z_to_le_bytes 4 maxv) ->
  rdn SEGS m (Z_to_bv 64 (s - 248)) 8 = Some (Z_to_le_bytes 8 nc) ->
  (forall j, (0 <= j < 10)%Z -> rdn SEGS m (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) ->
  store_ok SEGS m (Z_to_bv 64 kx) 1024 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 256)) 8 = true ->
  kidx_ok kx m ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 10 = Z_to_bv 64 kx -> getr regs 9 = Z_to_bv 64 nc -> getr regs 8 = Z_to_bv 64 9 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x39b14) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x39bd4) M' rom /\ frm_zero cs' /\
      rinv [(kx, 1024%Z); ((s - 256)%Z, 8%Z)] m M' /\ kidx_ok kx M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 256)) 8 = Some (Z_to_le_bytes 8 (2 ^ 64 - 1 - nc)) /\
      getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 10 = Z_to_bv 64 kx /\ getr regs' 16 = Z_to_bv 64 maxv /\
      getr regs' 8 = Z_to_bv 64 9 /\ getr regs' 9 = Z_to_bv 64 nc /\
      regs_agree (fun r => In r [5; 6; 7; 11; 12; 13; 14; 15; 16; 17]%list) regs regs' /\
      (forall r : reg, ~ In (ridx r) [14; 15]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s nc kx minv maxv FZ Hs Hn1 Hn2 Hk1 Hk2 ALk APnk Hmin Hmax Cmin Cmax Cnc Cv SOKk SOKf KO H2 H10 H9 H8.
  exact (kx_main s nc kx minv maxv Hs Hn1 Hn2 Hk1 Hk2 ALk APnk Hmin Hmax fr cs regs m FZ Cmin Cmax Cnc Cv SOKk SOKf KO H2 H10 H9 H8).
Qed.

End BilSegsK.
