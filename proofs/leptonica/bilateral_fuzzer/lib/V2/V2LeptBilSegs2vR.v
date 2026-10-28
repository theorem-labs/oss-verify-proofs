(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith DitherLib LeptExec LeptExecW LeptExecFP LeptExecX LeptExecB LeptArithB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import FpReal FpBound FpSiteC.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptBilSegs V2LeptBilSegs2.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

#[local] Opaque RiscvSemantics.store_ok.

Lemma vx_fr_keep : forall E L fr (r : reg), fr_find L (ridx r) = None -> reg_get (fr_denot E L fr) r = reg_get fr r.
Proof. intros E L fr r H. rewrite fr_get, H. reflexivity. Qed.
Lemma vx_fr_find_none : forall L k, Forall (fun kv => ridx (fst kv) <> k) L -> fr_find L k = None.
Proof.
  induction L as [|[r e] L IH]; intros k H; [reflexivity|].
  inversion H as [|? ? H1 H2]; subst. cbn [fr_find].
  destruct (Nat.eqb (ridx r) k) eqn:E; [apply Nat.eqb_eq in E; contradiction | apply IH; exact H2].
Qed.
Lemma vx_xor_eq : forall a b, a = b -> v_xor (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof. intros a b ->. unfold v_xor. rewrite Z.lxor_nilpotent. reflexivity. Qed.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma vx_xor3 : forall a : Z, (0 <= a < 2 ^ 64)%Z -> v_xor (Z_to_bv 64 a) (Z_to_bv 64 3) = Z_to_bv 64 (a - a mod 4 + (3 - a mod 4)).
Proof. intros a Ha. rewrite <- (zbv_xori3 a Ha). unfold v_xor, v_xori. f_equal. Qed.
Lemma vx_xor_lit : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> v_xor (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lxor a b).
Proof. intros a b Ha Hb. unfold v_xor. rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma vx_xor3_in : forall lined j W : Z, (lined mod 4 = 0)%Z -> (0 <= j < 4 * W)%Z ->
  (lined <= (lined + j) - (lined + j) mod 4 + (3 - (lined + j) mod 4) < lined + 4 * W)%Z.
Proof. intros lined j W H1 H2. lia. Qed.
Lemma vx_line4 : forall d i wpld : Z, (d mod 4 = 0)%Z -> ((d + 4 * (i * wpld)) mod 4 = 0)%Z.
Proof. intros d i wpld H. lia. Qed.
Lemma vx_wpld : forall w, (1 <= w)%Z -> (1 <= wpl_of w 8 /\ w <= 4 * wpl_of w 8)%Z.
Proof. intros w Hw. unfold wpl_of. lia. Qed.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Ltac vnorm := repeat first [ rewrite ex_sx32 by lia | rewrite bw_low32 | rewrite bw_alu32_add | rewrite bw_alu32_sub
  | rewrite bw_md32_mul | rewrite bw_sext64 by lia | rewrite alu_add | rewrite alu_sub | rewrite m_mul | rewrite zbv_add
  | rewrite zbv_sub | rewrite zbv_mul | rewrite Z.add_0_r ].
#[local] Ltac zltb := repeat match goal with |- context [(?a <? ?b)%Z] =>
  first [ replace (a <? b)%Z with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b)%Z with false by (symmetry; apply Z.ltb_ge; lia) ] end.
#[local] Ltac vreg := first [ reflexivity | (rewrite zbv_addw_small by lia; reflexivity) | (vnorm; reflexivity) | (f_equal; lia) ].
#[local] Ltac vdef := repeat rewrite ext_val_sx_id by (first [ lia | (rewrite ?u_Z2bv by lia; ex_pow2; lia) ]);
  rewrite ?w_addw; rewrite ?zbv_addw_small by lia; ex_br.
#[local] Ltac vovf := vnorm; rewrite ?alu_sltu, ?alu_slt, ?alu_xor; rewrite exB_ovf_idiom by lia;
  lazymatch goal with |- branch_taken _ (Z_to_bv 64 _) (Z_to_bv 64 _) = _ => reflexivity end.
#[local] Ltac vsok := lazymatch goal with |- RiscvSemantics.store_ok _ _ _ _ = true =>
  rewrite ?alu_xor, ?alu_add; rewrite ?zbv_add; rewrite ?vx_xor3 by lia; rewrite ?zbv_addi;
  match goal with H : RiscvSemantics.store_ok _ _ (Z_to_bv 64 _) _ = true |- _ =>
    eapply store_ok_sub; [ | exact H | | ]; rewrite ?u_Z2bv by lia; rewrite ?Z2Nat.id by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia end end.
#[local] Ltac vfrm := rewrite ?alu_xor; rewrite ?vx_xor3 by lia; rewrite ?u_Z2bv by lia; lia.
#[local] Ltac exB_sc_hook ::= first [ vdef | vsok | (vnorm; apply br_ne_same; reflexivity) | vovf | vfrm ].
#[local] Ltac vreg2 := repeat first [ rewrite zbv_addw_small by lia | rewrite m_mul | rewrite zbv_mul | rewrite zbv_add | rewrite Z.add_0_r ];
  rewrite ?v_sltu_Z by lia; zltb; first [ reflexivity | (f_equal; lia) ].
#[local] Ltac fr_keep2 :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Heq := fresh "Heq" in
  intros r Hr; apply vx_fr_keep; apply vx_fr_find_none;
  repeat (apply Forall_cons; [cbn [fst]; intro Heq; apply Hr; rewrite <- Heq; vm_compute; tauto |]); apply Forall_nil.
#[local] Ltac fr_lit := lazymatch goal with |- reg_get (fr_denot ?E ?L ?fr) ?r = Z_to_bv 64 ?z =>
  apply (fr_get_lit E L fr r z); vm_compute; reflexivity end.
#[local] Ltac vreg4 := first [ (rewrite vx_xor_eq by lia; reflexivity)
  | (rewrite v_slt_Z by lia; zltb; reflexivity)
  | (rewrite v_sltu_Z by lia; zltb; reflexivity)
  | (f_equal; lia)
  | (apply bv_eq; reflexivity)
  | reflexivity ].

Section Segs.
Variable rom : word -> option byte.
#[local] Existing Instance exf_fxd | 100.

Lemma v_rowset : forall (fr : bvmap 5 word) cs regs (M : word -> option byte) (s datat datad wpl wpld w h i : Z),
  frm_zero cs ->
  (4096 + 320 <= s <= 2 ^ 47)%Z -> (s mod 16 = 0)%Z ->
  (1 <= w)%Z -> (1 <= h)%Z -> (w + 22 <= 20000)%Z -> (h + 22 <= 20000)%Z -> wpl = wpl_of (w + 22) 8 -> (4 * (wpl * (h + 22)) <= 67108864)%Z ->
  wpld = wpl_of w 8 -> (0 <= i < h)%Z ->
  (4096 <= datat)%Z -> (datat + 4 * (wpl * (h + 22)) <= 2 ^ 47)%Z -> (datat mod 4 = 0)%Z ->
  (4096 <= datad)%Z -> (datad + 4 * (wpld * h) <= 2 ^ 47)%Z -> (datad mod 4 = 0)%Z ->
  rdn SEGS M (Z_to_bv 64 (s - 232)) 8 = Some (Z_to_le_bytes 8 datad) ->
  rdn SEGS M (Z_to_bv 64 (s - 208)) 8 = Some (Z_to_le_bytes 8 datat) ->
  rdn SEGS M (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS M (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 w) ->
  getr regs 1 = Z_to_bv 64 11 -> getr regs 2 = Z_to_bv 64 (s - 320) ->
  getr regs 10 = Z_to_bv 64 wpld -> getr regs 11 = Z_to_bv 64 i -> getr regs 24 = Z_to_bv 64 1 -> getr regs 25 = Z_to_bv 64 wpl ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a2e4) M rom)
    (fun fin => exists regs' M', fin = @mkst (mkFP fr cs) regs' (Z_to_bv 64 0x3a380) M' rom /\
       getr regs' 12 = Z_to_bv 64 (datat + 4 * ((i + 11) * wpl)) /\ getr regs' 13 = Z_to_bv 64 1 /\
       getr regs' 14 = Z_to_bv 64 (datad + 4 * (i * wpld)) /\ getr regs' 15 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 0 /\
       regs_agree (fun r => In r [12; 13; 14; 15; 16]%list) regs regs' /\ M' = M).
Proof.
  intros fr cs regs M s datat datad wpl wpld w h i FZ Hs Hs16 Hw Hh Hw2 Hh2 Ewpl Hwph Ewpld Hi Ht1 Ht2 Ht3 Hd1 Hd2 Hd3
    Cd Ct C0 Cw H1 H2 H10 H11 H24 H25.
  assert (Hwp : (1 <= wpl <= 20000)%Z) by (subst wpl; unfold wpl_of; split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
  assert (Hwpd : (1 <= wpld <= wpl)%Z) by (subst wpld wpl; unfold wpl_of; split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_mono; lia]).
  clear Ewpl Ewpld.
  assert (B1 : (0 <= (i + 11) * wpl /\ (i + 11) * wpl + wpl <= wpl * (h + 22))%Z) by nia.
  assert (B2 : (0 <= i * wpld /\ i * wpld + wpld <= wpld * h)%Z) by nia.
  assert (B3 : (4 * (wpld * h) <= 67108864)%Z) by nia.
  assert (B4 : (1 <= wpl)%Z) by lia. assert (B5 : (1 <= wpld)%Z) by lia.
  ex_entry regs [s; datat; datad; wpl; wpld; w; h; i] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datat; datad; wpl; wpld; w; h; i]) M
     [KRange (EVar 32) 4416 (2 ^ 47); KAlign (EVar 32) 16;
      KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 4; KRange (EVar 34) 4096 (2 ^ 47); KAlign (EVar 34) 4;
      KRange (EVar 35) 1 20000; KRange (EVar 36) 1 20000; KRange (EVar 37) 1 19978; KRange (EVar 38) 1 19978;
      KRange (EVar 39) 0 19977;
      KWord (SA (EVar 32) (-232)) 8 (EVar 34); KWord (SA (EVar 32) (-208)) 8 (EVar 33);
      KWord (SA (EVar 32) (-192)) 8 (ELit 0); KWord (SA (EVar 32) (-184)) 8 (EVar 37)]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adriveS 8%nat 400%nat [0x3a380%Z; 0x3a2d8%Z] (SCR (repeat false 12) [] []) (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_agree HR HR' | ex_reg regs HR' | reflexivity ].
  all: vreg2.
Qed.

Lemma v_latch : forall (fr : bvmap 5 word) cs regs (M : word -> option byte) (s h i : Z),
  frm_zero cs ->
  (4096 + 320 <= s <= 2 ^ 47)%Z -> (s mod 16 = 0)%Z ->
  (1 <= h)%Z -> (h + 22 <= 20000)%Z -> (0 <= i < h)%Z ->
  rdn SEGS M (Z_to_bv 64 (s - 216)) 8 = Some (Z_to_le_bytes 8 h) ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 11 = Z_to_bv 64 i ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a2d8) M rom)
    (fun fin => exists regs' M', fin = @mkst (mkFP fr cs) regs' (Z_to_bv 64 (if (i + 1 <? h)%Z then 0x3a2e4 else 0x3a010)) M' rom /\
       getr regs' 11 = Z_to_bv 64 (i + 1) /\ getr regs' 12 = Z_to_bv 64 h /\
       regs_agree (fun r => In r [11; 12]%list) regs regs' /\ M' = M).
Proof.
  intros fr cs regs M s h i FZ Hs Hs16 Hh Hh2 Hi Ch H2 H11.
  ex_entry regs [s; h; i] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; h; i]) M
     [KRange (EVar 32) 4416 (2 ^ 47); KAlign (EVar 32) 16; KRange (EVar 33) 1 19978; KRange (EVar 34) 0 19977;
      KWord (SA (EVar 32) (-216)) 8 (EVar 33)]) by (ex_know regs).
  destruct (Z_lt_ge_dec (i + 1) h) as [Hc|Hc].
  - replace (i + 1 <? h)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    exb_open HR HK ST.
    exb_adriveS 8%nat 400%nat [0x3a2e4%Z] (SCR [false] [] []) (@nil (nat * nat)) HK ST FZ.
    exb_exit ST R HR' Hlf Hms.
    eexists; split; [exact Hms|].
    do 2 eexists; split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end.
    all: first [ ex_agree HR HR' | ex_reg regs HR' | reflexivity ].
    all: vreg.
  - replace (i + 1 <? h)%Z with false by (symmetry; apply Z.ltb_ge; lia).
    exb_open HR HK ST.
    exb_adriveS 8%nat 400%nat [0x3a010%Z] (SCR [true] [] []) (@nil (nat * nat)) HK ST FZ.
    exb_exit ST R HR' Hlf Hms.
    eexists; split; [exact Hms|].
    do 2 eexists; split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end.
    all: first [ ex_agree HR HR' | ex_reg regs HR' | reflexivity ].
    all: vreg.
Qed.

Lemma v_store : forall (fr : bvmap 5 word) cs regs (M : word -> option byte) (s datad wpld w h i j v : Z),
  frm_zero cs ->
  (4096 + 320 <= s <= 2 ^ 47)%Z -> (s mod 16 = 0)%Z ->
  (1 <= w)%Z -> (1 <= h)%Z -> (w + 22 <= 20000)%Z -> (h + 22 <= 20000)%Z -> wpld = wpl_of w 8 ->
  (0 <= i < h)%Z -> (0 <= j < w)%Z -> (0 <= v <= 255)%Z ->
  (4096 <= datad)%Z -> (datad + 4 * (wpld * h) <= 2 ^ 47)%Z -> (datad mod 4 = 0)%Z ->
  (datad + 4 * (wpld * h) <= s - 320 \/ s <= datad)%Z ->
  store_ok SEGS M (Z_to_bv 64 datad) (Z.to_nat (4 * (wpld * h))) = true ->
  rdn SEGS M (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 w) ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 (datad + 4 * (i * wpld)) ->
  getr regs 15 = Z_to_bv 64 j -> getr regs 16 = Z_to_bv 64 v ->
  getr regs 19 = Z_to_bv 64 (- 2 ^ 31) -> getr regs 20 = Z_to_bv 64 1 -> getr regs 22 = Z_to_bv 64 3 -> getr regs 24 = Z_to_bv 64 1 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a4f8) M rom)
    (fun fin => exists regs' M', fin = @mkst (mkFP fr cs) regs' (Z_to_bv 64 (if (j + 1 <? w)%Z then 0x3a380 else 0x3a2d8)) M' rom /\
       getr regs' 5 = Z_to_bv 64 0 /\ getr regs' 15 = Z_to_bv 64 (j + 1) /\ getr regs' 16 = Z_to_bv 64 w /\
       getr regs' 17 = Z_to_bv 64 (Z.lxor (datad + 4 * (i * wpld) + j) 3) /\
       regs_agree (fun r => In r [5; 15; 16; 17]%list) regs regs' /\
       rinv [(datad, (4 * (wpld * h))%Z)] M M').
Proof.
  intros fr cs regs M s datad wpld w h i j v FZ Hs Hs16 Hw Hh Hw2 Hh2 Ewpld Hi Hj Hv Hd1 Hd2 Hd3 Hds SOK Cw
    H2 H13 H14 H15 H16 H19 H20 H22 H24.
  pose proof (vx_wpld w Hw) as (Hwpd & Hww). rewrite <- Ewpld in Hwpd, Hww. clear Ewpld.
  assert (B2 : (0 <= i * wpld /\ i * wpld + wpld <= wpld * h)%Z) by nia.
  ex_entry regs [s; datad; w; (datad + 4 * (i * wpld))%Z; j; v] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; w; (datad + 4 * (i * wpld))%Z; j; v]) M
     [KRange (EVar 32) 4416 (2 ^ 47); KAlign (EVar 32) 16;
      KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 4; KRange (EVar 34) 1 19978; KRange (EVar 35) 4096 (2 ^ 47); KAlign (EVar 35) 4;
      KRange (EVar 36) 0 19977; KRange (EVar 37) 0 255;
      KWord (SA (EVar 32) (-184)) 8 (EVar 34)]).
  { ex_know regs. all: exact (vx_line4 datad i wpld Hd3). }
  pose proof (vx_xor3_in (datad + 4 * (i * wpld)) j wpld (vx_line4 datad i wpld Hd3) ltac:(lia)) as P.
  destruct (Z_lt_ge_dec (j + 1) w) as [Hc|Hc].
  - replace (j + 1 <? w)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    exb_open HR HK ST.
    exb_adriveS 8%nat 400%nat [0x3a380%Z; 0x3a2d8%Z] (SCR [false; true] [] []) (@nil (nat * nat)) HK ST FZ.
    exb_exit ST R HR' Hlf Hms.
    eexists; split; [exact Hms|].
    do 2 eexists; split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end.
    all: try first [ ex_agree HR HR' | ex_reg regs HR' ].
    { vreg4. }
    { rewrite vx_xor_lit by lia. reflexivity. }
    exB_rinv_tac Hlf [(datad, (4 * (wpld * h))%Z)]; exB_reg_tac ltac:(rewrite ?alu_xor, ?alu_add; rewrite ?zbv_add; rewrite ?vx_xor3 by lia).
  - replace (j + 1 <? w)%Z with false by (symmetry; apply Z.ltb_ge; lia).
    exb_open HR HK ST.
    exb_adriveS 8%nat 400%nat [0x3a380%Z; 0x3a2d8%Z] (SCR [false; false] [] []) (@nil (nat * nat)) HK ST FZ.
    exb_exit ST R HR' Hlf Hms.
    eexists; split; [exact Hms|].
    do 2 eexists; split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end.
    all: try first [ ex_agree HR HR' | ex_reg regs HR' ].
    { vreg4. }
    { rewrite vx_xor_lit by lia. reflexivity. }
    exB_rinv_tac Hlf [(datad, (4 * (wpld * h))%Z)]; exB_reg_tac ltac:(rewrite ?alu_xor, ?alu_add; rewrite ?zbv_add; rewrite ?vx_xor3 by lia).
Qed.

Lemma v_colent : forall (fr : bvmap 5 word) cs regs (M : word -> option byte) (s w j : Z),
  frm_zero cs ->
  (4096 + 320 <= s <= 2 ^ 47)%Z -> (s mod 16 = 0)%Z ->
  (1 <= w)%Z -> (w + 22 <= 20000)%Z -> (0 <= j < w)%Z ->
  reg_get fr 18 = Z_to_bv 64 bc_fzero ->
  getr regs 1 = Z_to_bv 64 11 -> getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 8 = Z_to_bv 64 (-10) -> getr regs 15 = Z_to_bv 64 j ->
  getr regs 18 = Z_to_bv 64 10 -> getr regs 19 = Z_to_bv 64 (- 2 ^ 31) -> getr regs 20 = Z_to_bv 64 1 ->
  getr regs 22 = Z_to_bv 64 3 -> getr regs 24 = Z_to_bv 64 1 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a380) M rom)
    (fun fin => exists fr' regs' M', fin = @mkst (mkFP fr' cs) regs' (Z_to_bv 64 0x3a3a8) M' rom /\
       reg_get fr' 14 = Z_to_bv 64 bc_fzero /\ reg_get fr' 15 = Z_to_bv 64 bc_fzero /\
       (forall r : reg, ~ In (ridx r) [14; 15]%nat -> reg_get fr' r = reg_get fr r) /\
       getr regs' 5 = Z_to_bv 64 0 /\ getr regs' 6 = Z_to_bv 64 0 /\ getr regs' 7 = Z_to_bv 64 (-10) /\
       getr regs' 16 = Z_to_bv 64 j /\ getr regs' 17 = Z_to_bv 64 (j + 11) /\
       regs_agree (fun r => In r [5; 6; 7; 16; 17]%list) regs regs' /\ M' = M).
Proof.
  intros fr cs regs M s w j FZ Hs Hs16 Hw Hw2 Hj F18 H1 H2 H8 H15 H18 H19 H20 H22 H24.
  ex_entry regs [s; w; j; bv_unsigned (reg_get fr 18)] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; w; j; bv_unsigned (reg_get fr 18)]) M
     [KRange (EVar 32) 4416 (2 ^ 47); KRange (EVar 33) 1 19978; KRange (EVar 34) 0 19977]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adriveS 8%nat 400%nat [0x3a3a8%Z] (SCR (repeat false 4) [] []) [(18%nat, 35%nat)] HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 3 eexists; split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  fr_lit.
  fr_lit.
  fr_keep2.
  all: try first [ ex_agree HR HR' | ex_reg regs HR' ].
  all: try (rewrite ?zbv_addw_small by lia; rewrite ?zbv_add).
  all: vreg4.
Qed.

End Segs.
