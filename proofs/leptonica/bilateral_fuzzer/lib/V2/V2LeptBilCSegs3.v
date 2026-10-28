(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith DitherLib LeptRop LeptExec LeptExecW LeptExecFP LeptExecX LeptExecB LeptArithB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import FpReal FpBound FpSiteC.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptBilSegs2.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.
(* [comment removed for export] *)
#[local] Opaque RiscvSemantics.store_ok.

Ltac cv_norm :=
  repeat (rewrite ex_sx32 by lia);
  repeat rewrite ext_val_sx_id by (first [ lia | (rewrite ?u_Z2bv by lia; ex_pow2; lia) ]);
  rewrite ?w_mulw, ?w_addw, ?w_subw, ?m_mul, ?alu_add, ?alu_sub, ?alu_sltu, ?alu_slt, ?alu_xor, ?alu_or, ?alu_and;
  rewrite ?zbv_add, ?zbv_sub; rewrite ?zbv_mulw_small by lia; rewrite ?zbv_mul;
  rewrite ?addw_fit by lia; rewrite ?subw_fit by lia;
  rewrite ?exB_ovf_idiom by lia; rewrite ?zbv_sltu_ge by lia.
#[local] Ltac exB_sc_hook ::= cv_norm; ex_br.

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

Ltac fr_lit := lazymatch goal with |- reg_get (fr_denot ?E ?L ?fr) ?r = Z_to_bv 64 ?z =>
  apply (fr_get_lit E L fr r z); vm_compute; reflexivity end.

Lemma cv_xor_m1 : forall z, (0 <= z < 2 ^ 64)%Z -> v_xor (Z_to_bv 64 z) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - z).
Proof.
  intros z Hz. unfold v_xor. assert (E1 : bv_unsigned (Z_to_bv 64 (-1)) = (2 ^ 64 - 1)%Z) by reflexivity.
  rewrite E1, u_Z2bv by lia. rewrite lxor_ones64B by lia. reflexivity.
Qed.

Ltac cv_vnorm := cv_norm; rewrite ?divw1_id by lia; rewrite ?cv_xor_m1 by lia; rewrite ?zbv_snez by lia.

Ltac cv_cell HK Hlf regs :=
  lazymatch goal with
  | |- rdn _ _ (Z_to_bv 64 (?s - ?k)) ?n = Some (Z_to_le_bytes ?n ?z) =>
      let N := fresh "C" in
      exB_cell HK Hlf (EVar 32) (- k)%Z n (s - k)%Z z N idtac idtac idtac;
      [ exB_scs regs | exB_tacA idtac | exB_tacV cv_vnorm | exact N ]
  end.

Ltac cv_regfin := first [ reflexivity | (f_equal; lia) | (apply bv_eq; vm_compute; reflexivity) | (cv_vnorm; first [ reflexivity | (f_equal; lia) ]) ].
Ltac cv_sltu1 := rewrite v_sltu_Z by lia;
  lazymatch goal with |- context [(0 <? ?b)%Z] => replace (0 <? b)%Z with true by (symmetry; apply Z.ltb_lt; lia) end;
  first [ reflexivity | (vm_compute; reflexivity) ].

Lemma bc_M : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pa bsc pixs ws hs wpls datas w h rng : Z),
  frm_zero cs ->
  (4096 + 320 <= s <= 2 ^ 47)%Z -> (s mod 16 = 0)%Z ->
  (4096 <= bsc)%Z -> (bsc + 64 <= s - 320)%Z -> (bsc mod 8 = 0)%Z ->
  (4096 <= pixs)%Z -> (pixs + 64 <= s - 320)%Z -> (pixs mod 8 = 0)%Z ->
  (0 <= pa < 2 ^ 64)%Z -> (0 <= ws < 2 ^ 31)%Z -> (0 <= hs < 2 ^ 31)%Z -> (0 <= wpls < 2 ^ 31)%Z -> (4096 <= datas < 2 ^ 47)%Z ->
  (0 <= w < 2 ^ 31 - 1)%Z -> (0 <= h < 2 ^ 31 - 1)%Z -> (0 <= rng < 2 ^ 64)%Z ->
  img_none m 0x12588 8 -> img_none m 0x125d0 8 -> (0x125d8 <= s - 320)%Z ->
  rdn SEGS m (Z_to_bv 64 bsc) 4 = Some (Z_to_le_bytes 4 ws) ->
  rdn SEGS m (Z_to_bv 64 (bsc + 4)) 4 = Some (Z_to_le_bytes 4 hs) ->
  rdn SEGS m (Z_to_bv 64 (bsc + 16)) 4 = Some (Z_to_le_bytes 4 wpls) ->
  rdn SEGS m (Z_to_bv 64 (bsc + 56)) 8 = Some (Z_to_le_bytes 8 datas) ->
  rdn SEGS m (Z_to_bv 64 pixs) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (s - 296)) 8 = Some (Z_to_le_bytes 8 bsc) ->
  store_ok SEGS m (Z_to_bv 64 (s - 320)) 320 = true ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 10 = Z_to_bv 64 pa -> getr regs 22 = Z_to_bv 64 1 ->
  getr regs 23 = Z_to_bv 64 rng -> getr regs 24 = Z_to_bv 64 pixs ->
  reg_get fr 18 = Z_to_bv 64 4621819117588971520 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x39efc) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x3a038) M' rom /\ frm_zero cs' /\
      rinv [((s - 312)%Z, 8%Z); ((s - 240)%Z, 64%Z); ((s - 144)%Z, 16%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 312)) 8 = Some (Z_to_le_bytes 8 pa) /\
      rdn SEGS M' (Z_to_bv 64 (s - 240)) 8 = Some (Z_to_le_bytes 8 wpls) /\
      rdn SEGS M' (Z_to_bv 64 (s - 224)) 8 = Some (Z_to_le_bytes 8 datas) /\
      rdn SEGS M' (Z_to_bv 64 (s - 216)) 8 = Some (Z_to_le_bytes 8 h) /\
      rdn SEGS M' (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 0) /\
      rdn SEGS M' (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 w) /\
      getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 8 = Z_to_bv 64 (-10) /\ getr regs' 9 = Z_to_bv 64 0 /\
      getr regs' 18 = Z_to_bv 64 10 /\ getr regs' 19 = Z_to_bv 64 (- 2 ^ 31) /\ getr regs' 22 = Z_to_bv 64 3 /\
      getr regs' 26 = Z_to_bv 64 (2 ^ 64 - 1 - rng) /\ getr regs' 27 = Z_to_bv 64 1 /\
      regs_agree (fun r => In r [1; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 22; 26; 27]%list) regs regs' /\
      bc_fsc fr' /\ (forall r : reg, ~ In (ridx r) [8; 9; 18]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s pa bsc pixs ws hs wpls datas w h rng FZ Hs Hs16 Hb1 Hb2 Hb8 Hp1 Hp2 Hp8 Hpa Hws Hhs Hwpl Hd Hw Hh Hr
    IM1 IM2 Himg Rws Rhs Rwpl Rd Rw Rh Rb SOK H2 H10 H22 H23 H24 F18.
  unfold img_none in IM1, IM2.
  ex_entry regs [s; pa; bsc; pixs; ws; hs; wpls; datas; w; h; rng] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pa; bsc; pixs; ws; hs; wpls; datas; w; h; rng]) m
     [KWr (SA (EVar 32) (-320)) 320;
      KRange (EVar 32) 4416 (2 ^ 47); KAlign (EVar 32) 16;
      KRange (EVar 34) 4096 (2 ^ 47); KAlign (EVar 34) 8; KRange (EVar 35) 4096 (2 ^ 47); KAlign (EVar 35) 8;
      KRange (EVar 36) 0 (2 ^ 31 - 1); KRange (EVar 37) 0 (2 ^ 31 - 1); KRange (EVar 38) 0 (2 ^ 31 - 1);
      KRange (EVar 39) 4096 (2 ^ 47); KRange (EVar 40) 0 (2 ^ 31 - 2); KRange (EVar 41) 0 (2 ^ 31 - 2);
      KWord (SA (EVar 32) (-296)) 8 (EVar 34);
      KWord (SA (EVar 34) 0) 4 (EVar 36); KWord (SA (EVar 34) 4) 4 (EVar 37); KWord (SA (EVar 34) 16) 4 (EVar 38);
      KWord (SA (EVar 34) 56) 8 (EVar 39); KWord (SA (EVar 35) 0) 4 (EVar 40); KWord (SA (EVar 35) 4) 4 (EVar 41);
      KDisj (SA (EVar 34) 0) 64 (SA (EVar 32) (-320)) 320; KDisj (SA (EVar 35) 0) 64 (SA (EVar 32) (-320)) 320;
      KImg 0x12588 0x12590; KImg 0x125d0 0x125d8]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adriveS 8%nat 400%nat [0x3a038%Z] (SCR [false; false; false; false; false; false] [] []) (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [((s - 312)%Z, 8%Z); ((s - 240)%Z, 64%Z); ((s - 144)%Z, 16%Z)]; exB_reg_tac idtac|].
  do 6 (split; [cv_cell HK Hlf regs|]).
  split; [exB_reg regs HR'|].
  split; [exB_reg regs HR'; apply bv_eq; vm_compute; reflexivity|].
  split; [exB_reg regs HR'|].
  split; [exB_reg regs HR'|].
  split; [exB_reg regs HR'; apply bv_eq; vm_compute; reflexivity|].
  split; [exB_reg regs HR'|].
  split; [exB_reg regs HR'; apply cv_xor_m1; lia|].
  split; [exB_reg regs HR'; cv_sltu1|].
  split; [ex_agree HR HR'|].
  split; [unfold bc_fsc; repeat split; fr_lit | fr_keep2].
Qed.

Lemma bc_N : forall (fx : FPState) regs (m : word -> option byte) (s bsc : Z),
  (4096 + 320 <= s <= 2 ^ 47)%Z -> (0 <= bsc < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 296)) 8 = Some (Z_to_le_bytes 8 bsc) ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x3a038) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x1a314) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 0x3a044 /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 10 = Z_to_bv 64 0 /\
      getr regs' 11 = Z_to_bv 64 bsc /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs').
Proof.
  intros fx regs m s bsc Hs Hb Rb H2.
  ex_entry regs [s; bsc] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bsc]) m [KWord (SA (EVar 32) (-296)) 8 (EVar 33)]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [0x1a314%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.

Ltac bc_O_run regs m s pixt nc datat wplt kval h off :=
  let HR := fresh "HR" in let HK := fresh "HK" in let ST := fresh "ST" in
  let R := fresh "R" in let HR' := fresh "HR'" in let Hlf := fresh "Hlf" in let Hms := fresh "Hms" in
  ex_entry regs [s; pixt; nc; (2 ^ 64 - 1 - nc)%Z; datat; wplt; kval; h] HR;
  assert (HK : know_ok SEGS (ex_env regs [s; pixt; nc; (2 ^ 64 - 1 - nc)%Z; datat; wplt; kval; h]) m
    [KWr (SA (EVar 32) (-320)) 320; KRange (EVar 32) 4416 (2 ^ 47); KAlign (EVar 32) 16;
     KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 8; KRange (EVar 34) 4096 (2 ^ 47);
     KRange (EVar 35) (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1); KRange (EVar 36) 4096 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 31 - 1);
     KRange (EVar 38) 0 255; KRange (EVar 39) 1 (2 ^ 31 - 1);
     KWord (SA (EVar 33) 56) 8 (EVar 36); KWord (SA (EVar 33) 16) 4 (EVar 37); KWord (SA (EVar 34) off) 4 (EVar 38);
     KWord (SA (EVar 32) (-272)) 8 (ELit 11); KWord (SA (EVar 32) (-248)) 8 (EVar 34);
     KWord (SA (EVar 32) (-256)) 8 (EVar 35); KWord (SA (EVar 32) (-216)) 8 (EVar 39);
     KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-320)) 320]) by (ex_know regs);
  lazymatch goal with FZ : frm_zero _ |- _ =>
  exb_open HR HK ST;
  exb_adriveS 8%nat 400%nat [237720%Z] (SCR (repeat false 8) [] []) (@nil (nat * nat)) HK ST FZ;
  exb_exit ST R HR' Hlf Hms;
  eexists; split; [exact Hms|];
  do 2 eexists; split; [reflexivity|];
  split; [exB_rinv_tac Hlf [((s - 280)%Z, 8%Z); ((s - 208)%Z, 16%Z); ((s - 176)%Z, 8%Z)]; exB_reg_tac idtac|];
  split; [cv_cell HK Hlf regs|]; split; [cv_cell HK Hlf regs|];
  split; [unfold bc_cptr; cv_cell HK Hlf regs|]; split; [cv_cell HK Hlf regs|];
  do 8 (split; [exB_reg regs HR'; try cv_sltu1|]);
  ex_agree HR HR'
  end.

Lemma bc_O : forall (fx : FPState) regs (m : word -> option byte) (s pixt nc idx datat wplt kval h : Z),
  (4096 + 320 <= s <= 2 ^ 47)%Z -> (s mod 16 = 0)%Z ->
  (4096 <= pixt)%Z -> (pixt + 64 <= s - 320)%Z -> (pixt mod 8 = 0)%Z ->
  (4096 <= nc)%Z -> (nc + 40 <= s - 320)%Z -> (0 <= idx < 10)%Z ->
  (4096 <= datat < 2 ^ 47)%Z -> (0 <= wplt < 2 ^ 31)%Z -> (0 <= kval <= 255)%Z -> (1 <= h < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (pixt + 56)) 8 = Some (Z_to_le_bytes 8 datat) ->
  rdn SEGS m (Z_to_bv 64 (pixt + 16)) 4 = Some (Z_to_le_bytes 4 wplt) ->
  rdn SEGS m (Z_to_bv 64 (nc + 4 * idx)) 4 = Some (Z_to_le_bytes 4 kval) ->
  rdn SEGS m (Z_to_bv 64 (s - 272)) 8 = Some (Z_to_le_bytes 8 11) ->
  rdn SEGS m (Z_to_bv 64 (s - 248)) 8 = Some (Z_to_le_bytes 8 nc) ->
  rdn SEGS m (Z_to_bv 64 (s - 256)) 8 = Some (Z_to_le_bytes 8 (2 ^ 64 - 1 - nc)) ->
  rdn SEGS m (Z_to_bv 64 (s - 216)) 8 = Some (Z_to_le_bytes 8 h) ->
  store_ok SEGS m (Z_to_bv 64 (s - 320)) 320 = true ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 9 = Z_to_bv 64 idx -> getr regs 10 = Z_to_bv 64 pixt ->
  frm_zero (@fp_csr fx) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 237636) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 237720) M' rom /\
      rinv [((s - 280)%Z, 8%Z); ((s - 208)%Z, 16%Z); ((s - 176)%Z, 8%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 280)) 8 = Some (Z_to_le_bytes 8 idx) /\
      rdn SEGS M' (Z_to_bv 64 (s - 208)) 8 = Some (Z_to_le_bytes 8 datat) /\
      rdn SEGS M' (Z_to_bv 64 (s - 200)) 8 = Some (Z_to_le_bytes 8 bc_cptr) /\
      rdn SEGS M' (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 pixt) /\
      getr regs' 1 = Z_to_bv 64 0x3a05c /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 9 = Z_to_bv 64 kval /\
      getr regs' 10 = Z_to_bv 64 h /\ getr regs' 11 = Z_to_bv 64 (nc + 4 * idx) /\ getr regs' 24 = Z_to_bv 64 1 /\
      getr regs' 25 = Z_to_bv 64 wplt /\ getr regs' 29 = Z_to_bv 64 11 /\
      regs_agree (fun r => In r [1; 9; 10; 11; 24; 25; 29]%list) regs regs').
Proof.
  intros fx regs m s pixt nc idx datat wplt kval h Hs Hs16 Hp1 Hp2 Hp8 Hn1 Hn2 Hi Hd Hw Hk Hh Rd Rw Rk R11 Rnc Rnx Rh SOK H2 H9 H10 FZ.
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  assert (E : (idx = 0 \/ idx = 1 \/ idx = 2 \/ idx = 3 \/ idx = 4 \/ idx = 5 \/ idx = 6 \/ idx = 7 \/ idx = 8 \/ idx = 9)%Z) by lia.
  destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | -> ]]]]]]]]].
  all: lazymatch type of Rk with rdn _ _ (Z_to_bv 64 (_ + 4 * ?k)) 4 = _ =>
    let off := eval vm_compute in (4 * k)%Z in bc_O_run regs m s pixt nc datat wplt kval h off end.
Qed.

Lemma bc_P : forall (fx : FPState) regs (m : word -> option byte) (s w h : Z),
  (4096 + 320 <= s <= 2 ^ 47)%Z -> (0 <= w < 2 ^ 64)%Z -> (0 <= h < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 216)) 8 = Some (Z_to_le_bytes 8 h) ->
  rdn SEGS m (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 w) ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 238240) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x192d0) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 238256 /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 10 = Z_to_bv 64 w /\
      getr regs' 11 = Z_to_bv 64 h /\ getr regs' 12 = Z_to_bv 64 8 /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs').
Proof.
  intros fx regs m s w h Hs Hw Hh Rh Rw H2.
  ex_entry regs [s; w; h] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; w; h]) m
     [KWord (SA (EVar 32) (-216)) 8 (EVar 34); KWord (SA (EVar 32) (-184)) 8 (EVar 33)]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [0x192d0%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.

Lemma bc_Q : forall (fx : FPState) regs (m : word -> option byte) (s pixd datad wpld h : Z),
  (4096 + 320 <= s <= 2 ^ 47)%Z -> (s mod 16 = 0)%Z ->
  (4096 <= pixd)%Z -> (pixd + 64 <= s - 320)%Z -> (pixd mod 8 = 0)%Z ->
  (4096 <= datad < 2 ^ 47)%Z -> (0 <= wpld < 2 ^ 31)%Z -> (1 <= h < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (pixd + 56)) 8 = Some (Z_to_le_bytes 8 datad) ->
  rdn SEGS m (Z_to_bv 64 (pixd + 16)) 4 = Some (Z_to_le_bytes 4 wpld) ->
  rdn SEGS m (Z_to_bv 64 (s - 272)) 8 = Some (Z_to_le_bytes 8 11) ->
  rdn SEGS m (Z_to_bv 64 (s - 216)) 8 = Some (Z_to_le_bytes 8 h) ->
  store_ok SEGS m (Z_to_bv 64 (s - 320)) 320 = true ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 10 = Z_to_bv 64 pixd ->
  frm_zero (@fp_csr fx) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 238256) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 238308) M' rom /\
      rinv [((s - 264)%Z, 8%Z); ((s - 232)%Z, 8%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 264)) 8 = Some (Z_to_le_bytes 8 pixd) /\
      rdn SEGS M' (Z_to_bv 64 (s - 232)) 8 = Some (Z_to_le_bytes 8 datad) /\
      getr regs' 1 = Z_to_bv 64 11 /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 10 = Z_to_bv 64 wpld /\
      getr regs' 11 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs').
Proof.
  intros fx regs m s pixd datad wpld h Hs Hs16 Hp1 Hp2 Hp8 Hd Hwp Hh Rd Rwp R11 Rh SOK H2 H10 FZ.
  ex_entry regs [s; pixd; datad; wpld; h] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixd; datad; wpld; h]) m
     [KWr (SA (EVar 32) (-320)) 320; KRange (EVar 32) 4416 (2 ^ 47); KAlign (EVar 32) 16;
      KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 8; KRange (EVar 34) 4096 (2 ^ 47); KRange (EVar 35) 0 (2 ^ 31 - 1);
      KWord (SA (EVar 33) 56) 8 (EVar 34); KWord (SA (EVar 33) 16) 4 (EVar 35); KWord (SA (EVar 32) (-272)) 8 (ELit 11);
      KRange (EVar 36) 1 (2 ^ 31 - 1); KWord (SA (EVar 32) (-216)) 8 (EVar 36);
      KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-320)) 320]) by (ex_know regs).
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  exb_open HR HK ST.
  exb_adriveS 8%nat 400%nat [238308%Z] (SCR (repeat false 8) [] []) (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((s - 264)%Z, 8%Z); ((s - 232)%Z, 8%Z)]; exB_reg_tac idtac|].
  do 2 (split; [cv_cell HK Hlf regs|]).
  do 4 (split; [exB_reg regs HR'|]).
  ex_agree HR HR'.
Qed.

Lemma bc_R : forall (fx : FPState) regs (m : word -> option byte) (s : Z),
  (4096 + 320 <= s <= 2 ^ 47)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 237584) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x1982c) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 237592 /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 10 = Z_to_bv 64 (s - 176) /\
      regs_agree (fun r => In r [1; 10]%list) regs regs').
Proof.
  intros fx regs m s Hs H2.
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m []) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [0x1982c%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.

Lemma bc_S : forall (fx : FPState) regs (m : word -> option byte) (s pa pixd : Z),
  (4096 + 320 <= s <= 2 ^ 47)%Z -> (0 <= pa < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 312)) 8 = Some (Z_to_le_bytes 8 pa) ->
  rdn SEGS m (Z_to_bv 64 (s - 264)) 8 = Some (Z_to_le_bytes 8 pixd) ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 237592) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x18450) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 237608 /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 10 = Z_to_bv 64 pa /\
      getr regs' 11 = Z_to_bv 64 pixd /\ getr regs' 12 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs').
Proof.
  intros fx regs m s pa pixd Hs Hpa Hpd Rpa Rpd H2.
  ex_entry regs [s; pa; pixd] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pa; pixd]) m
     [KWord (SA (EVar 32) (-312)) 8 (EVar 33); KWord (SA (EVar 32) (-264)) 8 (EVar 34)]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [0x18450%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.

Lemma bc_T_more : forall (fx : FPState) regs (m : word -> option byte) (s idx : Z),
  (4096 + 320 <= s <= 2 ^ 47)%Z -> (0 <= idx <= 8)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 280)) 8 = Some (Z_to_le_bytes 8 idx) ->
  rdn SEGS m (Z_to_bv 64 (s - 288)) 8 = Some (Z_to_le_bytes 8 10) ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 237608) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 237624) M' rom /\
      M' = m /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 9 = Z_to_bv 64 (idx + 1) /\ getr regs' 10 = Z_to_bv 64 10 /\
      regs_agree (fun r => In r [9; 10]%list) regs regs').
Proof.
  intros fx regs m s idx Hs Hi Ri R10 H2.
  ex_entry regs [s; idx] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; idx]) m
     [KRange (EVar 33) 0 8; KWord (SA (EVar 32) (-280)) 8 (EVar 33); KWord (SA (EVar 32) (-288)) 8 (ELit 10)]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [237624%Z; 238888%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
  all: (cv_norm; first [ reflexivity | (f_equal; lia) ]).
Qed.

Lemma bc_T_last : forall (fx : FPState) regs (m : word -> option byte) (s : Z),
  (4096 + 320 <= s <= 2 ^ 47)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 280)) 8 = Some (Z_to_le_bytes 8 9) ->
  rdn SEGS m (Z_to_bv 64 (s - 288)) 8 = Some (Z_to_le_bytes 8 10) ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 237608) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 238888) M' rom /\
      M' = m /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 9 = Z_to_bv 64 10 /\ getr regs' 10 = Z_to_bv 64 10 /\
      regs_agree (fun r => In r [9; 10]%list) regs regs').
Proof.
  intros fx regs m s Hs Ri R10 H2.
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m
     [KWord (SA (EVar 32) (-280)) 8 (ELit 9); KWord (SA (EVar 32) (-288)) 8 (ELit 10)]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [237624%Z; 238888%Z] (SCR [] [] []) HR Hlf HK Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR | ex_agree HRo HR ].
  all: (cv_norm; first [ reflexivity | (f_equal; lia) ]).
Qed.

End Segs.
