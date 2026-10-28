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
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptRoom LeptSlots LeptExec LeptExecW LeptExecFP LeptExecX DitherLib DitherLoop LeptCmapArr LeptExecB LeptArithB LibAtomic.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2_code_pixaDestroy V2_code_boxDestroy.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.
(* [comment removed for export] *)
#[local] Opaque RiscvSemantics.store_ok.

Definition PC_pixaDestroy : Z := 0x18340.
Definition PC_boxaDestroy : Z := 0x18fa0.
Definition PC_pixDestroy : Z := 0x1982c.
Definition PC_FREE : Z := 0x3c230.

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Ltac guard8 F D EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite EQ; reflexivity).
Ltac guard4 F D EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_3; unorm; rewrite EQ; reflexivity).
Ltac snez1 F D := stepat F D (Z_to_bv 64 1) ltac:(gres; pin; imm_norm; apply zbv_snez; lia).
Ltac seqz0 F D := stepat F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).
Ltac amo_dec F D a C SOK :=
  chain_step;
    [ reflexivity
    | eapply (step_amoadd_w SEGS _ _ _ _ _ _ _ _ _ _ (Z_to_le_bytes 4 1) (Z_to_bv 64 1) F eq_refl D);
      [ gres; rewrite u_Z2bv by lia; apply mod16_plus_mod4; [exact a | reflexivity]
      | gres; repeat rdn_peel1; exact C
      | apply lez4; lia
      | gres; sok_in SOK ]
    | step_simpl ];
  gres; rewrite zbv_add;
  replace (Z_to_bv 64 (1 + 18446744073709551615)%Z) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity);
  rewrite (SumWalkTac.v_lw_small 1) by lia.
Ltac rinv_tac :=
  repeat (eapply rinv_wbytes;
          [ | rewrite ?length_N_to_le_bytes, ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; reflexivity | lia | lia
          | first [ (eexists; split; [ left; reflexivity | cbn [fst snd]; lia ])
                  | (eexists; split; [ right; left; reflexivity | cbn [fst snd]; lia ])
                  | (eexists; split; [ right; right; left; reflexivity | cbn [fst snd]; lia ]) ] ]);
  apply rinv_refl.
Ltac post1 :=
  lazymatch goal with
  | |- rinv _ _ _ => rinv_tac
  | |- regs_agree _ _ _ => solve_regs_agree
  | |- rdn _ _ _ _ = Some (word_to_le_bytes 8 _) => gres; rdn_solve
  | |- rdn _ (wbytes _ _ (word_to_le_bytes 4 _)) _ 4 = Some (Z_to_le_bytes 4 0) =>
      rewrite <- (w2b_Z 4 0) by lia; apply rdn_wbytes_hit4; rewrite u_Z2bv by lia; lia
  | |- rdn _ (wbytes _ _ (word_to_le_bytes 8 _)) _ 8 = Some (Z_to_le_bytes 8 0) =>
      rewrite <- (w2b_Z 8 0) by lia; apply rdn_wbytes_hit8; rewrite u_Z2bv by lia; lia
  | |- getr _ _ = _ => gres; pin; first [ reflexivity | apply bv_eq; rewrite ?u_Z2bv by lia; lia ]
  | |- _ = _ => first [ reflexivity | assumption ]
  end.
Ltac fin E :=
  lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ => replace pc with (Z_to_bv 64 E) by (apply bv_eq; reflexivity) end;
  apply mst_refl.
Ltac post := repeat (lazymatch goal with |- _ /\ _ => split end); post1.

Section Segs.
Variable rom : word -> option byte.
#[local] Existing Instance exf_fxd | 100.

Lemma pd_A : forall (fx : FPState) regs (m : word -> option byte) (s pp pa : Z),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (4096 <= pp)%Z ->
  (pp + 8 <= 2 ^ 47)%Z ->
  (4096 <= pa)%Z ->
  (pa + 32 <= s - 48)%Z ->
  (pa mod 16 = 0)%Z ->
  (pp mod 8 = 0)%Z ->
  (pp + 8 <= s - 48 \/ s <= pp)%Z ->
  (pp + 8 <= pa \/ pa + 32 <= pp)%Z ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pa) ->
  rdn SEGS m (Z_to_bv 64 pa) 4 = Some (Z_to_le_bytes 4 10) ->
  rdn SEGS m (Z_to_bv 64 (pa + 8)) 4 = Some (Z_to_le_bytes 4 1) ->
  store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
  store_ok SEGS m (Z_to_bv 64 (pa + 8)) 4 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 pp ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 PC_pixaDestroy) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x1839c) M' rom /\
      rinv [((s - 40)%Z, 40%Z); ((pa + 8)%Z, 4%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (pa + 8)) 4 = Some (Z_to_le_bytes 4 0) /\
      rdn SEGS M' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) /\
      getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 8 = Z_to_bv 64 pa /\ getr regs' 9 = Z_to_bv 64 pp /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 0 /\
      regs_agree (fun r => In r [2; 8; 9; 10; 11; 12; 18; 19]%list) regs regs').
Proof.
  intros fx regs m s pp pa Hs Hpp Hpp47 Hpa Hpas ALpa ALpp DJs DJp Rpp Rn Rrc SOK SOKrc H2 H10.
  assert (AL8 : (pa mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pa); apply mod16_plus_mod8; [exact ALpa | reflexivity]).
  unfold PC_pixaDestroy, reach. eexists. split.
  - norm_pc.
    zv F_18340 D_18340 (Z_to_bv 64 (s - 48)).
    stepST F_18344 D_18344 (Z_to_bv 64 (s - 8)) (getr regs 1) ltac:(sok_in SOK).
    stepST F_18348 D_18348 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_1834c D_1834c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_18350 D_18350 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_18354 D_18354 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_18358 D_18358 ltac:(condZ).
    guard8 F_1835c D_1835c ALpp.
    stepb_ft F_18360 D_18360 ltac:(condZ).
    stepLD F_18364 D_18364 (Z_to_le_bytes 8 pa) (Z_to_bv 64 pa) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
    stepb_ft F_18368 D_18368 ltac:(condZ).
    guard8 F_1836c D_1836c AL8.
    stepb_ft F_18370 D_18370 ltac:(condZ).
    zv F_18374 D_18374 (Z_to_bv 64 (pa + 8)).
    sn F_18378 D_18378.
    amo_dec F_1837c D_1837c ALpa Rrc SOKrc.
    sn F_18380 D_18380.
    stepb_ft F_18384 D_18384 ltac:(condZ).
    sn F_18388 D_18388.
    stepLD F_1838c D_1838c (Z_to_le_bytes 4 10) (Z_to_bv 64 10) ltac:(addr_norm; repeat rdn_peel1; exact Rn) ltac:(apply lez4; lia).
    stepb_ft F_18390 D_18390 ltac:(condZ).
    sn F_18394 D_18394. sn F_18398 D_18398.
    fin 0x1839c%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma pd_L : forall (fx : FPState) regs (m : word -> option byte) (s pa parr i : Z),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (4096 <= pa)%Z ->
  (pa + 32 <= 2 ^ 47)%Z ->
  (1 <= parr)%Z ->
  (parr + 80 <= 2 ^ 47)%Z ->
  (0 <= i <= 9)%Z ->
  rdn SEGS m (Z_to_bv 64 (pa + 16)) 8 = Some (Z_to_le_bytes 8 parr) ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  getr regs 8 = Z_to_bv 64 pa ->
  getr regs 18 = Z_to_bv 64 (8 * i) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x1839c) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 PC_pixDestroy) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 0x183bc /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 10 = Z_to_bv 64 (parr + 8 * i) /\
      regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs').
Proof.
  intros fx regs m s pa parr i Hs Hpa Hpa47 Hparr Hparr47 Hi Rparr H2 H8 H18.
  unfold PC_pixDestroy, reach. eexists. split.
  - norm_pc.
    stepLD F_1839c D_1839c (Z_to_le_bytes 8 parr) (Z_to_bv 64 parr) ltac:(addr_norm; exact Rparr) ltac:(apply lez8; lia).
    zv F_183a0 D_183a0 (Z_to_bv 64 (parr + 8 * i)).
    stepb_ft F_183a4 D_183a4 ltac:(condZ).
    snez1 F_183a8 D_183a8.
    seqz0 F_183ac D_183ac.
    sn F_183b0 D_183b0.
    stepb_ft F_183b4 D_183b4 ltac:(condZ).
    sn F_183b8 D_183b8.
    fin 0x1982c%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma pd_Mm : forall (fx : FPState) regs (m : word -> option byte) (s pa i : Z),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (4096 <= pa)%Z ->
  (pa + 32 <= 2 ^ 47)%Z ->
  (0 <= i <= 8)%Z ->
  rdn SEGS m (Z_to_bv 64 pa) 4 = Some (Z_to_le_bytes 4 10) ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  getr regs 8 = Z_to_bv 64 pa ->
  getr regs 18 = Z_to_bv 64 (8 * i) ->
  getr regs 19 = Z_to_bv 64 i ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x183bc) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x1839c) M' rom /\
      M' = m /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 8 = Z_to_bv 64 pa /\ getr regs' 18 = Z_to_bv 64 (8 * (i + 1)) /\ getr regs' 19 = Z_to_bv 64 (i + 1) /\
      regs_agree (fun r => In r [10; 18; 19]%list) regs regs').
Proof.
  intros fx regs m s pa i Hs Hpa Hpa47 Hi Rn H2 H8 H18 H19.
  unfold reach. eexists. split.
  - norm_pc.
    stepLD F_183bc D_183bc (Z_to_le_bytes 4 10) (Z_to_bv 64 10) ltac:(addr_norm; exact Rn) ltac:(apply lez4; lia).
    zv F_183c0 D_183c0 (Z_to_bv 64 (i + 1)).
    zv F_183c4 D_183c4 (Z_to_bv 64 (8 * (i + 1))).
    stepb_tk F_183c8 D_183c8 ltac:(condZ).
    fin 0x1839c%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma pd_Ml : forall (fx : FPState) regs (m : word -> option byte) (s pa : Z),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (4096 <= pa)%Z ->
  (pa + 32 <= 2 ^ 47)%Z ->
  rdn SEGS m (Z_to_bv 64 pa) 4 = Some (Z_to_le_bytes 4 10) ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  getr regs 8 = Z_to_bv 64 pa ->
  getr regs 18 = Z_to_bv 64 72 ->
  getr regs 19 = Z_to_bv 64 9 ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x183bc) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x183cc) M' rom /\
      M' = m /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 8 = Z_to_bv 64 pa /\
      regs_agree (fun r => In r [10; 18; 19]%list) regs regs').
Proof.
  intros fx regs m s pa Hs Hpa Hpa47 Rn H2 H8 H18 H19.
  unfold reach. eexists. split.
  - norm_pc.
    stepLD F_183bc D_183bc (Z_to_le_bytes 4 10) (Z_to_bv 64 10) ltac:(addr_norm; exact Rn) ltac:(apply lez4; lia).
    sn F_183c0 D_183c0.
    sn F_183c4 D_183c4.
    stepb_ft F_183c8 D_183c8 ltac:(condZ).
    fin 0x183cc%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma pd_B : forall (fx : FPState) regs (m : word -> option byte) (s pa parr : Z),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (4096 <= pa)%Z ->
  (pa + 32 <= 2 ^ 47)%Z ->
  (0 <= parr < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (pa + 16)) 8 = Some (Z_to_le_bytes 8 parr) ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  getr regs 8 = Z_to_bv 64 pa ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x183cc) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 PC_FREE) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 0x183d4 /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 8 = Z_to_bv 64 pa /\ getr regs' 10 = Z_to_bv 64 parr /\
      regs_agree (fun r => In r [1; 10]%list) regs regs').
Proof.
  intros fx regs m s pa parr Hs Hpa Hpa47 Hparr Rparr H2 H8.
  unfold PC_FREE, reach. eexists. split.
  - norm_pc.
    stepLD F_183cc D_183cc (Z_to_le_bytes 8 parr) (Z_to_bv 64 parr) ltac:(addr_norm; exact Rparr) ltac:(apply lez8; lia).
    sn F_183d0 D_183d0.
    fin 0x3c230%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma pd_C : forall (fx : FPState) regs (m : word -> option byte) (s pa : Z),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (4096 <= pa)%Z ->
  (pa + 32 <= 2 ^ 47)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  getr regs 8 = Z_to_bv 64 pa ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x183d4) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 PC_boxaDestroy) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 0x183dc /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 8 = Z_to_bv 64 pa /\ getr regs' 10 = Z_to_bv 64 (pa + 24) /\
      regs_agree (fun r => In r [1; 10]%list) regs regs').
Proof.
  intros fx regs m s pa Hs Hpa Hpa47 H2 H8.
  unfold PC_boxaDestroy, reach. eexists. split.
  - norm_pc.
    zv F_183d4 D_183d4 (Z_to_bv 64 (pa + 24)).
    sn F_183d8 D_183d8.
    fin 0x18fa0%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma pd_D : forall (fx : FPState) regs (m : word -> option byte) (s pa : Z),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (4096 <= pa)%Z ->
  (pa + 32 <= 2 ^ 47)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  getr regs 8 = Z_to_bv 64 pa ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x183dc) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 PC_FREE) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 0x183e4 /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 10 = Z_to_bv 64 pa /\
      regs_agree (fun r => In r [1; 10]%list) regs regs').
Proof.
  intros fx regs m s pa Hs Hpa Hpa47 H2 H8.
  unfold PC_FREE, reach. eexists. split.
  - norm_pc.
    sn F_183dc D_183dc.
    sn F_183e0 D_183e0.
    fin 0x3c230%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma pd_E : forall (fx : FPState) regs (m : word -> option byte) (s pp : Z) (ret : word) (v1 v8 v9 v18 v19 : word),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (4096 <= pp)%Z ->
  (pp + 8 <= 2 ^ 47)%Z ->
  (pp + 8 <= s - 48 \/ s <= pp)%Z ->
  ret_ok ret ->
  v1 = ret ->
  store_ok SEGS m (Z_to_bv 64 pp) 8 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  getr regs 9 = Z_to_bv 64 pp ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x183e4) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' ret M' rom /\
      rinv [(pp, 8%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) /\
      getr regs' 2 = Z_to_bv 64 s /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs regs').
Proof.
  intros fx regs m s pp ret v1 v8 v9 v18 v19 Hs Hpp Hpp47 DJ Hret E1 SOK R1 R8 R9 R18 R19 H2 H9. subst v1.
  unfold reach. eexists. split.
  - norm_pc.
    sn F_183e4 D_183e4.
    stepST F_183e8 D_183e8 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(sok_in SOK).
    sn F_183ec D_183ec.
    stepLD8 F_18430 D_18430 ret.
    stepLD8 F_18434 D_18434 v8.
    stepLD8 F_18438 D_18438 v9.
    stepLD8 F_1843c D_1843c v18.
    stepLD8 F_18440 D_18440 v19.
    zv F_18444 D_18444 (Z_to_bv 64 s).
    stepret F_18448 D_18448 ret ltac:(bveq).
    apply mst_refl.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma bd_A : forall (fx : FPState) regs (m : word -> option byte) (s pp ba barr : Z),
  (4096 + 96 <= s <= 2 ^ 47)%Z ->
  (4096 <= pp)%Z ->
  (pp + 8 <= s - 96)%Z ->
  (4096 <= ba)%Z ->
  (ba + 24 <= s - 96)%Z ->
  (ba mod 16 = 0)%Z ->
  (pp mod 8 = 0)%Z ->
  (0 <= barr < 2 ^ 64)%Z ->
  (pp + 8 <= ba \/ ba + 24 <= pp)%Z ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 ba) ->
  rdn SEGS m (Z_to_bv 64 ba) 4 = Some (Z_to_le_bytes 4 0) ->
  rdn SEGS m (Z_to_bv 64 (ba + 8)) 4 = Some (Z_to_le_bytes 4 1) ->
  rdn SEGS m (Z_to_bv 64 (ba + 16)) 8 = Some (Z_to_le_bytes 8 barr) ->
  store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
  store_ok SEGS m (Z_to_bv 64 (ba + 8)) 4 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 pp ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 PC_boxaDestroy) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 PC_FREE) M' rom /\
      rinv [((s - 96)%Z, 96%Z); ((ba + 8)%Z, 4%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (ba + 8)) 4 = Some (Z_to_le_bytes 4 0) /\
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
      getr regs' 1 = Z_to_bv 64 0x19120 /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 8 = Z_to_bv 64 ba /\ getr regs' 19 = Z_to_bv 64 pp /\ getr regs' 10 = Z_to_bv 64 barr /\
      regs_agree (fun r => In r [1; 2; 8; 10; 11; 12; 19]%list) regs regs').
Proof.
  intros fx regs m s pp ba barr Hs Hpp Hpps Hba Hbas ALba ALpp Hbarr DJ Rpp Rn Rrc Rarr SOK SOKrc H2 H10.
  assert (AL8 : (ba mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r ba); apply mod16_plus_mod8; [exact ALba | reflexivity]).
  unfold PC_boxaDestroy, PC_FREE, reach. eexists. split.
  - norm_pc.
    zv F_18fa0 D_18fa0 (Z_to_bv 64 (s - 96)).
    stepST F_18fa4 D_18fa4 (Z_to_bv 64 (s - 8)) (getr regs 1) ltac:(sok_in SOK).
    stepST F_18fa8 D_18fa8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_18fac D_18fac (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_18fb0 D_18fb0 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_18fb4 D_18fb4 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepST F_18fb8 D_18fb8 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
    stepST F_18fbc D_18fbc (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
    stepST F_18fc0 D_18fc0 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
    stepST F_18fc4 D_18fc4 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
    stepST F_18fc8 D_18fc8 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
    stepST F_18fcc D_18fcc (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
    stepST F_18fd0 D_18fd0 (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
    stepb_ft F_18fd4 D_18fd4 ltac:(condZ).
    guard8 F_18fd8 D_18fd8 ALpp.
    stepb_ft F_18fdc D_18fdc ltac:(condZ).
    stepLD F_18fe0 D_18fe0 (Z_to_le_bytes 8 ba) (Z_to_bv 64 ba) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
    stepb_ft F_18fe4 D_18fe4 ltac:(condZ).
    guard8 F_18fe8 D_18fe8 AL8.
    stepb_ft F_18fec D_18fec ltac:(condZ).
    zv F_18ff0 D_18ff0 (Z_to_bv 64 (ba + 8)).
    sn F_18ff4 D_18ff4.
    amo_dec F_18ff8 D_18ff8 ALba Rrc SOKrc.
    sn F_18ffc D_18ffc.
    stepb_ft F_19000 D_19000 ltac:(condZ).
    sn F_19004 D_19004.
    stepLD F_19008 D_19008 (Z_to_le_bytes 4 0) (Z_to_bv 64 0) ltac:(addr_norm; repeat rdn_peel1; exact Rn) ltac:(apply lez4; lia).
    stepb_tk F_1900c D_1900c ltac:(condZ).
    stepLD F_19118 D_19118 (Z_to_le_bytes 8 barr) (Z_to_bv 64 barr) ltac:(addr_norm; repeat rdn_peel1; exact Rarr) ltac:(apply lez8; lia).
    sn F_1911c D_1911c.
    fin 0x3c230%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma bd_B : forall (fx : FPState) regs (m : word -> option byte) (s ba : Z),
  (4096 + 96 <= s <= 2 ^ 47)%Z ->
  (0 <= ba < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 96) ->
  getr regs 8 = Z_to_bv 64 ba ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x19120) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 PC_FREE) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 0x19128 /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 10 = Z_to_bv 64 ba /\
      regs_agree (fun r => In r [1; 10]%list) regs regs').
Proof.
  intros fx regs m s ba Hs Hba H2 H8.
  unfold PC_FREE, reach. eexists. split.
  - norm_pc.
    sn F_19120 D_19120.
    sn F_19124 D_19124.
    fin 0x3c230%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma bd_C : forall (fx : FPState) regs (m : word -> option byte) (s pp : Z) (ret : word) (v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 : word),
  (4096 + 96 <= s <= 2 ^ 47)%Z ->
  (4096 <= pp)%Z ->
  (pp + 8 <= 2 ^ 47)%Z ->
  (pp + 8 <= s - 96 \/ s <= pp)%Z ->
  ret_ok ret ->
  v1 = ret ->
  store_ok SEGS m (Z_to_bv 64 pp) 8 = true ->
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
  getr regs 2 = Z_to_bv 64 (s - 96) ->
  getr regs 19 = Z_to_bv 64 pp ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x19128) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' ret M' rom /\
      rinv [(pp, 8%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) /\
      getr regs' 2 = Z_to_bv 64 s /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\ getr regs' 21 = v21 /\ getr regs' 22 = v22 /\ getr regs' 23 = v23 /\ getr regs' 24 = v24 /\ getr regs' 25 = v25 /\ getr regs' 26 = v26 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26]%list) regs regs').
Proof.
  intros fx regs m s pp ret v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 Hs Hpp Hpp47 DJ Hret E1 SOK
    R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 H2 H19. subst v1.
  unfold reach. eexists. split.
  - norm_pc.
    sn F_19128 D_19128.
    stepST F_1912c D_1912c (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(sok_in SOK).
    stepLD8 F_19130 D_19130 ret.
    stepLD8 F_19134 D_19134 v8.
    stepLD8 F_19138 D_19138 v9.
    stepLD8 F_1913c D_1913c v18.
    stepLD8 F_19140 D_19140 v19.
    stepLD8 F_19144 D_19144 v20.
    stepLD8 F_19148 D_19148 v21.
    stepLD8 F_1914c D_1914c v22.
    stepLD8 F_19150 D_19150 v23.
    stepLD8 F_19154 D_19154 v24.
    stepLD8 F_19158 D_19158 v25.
    stepLD8 F_1915c D_1915c v26.
    zv F_19160 D_19160 (Z_to_bv 64 s).
    stepret F_19164 D_19164 ret ltac:(bveq).
    apply mst_refl.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

End Segs.
