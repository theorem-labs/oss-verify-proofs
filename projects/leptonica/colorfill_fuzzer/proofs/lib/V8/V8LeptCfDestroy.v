(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.colorfill_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptDefs LeptStructs LeptArith LibAtomic LeptRecs LeptSlots.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require Import V8LeptStderr V8LeptBase V8LeptBoxa V8LeptPtra V8LeptPixa.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require Import V8CL7a.
Import V8CL7a.V8LeptPixMisc.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require Import V8CL11a.
Import V8CL11a.V8LeptCf.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require Import V8_code_14000_15000 V8_code_15000_16000 V8_code_16000_17000 V8_code_17000_18000.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Local Ltac forall_cells := repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil.
(* [comment removed for export] *)
Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).

Section CfDestroy.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU8} {PU8 : V8Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
Variable rom : word -> option byte.

  Definition cdF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).
  Definition cd_cells (m : word -> option byte) (s : Z) (ret : word) (R : bvmap 5 word) : Prop :=
    cellsZ m [(s - 8, ret); (s - 16, getr R 8); (s - 24, getr R 9)]%Z.
  Lemma cdF_cells : forall m s ret regs, (32 <= s)%Z -> (s < 2 ^ 64)%Z -> cd_cells (cdF m s ret regs) s ret regs.
  Proof. intros m s ret regs Hs Hs64. unfold cd_cells, cdF. cbn [cellsZ]. repeat split; rdn_solve. Qed.

  (* [comment removed for export] *)
  Lemma cd_A : forall regs m (s pp v : Z) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (0 <= v < 2 ^ 64)%Z -> (pp mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 v) -> (pp + 8 <= s - 32 \/ s <= pp)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x17030 : word) m rom) (mkst regs' (0x17054 : word) (cdF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 8 = Z_to_bv 64 pp /\ getr regs' 9 = Z_to_bv 64 v
      /\ regs_agree (fun r => In r [2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s pp v ret Hs Hs64 Hpp Hpp64 Hv ALpp SOK Rpp DJ H2 H1 H10.
    eexists. split.
    - zv F_16f2c D_16f2c (Z_to_bv 64 (s - 32)).
      stepST F_16f30 D_16f30 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_16f34 D_16f34 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_16f38 D_16f38 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_16f3c D_16f3c ltac:(condZ).
      sn F_16f40 D_16f40.
      zand F_16f44 D_16f44 andi_7 ALpp. stepb_ft F_16f48 D_16f48 ltac:(condZ).
      stepLD F_16f4c D_16f4c (Z_to_le_bytes 8 v) (Z_to_bv 64 v) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma cd_epi : forall regs m (s : Z) (ret : word) (R : bvmap 5 word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cd_cells m s ret R ->
    getr regs 2 = Z_to_bv 64 (s - 32) ->
    exists regs',
      msteps SEGS (mkst regs (0x170e8 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = getr R 8 /\ getr regs' 9 = getr R 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9]%list) regs regs'.
  Proof.
    intros regs m s ret R Hs Hs64 Hret CE H2. destruct CE as (C8 & C16 & C24 & _).
    eexists. split.
    - stepLD8 F_16fe4 D_16fe4 ret. stepLD8 F_16fe8 D_16fe8 (getr R 8). stepLD8 F_16fec D_16fec (getr R 9).
      zv F_16ff0 D_16ff0 (Z_to_bv 64 s).
      stepret F_16ff4 D_16ff4 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma cd_Z : forall regs m,
    getr regs 9 = Z_to_bv 64 0 ->
    msteps SEGS (mkst regs (0x17054 : word) m rom) (mkst regs (0x170e8 : word) m rom).
  Proof. intros regs m H9. stepb_tk F_16f50 D_16f50 ltac:(condZ). apply mst_refl. Qed.

  (* [comment removed for export] *)
  Lemma cd_1 : forall regs m (cf : Z),
    (1 <= cf)%Z -> (cf + 88 < 2 ^ 64)%Z -> (cf mod 8 = 0)%Z -> getr regs 9 = Z_to_bv 64 cf ->
    exists regs',
      msteps SEGS (mkst regs (0x17054 : word) m rom) (mkst regs' (0x154fc : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x17068 /\ getr regs' 10 = Z_to_bv 64 cf /\ getr regs' 9 = Z_to_bv 64 cf /\ getr regs' 8 = getr regs 8
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m cf Hcf Hcf64 ALcf H9. eexists. split.
    - stepb_ft F_16f50 D_16f50 ltac:(condZ). zand F_16f54 D_16f54 andi_7 ALcf. stepb_ft F_16f58 D_16f58 ltac:(condZ).
      sn F_16f5c D_16f5c. sn F_16f60 D_16f60. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cd_2 : forall regs m (cf : Z),
    (0 <= cf)%Z -> (cf + 88 < 2 ^ 64)%Z -> getr regs 9 = Z_to_bv 64 cf ->
    exists regs',
      msteps SEGS (mkst regs (0x17068 : word) m rom) (mkst regs' (0x154fc : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x17070 /\ getr regs' 10 = Z_to_bv 64 (cf + 8) /\ getr regs' 9 = Z_to_bv 64 cf /\ getr regs' 8 = getr regs 8
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m cf Hcf Hcf64 H9. eexists. split.
    - zv F_16f64 D_16f64 (Z_to_bv 64 (cf + 8)). sn F_16f68 D_16f68. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cd_3 : forall regs m (cf : Z),
    (0 <= cf)%Z -> (cf + 88 < 2 ^ 64)%Z -> getr regs 9 = Z_to_bv 64 cf ->
    exists regs',
      msteps SEGS (mkst regs (0x17070 : word) m rom) (mkst regs' (0x14a20 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x17078 /\ getr regs' 10 = Z_to_bv 64 (cf + 40) /\ getr regs' 9 = Z_to_bv 64 cf /\ getr regs' 8 = getr regs 8
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m cf Hcf Hcf64 H9. eexists. split.
    - zv F_16f6c D_16f6c (Z_to_bv 64 (cf + 40)). sn F_16f70 D_16f70. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cd_4 : forall regs m (cf : Z),
    (0 <= cf)%Z -> (cf + 88 < 2 ^ 64)%Z -> getr regs 9 = Z_to_bv 64 cf ->
    exists regs',
      msteps SEGS (mkst regs (0x17078 : word) m rom) (mkst regs' (0x146c0 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x17080 /\ getr regs' 10 = Z_to_bv 64 (cf + 48) /\ getr regs' 9 = Z_to_bv 64 cf /\ getr regs' 8 = getr regs 8
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m cf Hcf Hcf64 H9. eexists. split.
    - zv F_16f74 D_16f74 (Z_to_bv 64 (cf + 48)). sn F_16f78 D_16f78. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cd_5 : forall regs m (cf : Z),
    (0 <= cf)%Z -> (cf + 88 < 2 ^ 64)%Z -> getr regs 9 = Z_to_bv 64 cf ->
    exists regs',
      msteps SEGS (mkst regs (0x17080 : word) m rom) (mkst regs' (0x146c0 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x17088 /\ getr regs' 10 = Z_to_bv 64 (cf + 56) /\ getr regs' 9 = Z_to_bv 64 cf /\ getr regs' 8 = getr regs 8
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m cf Hcf Hcf64 H9. eexists. split.
    - zv F_16f7c D_16f7c (Z_to_bv 64 (cf + 56)). sn F_16f80 D_16f80. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cd_6 : forall regs m (cf : Z),
    (0 <= cf)%Z -> (cf + 88 < 2 ^ 64)%Z -> getr regs 9 = Z_to_bv 64 cf ->
    exists regs',
      msteps SEGS (mkst regs (0x17088 : word) m rom) (mkst regs' (0x14404 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x17090 /\ getr regs' 10 = Z_to_bv 64 (cf + 64) /\ getr regs' 9 = Z_to_bv 64 cf /\ getr regs' 8 = getr regs 8
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m cf Hcf Hcf64 H9. eexists. split.
    - zv F_16f84 D_16f84 (Z_to_bv 64 (cf + 64)). sn F_16f88 D_16f88. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cd_7 : forall regs m (cf : Z),
    (0 <= cf)%Z -> (cf + 88 < 2 ^ 64)%Z -> getr regs 9 = Z_to_bv 64 cf ->
    exists regs',
      msteps SEGS (mkst regs (0x17090 : word) m rom) (mkst regs' (0x14168 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x17098 /\ getr regs' 10 = Z_to_bv 64 (cf + 72) /\ getr regs' 9 = Z_to_bv 64 cf /\ getr regs' 8 = getr regs 8
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m cf Hcf Hcf64 H9. eexists. split.
    - zv F_16f8c D_16f8c (Z_to_bv 64 (cf + 72)). sn F_16f90 D_16f90. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cd_8 : forall regs m (cf : Z),
    (0 <= cf)%Z -> (cf + 88 < 2 ^ 64)%Z -> getr regs 9 = Z_to_bv 64 cf ->
    exists regs',
      msteps SEGS (mkst regs (0x17098 : word) m rom) (mkst regs' (0x146c0 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x170a0 /\ getr regs' 10 = Z_to_bv 64 (cf + 80) /\ getr regs' 9 = Z_to_bv 64 cf /\ getr regs' 8 = getr regs 8
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m cf Hcf Hcf64 H9. eexists. split.
    - zv F_16f94 D_16f94 (Z_to_bv 64 (cf + 80)). sn F_16f98 D_16f98. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cd_9 : forall regs m (cf : Z),
    getr regs 9 = Z_to_bv 64 cf ->
    exists regs',
      msteps SEGS (mkst regs (0x170a0 : word) m rom) (mkst regs' (0x17c54 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x170a8 /\ getr regs' 10 = Z_to_bv 64 cf /\ getr regs' 9 = Z_to_bv 64 cf /\ getr regs' 8 = getr regs 8
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m cf H9. eexists. split.
    - sn F_16f9c D_16f9c. sn F_16fa0 D_16fa0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cd_E : forall regs m (pp : Z),
    (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 pp) 8 = true ->
    getr regs 8 = Z_to_bv 64 pp ->
    msteps SEGS (mkst regs (0x170a8 : word) m rom) (mkst regs (0x170e8 : word) (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom).
  Proof.
    intros regs m pp Hpp Hpp64 SOKp H8.
    stepST F_16fa4 D_16fa4 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOKp).
    sn F_16fa8 D_16fa8. apply mst_refl.
  Qed.
End Segs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cdF_out : forall m s ret regs (x : word), (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (u x < s - 32 \/ s <= u x)%Z -> cdF m s ret regs x = m x.
Proof.
  intros m s ret regs x Hs Hs64 Hx. unfold cdF.
  repeat (rewrite wbytes_outside; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
  reflexivity.
Qed.

Lemma cellsZ_pd3 : forall C A s pp m m' l, Cok C -> POSTD C A s pp m m' -> (c_top C - LSTK <= s)%Z ->
  Forall (fun av => s <= fst av /\ fst av + 8 <= 2 ^ 64 /\ (pp + 8 <= fst av \/ fst av + 8 <= pp))%Z l -> cellsZ m l -> cellsZ m' l.
Proof.
  intros C A s pp m m' l CK PD Hlo HL. induction l as [|[a v] t IH]; intros CE; [exact I|].
  destruct CE as [R CE]. inversion HL as [|x t' (Ha & Hn & Hd) HL']; subst. cbn in Ha, Hn, Hd.
  split; [| exact (IH HL' CE)]. rewrite <- pu8_segs, (POSTD_rdn_above C A s pp m m' a 8 CK PD); [rewrite pu8_segs; exact R | lia | cbn; lia | lia | cbn; lia].
Qed.

Section Walk.
  Variables (C : lctx) (A0 A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s pp : Z) (ret : word) (v : pixv) (o : cfo) (S : TSet).
  Hypothesis CK : Cok C.
  Hypothesis Hs16 : (s mod 16 = 0)%Z.
  Hypothesis Hlo : (c_top C - LSTK + 176 + ALLOC_STACK <= s)%Z.
  Hypothesis Hhi : (s <= c_top C)%Z.
  Hypothesis Hret : ret_ok ret.
  Hypothesis H2 : getr regs 2 = Z_to_bv 64 s.
  Hypothesis H4 : getr regs 4 = Z_to_bv 64 0x31b70.
  Hypothesis Hpp : (s <= pp)%Z.
  Hypothesis Hpphi : (pp + 8 <= c_top C)%Z.
  Hypothesis ALpp : (pp mod 8 = 0)%Z.
  Hypothesis Z0 : live (c_A0 C) (Z_to_bv 64 0) = None.
  Hypothesis CF : cf_ok C A0 A m v o.
  Hypothesis HWe : W C A m md.   (* [comment removed for export] *)
  Hypothesis HK : forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     PIXat m' (o_pix o) (set_rc v 1) -> live A' (Z_to_bv 64 (o_pix o)) = Some 64%Z ->
     (forall (q : Z) k, live A0 (Z_to_bv 64 q) = Some k -> (0 <= q < 2 ^ 64)%Z -> q <> o_pix o -> keeps A A' m m' q) ->
     sub_live A' A ->
     POSTD C (c_A0 C) s pp m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S.

  #[local] Notation cf := (o_cf o) (only parsing).
  #[local] Notation pix := (o_pix o) (only parsing).

  (* [comment removed for export] *)
  Definition ST (fp fb fn fd fpx : Z) (NF : word -> Prop) (Ak : AS) (mk : word -> option byte) (vmk : VmMaps) (rk : bvmap 5 word) : Prop :=
    roomtr A (m_vmmaps md) Ak vmk 0 0 /\
    W C Ak mk (with_vmmaps vmk md) /\
    getr rk 2 = Z_to_bv 64 (s - 32) /\ getr rk 8 = Z_to_bv 64 pp /\ getr rk 9 = Z_to_bv 64 cf /\ getr rk 4 = Z_to_bv 64 0x31b70 /\
    getr rk 3 = getr regs 3 /\ (forall r, In r [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr rk r = getr regs r) /\
    cd_cells mk s ret regs /\
    RECat mk cf (cf_flds fp (o_tw o) (o_th o) fb fn fd fpx) /\
    PIXat mk pix (set_rc v 1) /\
    live Ak (Z_to_bv 64 cf) = Some 88%Z /\ live Ak (Z_to_bv 64 pix) = Some 64%Z /\ sub_live Ak A /\
    (forall q : Z, (0 <= q < 2 ^ 64)%Z -> q <> cf -> q <> pix -> live Ak (Z_to_bv 64 q) = live A (Z_to_bv 64 q) -> keeps A Ak m mk q) /\
    (forall q : word, NF q -> live Ak q = live A q) /\
    POSTM C (c_A0 C) s m mk.

  (* [comment removed for export] *)
  Definition nf_ba (q : word) : Prop := o_ba o <> 0%Z -> q <> Z_to_bv 64 (o_ba o) /\ q <> Z_to_bv 64 (o_barr o) /\ (o_nb o = 1%Z -> q <> Z_to_bv 64 (o_b0 o)).
  Definition nf_naa (q : word) : Prop := o_naa o <> 0%Z -> q <> Z_to_bv 64 (o_naa o) /\ q <> Z_to_bv 64 (o_narr o).
  Definition nf_dnaa (q : word) : Prop := o_dnaa o <> 0%Z -> q <> Z_to_bv 64 (o_dnaa o) /\ q <> Z_to_bv 64 (o_darr o).
  Definition nf_px (q : word) : Prop := o_px o <> 0%Z -> q <> Z_to_bv 64 (o_px o) /\ q <> Z_to_bv 64 (o_parr o) /\ q <> Z_to_bv 64 (o_pba o) /\ q <> Z_to_bv 64 (o_pbarr o).
  Definition NF1 (q : word) : Prop := True.
  Definition NF3 (q : word) : Prop := nf_ba q.
  Definition NF6 (q : word) : Prop := nf_ba q /\ nf_naa q.
  Definition NF7 (q : word) : Prop := nf_ba q /\ nf_naa q /\ nf_dnaa q.
  Definition NF8 (q : word) : Prop := nf_ba q /\ nf_naa q /\ nf_dnaa q /\ nf_px q.

  (* [comment removed for export] *)
  Lemma ALcfk : forall k, (k mod 8 = 0)%Z -> ((o_cf o + k) mod 8 = 0)%Z.
  Proof.
    intros k Hk. pose proof CF as (RC & Lcf0 & _). pose proof (RECat_range m (o_cf o) _ RC) as [Wcf0 Wcf]. cbn in Wcf.
    pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HWe) Lcf0) as (_ & AL16 & _). rewrite u_Z2bv in AL16 by lia.
    apply mod16_plus_mod8; [exact AL16 | exact Hk].
  Qed.

  (* [comment removed for export] *)
  Lemma J9 : forall A8 m8 vm8 r8, ST 0 0 0 0 0 NF8 A8 m8 vm8 r8 ->
    realizes SEGS (mkCfg (mkst r8 (0x170a0 : word) m8 al_rom) (with_vmmaps vm8 md)) S.
  Proof.
    intros A8 m8 vm8 r8 (RT & HW8 & R2 & R8 & R9 & R4 & R3 & RR & CE8 & RC8 & PX8 & Lcf & Lpix & SUB8 & KP8 & NF & PM8).
    pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU8] in *. unfold ALLOC_STACK in Hlo.
    pose proof CF as (RC & Lcf0 & L0cf & PX & RC2 & Halp & Lpix0 & L0pix & _).
    pose proof (RECat_range m cf _ RC) as [Wcf0 Wcf]. cbn in Wcf. pose proof PX as (Wp0 & Wp64 & _).
    assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
    destruct (cd_9 al_rom r8 m8 cf R9) as (r9 & RUN9 & U2 & U1 & U10 & U9 & U8 & AG9).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact RUN9 |].
    assert (U2' : getr r9 2 = Z_to_bv 64 (s - 32)) by (rewrite U2; exact R2).
    assert (U4 : getr r9 4 = Z_to_bv 64 0x31b70) by (csr; reflexivity).
    replace (0x17c54 : word) with (Z_to_bv 64 0x17c54) by (apply bv_eq; reflexivity).
    apply (W_free16 C A8 m8 _ r9 (Z_to_bv 64 cf) (Z_to_bv 64 0x170a8) 88 (s - 32) S CK HW8 U10 Lcf L0cf U1
             ltac:(red; apply bv_eq; reflexivity) U4 U2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A9 m9 vm9 r10 HW9 CS9 Lcf9 LEQ9 PM9 HRT9. rewrite with_vmmaps_twice in HW9. rewrite with_vmmaps_twice.
    replace (Z_to_bv 64 0x170a8) with (0x170a8 : word) by (apply bv_eq; reflexivity).
    assert (SUB9 : sub_live A9 A8).
    { intros q k L. destruct (bv_eq_dec _ q (Z_to_bv 64 cf)) as [->|NE]; [congruence|]. rewrite <- (LEQ9 q NE). exact L. }
    pose proof (W_sok_win C A9 m9 _ pp 8 CK HW9 ltac:(lia) ltac:(cbn; lia)) as SOKp.
    assert (E8 : getr r10 8 = Z_to_bv 64 pp) by (csr; reflexivity).
    pose proof (cd_E al_rom r10 m9 pp ltac:(lia) ltac:(lia) SOKp E8) as RUN10.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact RUN10 |].
    set (M10 := wbytes m9 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    assert (HW10 : W C A9 M10 (with_vmmaps vm9 md)).
    { subst M10. apply (W_store_win C A9 m9 _ _ _ CK HW9); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; [lia | cbn; lia]. }
    assert (CE10 : cd_cells M10 s ret regs).
    { unfold cd_cells. apply (cellsZ_out m9 M10 pp (pp + 8)).
      - intros x Hx. subst M10. apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
      - clear -HsR Hpp. forall_cells.
      - apply (cellsZ_frm C (s - 32) m8 m9); [exact CK | exact (proj1 PM9) | lia | clear -HsR; forall_cells | exact CE8]. }
    assert (E2 : getr r10 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    destruct (cd_epi al_rom r10 M10 s ret regs ltac:(lia) ltac:(lia) Hret CE10 E2) as (r11 & RUN11 & V2 & V1 & V8 & V9 & AG11).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW10)) | exact (mp_lazy _ (w_pure _ _ _ _ HW10)) | exact RUN11 |].
    apply (HK A9 M10 vm9 r11 HW10).
    - apply cs_kept_intro; rewrite ?V2, ?V8, ?V9, ?H2; try reflexivity.
      all: csr; try reflexivity. all: symmetry; csr; symmetry; apply RR; cbn; tauto.
    - subst M10. apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn].
      + apply (PIXat_frame m8 m9 pix _ PX8). intros x Hx.
        exact (LIVK_byte A9 m8 m9 (Z_to_bv 64 pix) 64 x (proj2 PM9) ltac:(rewrite (LEQ9 _ ltac:(apply (zneq_w pix cf); [lia | lia | intros E; rewrite E in Lpix; congruence])); exact Lpix) ltac:(rewrite u_Z2bv by lia; lia)).
      + destruct (blk_range C A8 m8 _ (Z_to_bv 64 pix) 64 CK HW8 Lpix ltac:(lia)) as [_ TOPp]. rewrite u_Z2bv in TOPp by lia. lia.
    - rewrite (LEQ9 _ ltac:(apply (zneq_w pix cf); [lia | lia | intros E; rewrite E in Lpix; congruence])). exact Lpix.
    - intros q k L0q Hq NEp.
      pose proof CF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S01 & S12 & S23 & S34 & S45 & S5A & _ & Fba & Fb0 & Lcf2 & _ & Fnaa & Fdnaa & Fpx).
      pose proof (sub_live_trans _ _ _ S01 S12) as S02. pose proof (sub_live_trans _ _ _ S02 S23) as S03.
      pose proof (sub_live_trans _ _ _ S03 S34) as S04. pose proof (sub_live_trans _ _ _ S04 S45) as S05.
      assert (NEc : q <> cf).
      { intros ->. exact (live_apart A0 (o_B2 o) _ _ k S02 L0q Lcf2 eq_refl). }
      assert (LAq : live A (Z_to_bv 64 q) = Some k) by (exact (S5A _ _ (S05 _ _ L0q))).
      assert (NFq : NF8 (Z_to_bv 64 q)).
      { split; [|split; [|split]].
        - intros NZ. destruct (Fba NZ) as (N1 & N2 & _). split; [intros E; rewrite E in L0q; congruence|]. split; [intros E; rewrite E in L0q; congruence|].
          intros Hnb. destruct (Fb0 NZ Hnb) as [N3 _]. exact (live_apart A0 (o_B1 o) _ _ k S01 L0q N3).
        - intros NZ. destruct (Fnaa NZ) as (N1 & N2 & _). split; [exact (live_apart A0 (o_B3 o) _ _ k S03 L0q N1) | exact (live_apart A0 (o_B3 o) _ _ k S03 L0q N2)].
        - intros NZ. destruct (Fdnaa NZ) as (N1 & N2 & _). split; [exact (live_apart A0 (o_B4 o) _ _ k S04 L0q N1) | exact (live_apart A0 (o_B4 o) _ _ k S04 L0q N2)].
        - intros NZ. destruct (Fpx NZ) as (N1 & N2 & N3 & N4).
          split; [exact (live_apart A0 (o_B5 o) _ _ k S05 L0q N1)|]. split; [exact (live_apart A0 (o_B5 o) _ _ k S05 L0q N2)|].
          split; [exact (live_apart A0 (o_B5 o) _ _ k S05 L0q N3) | exact (live_apart A0 (o_B5 o) _ _ k S05 L0q N4)]. }
      pose proof (NF _ NFq) as EA8.
      assert (EA9 : live A9 (Z_to_bv 64 q) = live A8 (Z_to_bv 64 q)) by (apply LEQ9; exact (zneq_w q cf ltac:(lia) ltac:(lia) NEc)).
      apply (keeps_trans A A8 A9 m m8 M10 q (KP8 q Hq NEc NEp EA8)).
      apply (keeps_trans A8 A9 A9 m8 m9 M10 q (keeps_postm C A8 A9 A9 (s - 32) m8 m9 _ q HW9 PM9 EA9 EA9 Hq)).
      apply (keeps_agree C A9 A9 m9 M10 _ q HW10 eq_refl Hq). intros k' x L' Hx.
      destruct (blk_range C A9 m9 _ (Z_to_bv 64 q) k' CK HW9 L' ltac:(destruct (Z_lt_le_dec 0 k'); [lia | exfalso; lia])) as [_ TOPq]. rewrite u_Z2bv in TOPq by lia.
      subst M10. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
    - exact (sub_live_trans _ _ _ SUB9 SUB8).
    - apply (POSTD_trans C (c_A0 C) s pp m m9 M10); [| subst M10; apply POSTD_slotw; [rewrite length_N_to_le_bytes; reflexivity | lia | lia]].
      apply (POSTD_of_POSTM C (c_A0 C) (c_A0 C)); [| apply sub_live_refl].
      eapply POSTM_trans; [exact PM8|]. apply (POSTM_sub C (c_A0 C) A9 _ _ _ (w_keep _ _ _ _ HW9)). eapply POSTM_mono; [|exact PM9]. lia.
    - subst M10. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
    - exact (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT (roomtr_wv _ _ _ _ _ _ _ HRT9) ltac:(lia) ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  #[local] Ltac prep :=
    pose proof CK as [T1 T2 T3 T4 T5]; laypins; cbn [fst snd ll_img LLU8] in *; unfold ALLOC_STACK in Hlo.

  (* [comment removed for export] *)
  Lemma ST_null : forall fp fb fn fd fpx (NF NF' : word -> Prop) Ak mk vmk rk mk' rk' (ra : Z),
    ST fp fb fn fd fpx NF Ak mk vmk rk ->
    (forall q, NF' q -> NF q) ->
    W C Ak mk' (with_vmmaps vmk md) -> POSTM C Ak (s - 32) mk mk' ->
    (exists r1, getr r1 2 = getr rk 2 /\ getr r1 9 = Z_to_bv 64 cf /\ getr r1 8 = getr rk 8 /\ regs_agree (fun r => In r [1; 10]%list) rk r1 /\ cs_kept r1 rk') ->
    ST fp fb fn fd fpx NF' Ak mk' vmk rk'.
  Proof.
    intros fp fb fn fd fpx NF NF' Ak mk vmk rk mk' rk' ra (RT & HWk & R2 & R8 & R9 & R4 & R3 & RR & CEk & RCk & PXk & Lcf & Lpix & SUBk & KPk & NFk & PMk)
           HNF HW' PM' (r1 & Q2 & Q9 & Q8 & AG & CS). prep.
    pose proof CF as (RC & Lcf0 & L0cf & PX & _). pose proof (RECat_range m cf _ RC) as [Wcf0 Wcf]. cbn in Wcf. pose proof PX as (Wp0 & Wp64 & _).
    assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
    split; [exact RT|]. split; [exact HW'|].
    split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|].
    split; [intros r Hr; transitivity (getr rk r); [| exact (RR r Hr)]; cbn in Hr; repeat (destruct Hr as [<-|Hr]; [csr; reflexivity|]); destruct Hr|].
    split; [unfold cd_cells; apply (cellsZ_frm C (s - 32) mk mk'); [exact CK | exact (proj1 PM') | lia | clear -HsR; forall_cells | exact CEk]|].
    split; [apply (RECat_POSTM C Ak (s - 32) mk mk' (Z_to_bv 64 cf) 88 _ _ RCk PM' Lcf); rewrite u_Z2bv by lia; [lia | cbn; lia]|].
    split; [apply (PIXat_frame mk mk' pix _ PXk); intros x Hx; exact (LIVK_byte Ak mk mk' (Z_to_bv 64 pix) 64 x (proj2 PM') Lpix ltac:(rewrite u_Z2bv by lia; lia))|].
    split; [exact Lcf|]. split; [exact Lpix|]. split; [exact SUBk|].
    split; [intros q Hq NEc NEp Eq; apply (keeps_trans A Ak Ak m mk mk' q (KPk q Hq NEc NEp Eq)); exact (keeps_postm C Ak Ak Ak (s - 32) mk mk' _ q HW' PM' eq_refl eq_refl Hq)|].
    split; [intros q Hq; exact (NFk q (HNF q Hq))|].
    eapply POSTM_trans; [exact PMk|]. apply (POSTM_sub C (c_A0 C) Ak _ _ _ (w_keep _ _ _ _ HW')). eapply POSTM_mono; [|exact PM']. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma J8 : forall A7 m7 vm7 r7, ST 0 0 0 0 (o_px o) NF7 A7 m7 vm7 r7 ->
    realizes SEGS (mkCfg (mkst r7 (0x17098 : word) m7 al_rom) (with_vmmaps vm7 md)) S.
  Proof.
    intros A7 m7 vm7 r7 STk. pose proof STk as (RT & HW7 & R2 & R8 & R9 & R4 & R3 & RR & CE7 & RC7 & PX7 & Lcf & Lpix & SUB7 & KP7 & NF & PM7). prep.
    pose proof CF as (RC & Lcf0 & L0cf & PX & RC2 & Halp & LpixA & L0pix & OBA & ONAA & ODNAA & OPX & S01 & S12 & S23 & S34 & S45 & S5A & Lpix0 & Fba & Fb0 & Lcf2 & Lcf3 & Fnaa & Fdnaa & Fpx).
    pose proof (sub_live_trans _ _ _ S01 S12) as S02. pose proof (sub_live_trans _ _ _ S02 S23) as S03.
    pose proof (sub_live_trans _ _ _ S03 S34) as S04. pose proof (sub_live_trans _ _ _ S04 S45) as S05.
    pose proof (sub_live_trans _ _ _ S34 S45) as S35. pose proof (sub_live_trans _ _ _ S12 S23) as S13.
    pose proof (sub_live_trans _ _ _ S13 S35) as S15.
    pose proof (RECat_range m cf _ RC) as [Wcf0 Wcf]. cbn in Wcf. pose proof PX as (Wp0 & Wp64 & _).
    assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
    destruct (cd_8 al_rom r7 m7 cf ltac:(lia) ltac:(lia) R9) as (r8 & RUN8 & U2 & U1 & U10 & U9 & U8 & AG8).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact RUN8 |].
    assert (U2' : getr r8 2 = Z_to_bv 64 (s - 32)) by (rewrite U2; exact R2).
    assert (U4 : getr r8 4 = Z_to_bv 64 0x31b70) by (csr; reflexivity).
    assert (SL : slotok C A7 (s - 32) (cf + 80) (Some (Z_to_bv 64 cf, 88%Z))).
    { cbn. rewrite u_Z2bv by lia. split; [exact Lcf|]. split; [exact L0cf|]. lia. }
    assert (RD : rdn SEGS m7 (Z_to_bv 64 (cf + 80)) 8 = Some (Z_to_le_bytes 8 (o_px o))).
    { eapply (REC_rd' SEGS _ _ (cf_flds 0 (o_tw o) (o_th o) 0 0 0 (o_px o)) 13 8); [exact RC7 | cbn; lia | reflexivity | reflexivity | reflexivity]. }
    destruct OPX as [Hpx0 | PXA].
    - (* [comment removed for export] *)
      rewrite Hpx0 in RD.
      apply (pixaDestroy_null_W C A7 m7 _ r8 (s - 32) (cf + 80) (Some (Z_to_bv 64 cf, 88%Z)) (Z_to_bv 64 0x170a0) S CK HW7 U2'
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(lia) ltac:(lia) U1 ltac:(red; apply bv_eq; reflexivity) U10 SL (ALcfk 80 eq_refl) RD).
      intros m8 r9 HW8 CS8 PM8. replace (Z_to_bv 64 0x170a0) with (0x170a0 : word) by (apply bv_eq; reflexivity).
      apply (J9 A7 m8 vm7 r9). rewrite Hpx0 in STk.
      apply (ST_null 0 0 0 0 0 NF7 NF8 A7 m7 vm7 r7 m8 r9 0 STk); [intros q (X1 & X2 & X3 & _); exact (conj X1 (conj X2 X3)) | exact HW8 | exact PM8 |].
      exists r8. split; [exact U2|]. split; [exact U9|]. split; [exact U8|]. split; [exact AG8 | exact CS8].
    - (* [comment removed for export] *)
      pose proof PXA as (RP & Halx & LpxA' & L0px & Lparr & L0parr & _ & NE1 & BA & NE2 & NE3 & NE4 & NE5).
      pose proof BA as (RB & _ & Lpba & L0pba & ARRB).
      pose proof (RECat_range m _ _ RP) as [Wpx0 Wpx]. cbn in Wpx. pose proof (RECat_range m _ _ RB) as [Wb0 Wb]. cbn in Wb.
      pose proof (PIXA_wf m _ 0 20 1 _ _ RP) as (_ & _ & Wparr & Wpba & _).
      pose proof (BOXA_wf m _ 0 20 1 _ RB) as (_ & _ & Wpbarr & _).
      destruct (blk_range C A m md (Z_to_bv 64 (o_px o)) 32 CK HWe LpxA' ltac:(lia)) as [Gpx _]. rewrite u_Z2bv in Gpx by lia.
      assert (Hcf : (0 <= cf < 2 ^ 64)%Z) by lia. assert (Hpix : (0 <= pix < 2 ^ 64)%Z) by lia.
      assert (H1 : (0 <= o_px o < 2 ^ 64)%Z) by lia. assert (H2' : (0 <= o_parr o < 2 ^ 64)%Z) by lia.
      assert (H3 : (0 <= o_pba o < 2 ^ 64)%Z) by lia. assert (H4' : (0 <= o_pbarr o < 2 ^ 64)%Z) by lia.
      destruct (Fpx ltac:(lia)) as (F1 & F2 & F3 & F4).
      (* [comment removed for export] *)
      assert (NQ : forall y : Z, live (o_B5 o) (Z_to_bv 64 y) = None -> (0 <= y < 2 ^ 64)%Z ->
                 y <> cf /\ y <> pix /\ NF7 (Z_to_bv 64 y)).
      { intros y Fy Hy. split; [intros ->; exact (live_apart (o_B3 o) (o_B5 o) _ _ 88%Z S35 Lcf3 Fy eq_refl)|].
        split; [intros ->; exact (live_apart A0 (o_B5 o) _ _ 64%Z S05 Lpix0 Fy eq_refl)|].
        split; [|split].
        - intros NZ. destruct (Fba NZ) as (_ & _ & Xa & Xr).
          split; [exact (not_eq_sym (live_apart (o_B1 o) (o_B5 o) _ _ _ S15 Xa Fy))|].
          split; [exact (not_eq_sym (live_apart (o_B1 o) (o_B5 o) _ _ _ S15 Xr Fy))|].
          intros Hnb. destruct (Fb0 NZ Hnb) as [_ Xb]. exact (not_eq_sym (live_apart (o_B2 o) (o_B5 o) _ _ _ (sub_live_trans _ _ _ S23 S35) Xb Fy)).
        - intros NZ. destruct (Fnaa NZ) as (_ & _ & Xa & Xr).
          split; [exact (not_eq_sym (live_apart (o_B4 o) (o_B5 o) _ _ _ S45 Xa Fy)) | exact (not_eq_sym (live_apart (o_B4 o) (o_B5 o) _ _ _ S45 Xr Fy))].
        - intros NZ. destruct (Fdnaa NZ) as (_ & _ & Xa & Xr).
          split; [exact (not_eq_sym (live_apart (o_B5 o) (o_B5 o) _ _ _ (sub_live_refl _) Xa Fy)) | exact (not_eq_sym (live_apart (o_B5 o) (o_B5 o) _ _ _ (sub_live_refl _) Xr Fy))]. }
      destruct (NQ _ F1 H1) as (Nc1 & Np1 & Nf1). destruct (NQ _ F2 H2') as (Nc2 & Np2 & Nf2).
      destruct (NQ _ F3 H3) as (Nc3 & Np3 & Nf3). destruct (NQ _ F4 H4') as (Nc4 & Np4 & Nf4).
      assert (PXA7 : pixa_at C A7 m7 (o_px o) 20 (o_parr o) (o_pba o) 20 (o_pbarr o)).
      { exact (pixa_at_transport C A A7 m m7 _ 20 _ _ 20 _ PXA (KP7 _ H1 Nc1 Np1 (NF _ Nf1)) (KP7 _ H2' Nc2 Np2 (NF _ Nf2)) (KP7 _ H3 Nc3 Np3 (NF _ Nf3)) (KP7 _ H4' Nc4 Np4 (NF _ Nf4))). }
      apply (pixaDestroy_W C A7 m7 _ r8 (s - 32) (cf + 80) (o_px o) 20 (o_parr o) (o_pba o) 20 (o_pbarr o) (Some (Z_to_bv 64 cf, 88%Z)) (Z_to_bv 64 0x170a0) S
               CK HW7 U2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) U1 ltac:(red; apply bv_eq; reflexivity) U4 U10 SL (ALcfk 80 eq_refl) RD Z0 PXA7).
      { intros p k E. injection E as <- <-.
        split; [exact (zneq_w cf (o_px o) Hcf H1 (not_eq_sym Nc1))|]. split; [exact (zneq_w cf (o_parr o) Hcf H2' (not_eq_sym Nc2))|].
        split; [exact (zneq_w cf (o_pba o) Hcf H3 (not_eq_sym Nc3)) | exact (zneq_w cf (o_pbarr o) Hcf H4' (not_eq_sym Nc4))]. }
      intros A8 m8 vm8 r9 HW8 CS8 L1 L2 L3 L4 LEQ8 SUB8 PD8 RD8 HRT8. rewrite with_vmmaps_twice in HW8. rewrite with_vmmaps_twice.
      replace (Z_to_bv 64 0x170a0) with (0x170a0 : word) by (apply bv_eq; reflexivity).
      assert (E8 : forall q : Z, (0 <= q < 2 ^ 64)%Z -> q <> o_px o -> q <> o_parr o -> q <> o_pba o -> q <> o_pbarr o -> live A8 (Z_to_bv 64 q) = live A7 (Z_to_bv 64 q)).
      { intros q Hq X1 X2 X3 X4. apply LEQ8; [exact (zneq_w q _ Hq H1 X1) | exact (zneq_w q _ Hq H2' X2) | exact (zneq_w q _ Hq H3 X3) | exact (zneq_w q _ Hq H4' X4)]. }
      assert (Lcf8 : live A8 (Z_to_bv 64 cf) = Some 88%Z) by (rewrite (E8 cf Hcf (not_eq_sym Nc1) (not_eq_sym Nc2) (not_eq_sym Nc3) (not_eq_sym Nc4)); exact Lcf).
      assert (Lpix8 : live A8 (Z_to_bv 64 pix) = Some 64%Z) by (rewrite (E8 pix Hpix (not_eq_sym Np1) (not_eq_sym Np2) (not_eq_sym Np3) (not_eq_sym Np4)); exact Lpix).
      apply (J9 A8 m8 vm8 r9). split; [exact (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT (roomtr_wv _ _ _ _ _ _ _ HRT8) ltac:(lia) ltac:(lia))|]. split; [exact HW8|].
      split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|].
      split; [intros r Hr; transitivity (getr r7 r); [| exact (RR r Hr)]; cbn in Hr; repeat (destruct Hr as [<-|Hr]; [csr; reflexivity|]); destruct Hr|].
      split; [unfold cd_cells; apply (cellsZ_pd3 C A8 (s - 32) (cf + 80) m7 m8); [exact CK | exact PD8 | lia | | exact CE7]|].
      { destruct (blk_range C A7 m7 _ (Z_to_bv 64 cf) 88 CK HW7 Lcf ltac:(lia)) as [_ TOPc]. rewrite u_Z2bv in TOPc by lia. clear -HsR TOPc T1 Hlo PIN7. forall_cells. }
      split.
      { (* [comment removed for export] *)
        change (cf_flds 0 (o_tw o) (o_th o) 0 0 0 0) with (fld_set (cf_flds 0 (o_tw o) (o_th o) 0 0 0 (o_px o)) 13 0).
        apply (RECat_set_rdn SEGS m7 m8 cf _ 13 0 RC7); [clear; cbn; lia | clear; cbn; lia | | | exact RD8].
        - intros x Hx Hoff.
          assert (Q1 : (u (Z_to_bv 64 cf) <= u x < u (Z_to_bv 64 cf) + 88)%Z) by (clear -Hx Hcf; rewrite u_Z2bv by lia; cbn in Hx; lia).
          assert (Q2 : ~ inslot (cf + 80) x) by (clear -Hoff; unfold inslot; cbn in Hoff; lia).
          exact (POSTD_blk_byte C A8 (s - 32) (cf + 80) m7 m8 (Z_to_bv 64 cf) 88 x PD8 Lcf8 Q1 Q2).
        - intros x Hx.
          assert (Q1 : (u (Z_to_bv 64 cf) <= u x < u (Z_to_bv 64 cf) + 88)%Z) by (clear -Hx Hcf; rewrite u_Z2bv by lia; cbn in Hx; lia).
          destruct (blk_byte C A8 m8 _ (Z_to_bv 64 cf) 88 x CK HW8 Lcf8 Q1) as (_ & D & _). exact D. }
      assert (Kpix : keeps A7 A8 m7 m8 pix).
      { apply (keeps_step C A7 A8 m7 m8 _ (s - 32) (cf + 80) cf pix 88 CK HW8 PD8 Lcf8 Hcf ltac:(clear; lia) ltac:(clear; lia)); [rewrite Lpix8, Lpix; reflexivity | exact Hpix |].
        intros E. exact (live_apart A0 (o_B2 o) _ _ 64%Z S02 Lpix0 Lcf2 (f_equal (Z_to_bv 64) E)). }
      split; [apply (PIXat_frame m7 m8 pix _ PX7); destruct (Kpix 64%Z Lpix) as (_ & _ & M); exact M|].
      split; [exact Lcf8|]. split; [exact Lpix8|]. split; [exact (sub_live_trans _ _ _ SUB8 SUB7)|].
      split.
      { intros q Hq NEc NEp E8q k LAq. rewrite <- E8q in LAq.
        pose proof (SUB8 _ _ LAq) as L7q.
        assert (E78 : live A8 (Z_to_bv 64 q) = live A7 (Z_to_bv 64 q)) by (rewrite LAq, L7q; reflexivity).
        refine (keeps_trans A A7 A8 m m7 m8 q (KP7 q Hq NEc NEp ltac:(rewrite L7q, <- LAq; exact E8q)) _ k _); [| rewrite E8q in LAq; exact LAq].
        exact (keeps_step C A7 A8 m7 m8 _ (s - 32) (cf + 80) cf q 88 CK HW8 PD8 Lcf8 Hcf ltac:(clear; lia) ltac:(clear; lia) E78 Hq NEc). }
      split.
      { intros q (Xb & Xn & Xd & Xp). destruct (Xp ltac:(clear -Gpx; lia)) as (Y1 & Y2 & Y3 & Y4). rewrite (LEQ8 q Y1 Y2 Y3 Y4). apply NF. exact (conj Xb (conj Xn Xd)). }
      eapply POSTM_trans; [exact PM7|]. apply (POSTM_mono C (c_A0 C) (s - 32) s); [lia|].
      apply (POSTD_POSTM_blk C (c_A0 C) A8 m8 _ (Z_to_bv 64 cf) 88 (s - 32) (cf + 80) m7 m8 CK HW8 Lcf8); [clear -Hcf; rewrite u_Z2bv by lia; lia | clear -Hcf; rewrite u_Z2bv by lia; lia | exact L0cf | exact (w_keep _ _ _ _ HW8) |].
      exact (POSTD_sub C A8 (c_A0 C) _ _ _ _ (w_keep _ _ _ _ HW8) PD8).
  Qed.

  (* [comment removed for export] *)
  Lemma J7 : forall A7 m7 vm7 r7, ST 0 0 0 (o_dnaa o) (o_px o) NF6 A7 m7 vm7 r7 ->
    realizes SEGS (mkCfg (mkst r7 (0x17090 : word) m7 al_rom) (with_vmmaps vm7 md)) S.
  Proof.
    intros A7 m7 vm7 r7 STk. pose proof STk as (RT & HW7 & R2 & R8 & R9 & R4 & R3 & RR & CE7 & RC7 & PX7 & Lcf & Lpix & SUB7 & KP7 & NF & PM7). prep.
    pose proof CF as (RC & Lcf0 & L0cf & PX & RC2 & Halp & LpixA & L0pix & OBA & ONAA & ODNAA & OPX & S01 & S12 & S23 & S34 & S45 & S5A & Lpix0 & Fba & Fb0 & Lcf2 & Lcf3 & Fnaa & Fdnaa & Fpx).
    pose proof (sub_live_trans _ _ _ S01 S12) as S02. pose proof (sub_live_trans _ _ _ S02 S23) as S03.
    pose proof (sub_live_trans _ _ _ S03 S34) as S04. pose proof (sub_live_trans _ _ _ S04 S45) as S05.
    pose proof (sub_live_trans _ _ _ S34 S45) as S35. pose proof (sub_live_trans _ _ _ S12 S23) as S13.
    pose proof (sub_live_trans _ _ _ S13 S35) as S15. pose proof (sub_live_trans _ _ _ S13 S34) as S14. pose proof (sub_live_trans _ _ _ S23 S34) as S24.
    pose proof (RECat_range m cf _ RC) as [Wcf0 Wcf]. cbn in Wcf. pose proof PX as (Wp0 & Wp64 & _).
    assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
    assert (Hcf : (0 <= cf < 2 ^ 64)%Z) by lia. assert (Hpix : (0 <= pix < 2 ^ 64)%Z) by lia.
    destruct (cd_7 al_rom r7 m7 cf ltac:(lia) ltac:(lia) R9) as (r8 & RUN8 & U2 & U1 & U10 & U9 & U8 & AG8).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact RUN8 |].
    assert (U2' : getr r8 2 = Z_to_bv 64 (s - 32)) by (rewrite U2; exact R2).
    assert (U4 : getr r8 4 = Z_to_bv 64 0x31b70) by (csr; reflexivity).
    assert (SL : slotok C A7 (s - 32) (cf + 72) (Some (Z_to_bv 64 cf, 88%Z))).
    { cbn. rewrite u_Z2bv by lia. split; [exact Lcf|]. split; [exact L0cf|]. lia. }
    assert (RD : rdn SEGS m7 (Z_to_bv 64 (cf + 72)) 8 = Some (Z_to_le_bytes 8 (o_dnaa o))).
    { eapply (REC_rd' SEGS _ _ (cf_flds 0 (o_tw o) (o_th o) 0 0 (o_dnaa o) (o_px o)) 12 8); [exact RC7 | clear; cbn; lia | reflexivity | reflexivity | reflexivity]. }
    destruct ODNAA as [Hz0 | [PTA Harr0]].
    - rewrite Hz0 in RD.
      apply (l_dnaaDestroy_null_W C A7 m7 _ r8 (s - 32) (cf + 72) (Some (Z_to_bv 64 cf, 88%Z)) (Z_to_bv 64 0x17098) S CK HW7 U2'
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(lia) ltac:(lia) U1 ltac:(red; apply bv_eq; reflexivity) U10 SL (ALcfk 72 eq_refl) RD).
      intros m8 r9 HW8 CS8 PM8. replace (Z_to_bv 64 0x17098) with (0x17098 : word) by (apply bv_eq; reflexivity).
      apply (J8 A7 m8 vm7 r9). rewrite Hz0 in STk.
      apply (ST_null 0 0 0 0 (o_px o) NF6 NF7 A7 m7 vm7 r7 m8 r9 0 STk); [intros q (X1 & X2 & _); exact (conj X1 X2) | exact HW8 | exact PM8 |].
      exists r8. split; [exact U2|]. split; [exact U9|]. split; [exact U8|]. split; [exact AG8 | exact CS8].
    - pose proof PTA as (RP & LpaA & L0pa & ARR).
      pose proof (RECat_range m _ _ RP) as [Wpa0 Wpa]. cbn in Wpa. pose proof (PTRA_wf m _ 1 0 _ RP) as (_ & _ & Warr & _).
      destruct (blk_range C A m md (Z_to_bv 64 (o_dnaa o)) 16 CK HWe LpaA ltac:(lia)) as [Gpa _]. rewrite u_Z2bv in Gpa by lia.
      assert (H1 : (0 <= o_dnaa o < 2 ^ 64)%Z) by lia.
      destruct (Fdnaa ltac:(lia)) as (F1 & F2 & _).
      assert (NQ : forall y : Z, live (o_B4 o) (Z_to_bv 64 y) = None -> (0 <= y < 2 ^ 64)%Z -> y <> cf /\ y <> pix /\ NF6 (Z_to_bv 64 y)).
      { intros y Fy Hy. split; [intros ->; exact (live_apart (o_B3 o) (o_B4 o) _ _ 88%Z S34 Lcf3 Fy eq_refl)|].
        split; [intros ->; exact (live_apart A0 (o_B4 o) _ _ 64%Z S04 Lpix0 Fy eq_refl)|].
        split.
        - intros NZ. destruct (Fba NZ) as (_ & _ & Xa & Xr).
          split; [exact (not_eq_sym (live_apart (o_B1 o) (o_B4 o) _ _ _ S14 Xa Fy))|].
          split; [exact (not_eq_sym (live_apart (o_B1 o) (o_B4 o) _ _ _ S14 Xr Fy))|].
          intros Hnb. destruct (Fb0 NZ Hnb) as [_ Xb]. exact (not_eq_sym (live_apart (o_B2 o) (o_B4 o) _ _ _ S24 Xb Fy)).
        - intros NZ. destruct (Fnaa NZ) as (_ & _ & Xa & Xr).
          split; [exact (not_eq_sym (live_apart (o_B4 o) (o_B4 o) _ _ _ (sub_live_refl _) Xa Fy)) | exact (not_eq_sym (live_apart (o_B4 o) (o_B4 o) _ _ _ (sub_live_refl _) Xr Fy))]. }
      destruct (NQ _ F1 H1) as (Nc1 & Np1 & Nf1). destruct (NQ _ F2 Warr) as (Nc2 & Np2 & Nf2).
      assert (PTA7 : ptra_at C A7 m7 (o_dnaa o) 1 (o_darr o)).
      { exact (ptra_at_transport C A A7 m m7 _ 1 _ PTA (KP7 _ H1 Nc1 Np1 (NF _ Nf1)) (KP7 _ Warr Nc2 Np2 (NF _ Nf2))). }
      apply (l_dnaaDestroy_W C A7 m7 _ r8 (s - 32) (cf + 72) (o_dnaa o) 1 (o_darr o) (Some (Z_to_bv 64 cf, 88%Z)) (Z_to_bv 64 0x17098) S
               CK HW7 U2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) U1 ltac:(red; apply bv_eq; reflexivity) U4 U10 SL (ALcfk 72 eq_refl) RD Z0 PTA7).
      { intros p k E. injection E as <- <-.
        split; [exact (zneq_w cf _ Hcf H1 (not_eq_sym Nc1)) | exact (zneq_w cf _ Hcf Warr (not_eq_sym Nc2))]. }
      intros A8 m8 vm8 r9 HW8 CS8 L1 L2 LEQ8 SUB8 PD8 RD8 HRT8. rewrite with_vmmaps_twice in HW8. rewrite with_vmmaps_twice.
      replace (Z_to_bv 64 0x17098) with (0x17098 : word) by (apply bv_eq; reflexivity).
      assert (E8 : forall q : Z, (0 <= q < 2 ^ 64)%Z -> q <> o_dnaa o -> q <> o_darr o -> live A8 (Z_to_bv 64 q) = live A7 (Z_to_bv 64 q)).
      { intros q Hq X1 X2. apply LEQ8; [exact (zneq_w q _ Hq H1 X1) | exact (zneq_w q _ Hq Warr X2)]. }
      assert (Lcf8 : live A8 (Z_to_bv 64 cf) = Some 88%Z) by (rewrite (E8 cf Hcf (not_eq_sym Nc1) (not_eq_sym Nc2)); exact Lcf).
      assert (Lpix8 : live A8 (Z_to_bv 64 pix) = Some 64%Z) by (rewrite (E8 pix Hpix (not_eq_sym Np1) (not_eq_sym Np2)); exact Lpix).
      apply (J8 A8 m8 vm8 r9). split; [exact (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT (roomtr_wv _ _ _ _ _ _ _ HRT8) ltac:(lia) ltac:(lia))|]. split; [exact HW8|].
      split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|].
      split; [intros r Hr; transitivity (getr r7 r); [| exact (RR r Hr)]; cbn in Hr; repeat (destruct Hr as [<-|Hr]; [csr; reflexivity|]); destruct Hr|].
      split; [unfold cd_cells; apply (cellsZ_pd3 C A8 (s - 32) (cf + 72) m7 m8); [exact CK | exact PD8 | lia | | exact CE7]|].
      { destruct (blk_range C A7 m7 _ (Z_to_bv 64 cf) 88 CK HW7 Lcf ltac:(lia)) as [_ TOPc]. rewrite u_Z2bv in TOPc by lia. clear -HsR TOPc T1 Hlo PIN7. forall_cells. }
      split.
      { change (cf_flds 0 (o_tw o) (o_th o) 0 0 0 (o_px o)) with (fld_set (cf_flds 0 (o_tw o) (o_th o) 0 0 (o_dnaa o) (o_px o)) 12 0).
        apply (RECat_set_rdn SEGS m7 m8 cf _ 12 0 RC7); [clear; cbn; lia | clear; cbn; lia | | | exact RD8].
        - intros x Hx Hoff.
          assert (Q1 : (u (Z_to_bv 64 cf) <= u x < u (Z_to_bv 64 cf) + 88)%Z) by (clear -Hx Hcf; rewrite u_Z2bv by lia; cbn in Hx; lia).
          assert (Q2 : ~ inslot (cf + 72) x) by (clear -Hoff; unfold inslot; cbn in Hoff; lia).
          exact (POSTD_blk_byte C A8 (s - 32) (cf + 72) m7 m8 (Z_to_bv 64 cf) 88 x PD8 Lcf8 Q1 Q2).
        - intros x Hx.
          assert (Q1 : (u (Z_to_bv 64 cf) <= u x < u (Z_to_bv 64 cf) + 88)%Z) by (clear -Hx Hcf; rewrite u_Z2bv by lia; cbn in Hx; lia).
          destruct (blk_byte C A8 m8 _ (Z_to_bv 64 cf) 88 x CK HW8 Lcf8 Q1) as (_ & D & _). exact D. }
      assert (Kpix : keeps A7 A8 m7 m8 pix).
      { apply (keeps_step C A7 A8 m7 m8 _ (s - 32) (cf + 72) cf pix 88 CK HW8 PD8 Lcf8 Hcf ltac:(clear; lia) ltac:(clear; lia)); [rewrite Lpix8, Lpix; reflexivity | exact Hpix |].
        intros E. exact (live_apart A0 (o_B2 o) _ _ 64%Z S02 Lpix0 Lcf2 (f_equal (Z_to_bv 64) E)). }
      split; [apply (PIXat_frame m7 m8 pix _ PX7); destruct (Kpix 64%Z Lpix) as (_ & _ & M); exact M|].
      split; [exact Lcf8|]. split; [exact Lpix8|]. split; [exact (sub_live_trans _ _ _ SUB8 SUB7)|].
      split.
      { intros q Hq NEc NEp E8q k LAq. rewrite <- E8q in LAq.
        pose proof (SUB8 _ _ LAq) as L7q.
        assert (E78 : live A8 (Z_to_bv 64 q) = live A7 (Z_to_bv 64 q)) by (rewrite LAq, L7q; reflexivity).
        refine (keeps_trans A A7 A8 m m7 m8 q (KP7 q Hq NEc NEp ltac:(rewrite L7q, <- LAq; exact E8q)) _ k _); [| rewrite E8q in LAq; exact LAq].
        exact (keeps_step C A7 A8 m7 m8 _ (s - 32) (cf + 72) cf q 88 CK HW8 PD8 Lcf8 Hcf ltac:(clear; lia) ltac:(clear; lia) E78 Hq NEc). }
      split.
      { intros q (Xb & Xn & Xd). destruct (Xd ltac:(clear -Gpa; lia)) as (Y1 & Y2). rewrite (LEQ8 q Y1 Y2). apply NF. exact (conj Xb Xn). }
      eapply POSTM_trans; [exact PM7|]. apply (POSTM_mono C (c_A0 C) (s - 32) s); [lia|].
      apply (POSTD_POSTM_blk C (c_A0 C) A8 m8 _ (Z_to_bv 64 cf) 88 (s - 32) (cf + 72) m7 m8 CK HW8 Lcf8); [clear -Hcf; rewrite u_Z2bv by lia; lia | clear -Hcf; rewrite u_Z2bv by lia; lia | exact L0cf | exact (w_keep _ _ _ _ HW8) |].
      exact (POSTD_sub C A8 (c_A0 C) _ _ _ _ (w_keep _ _ _ _ HW8) PD8).
  Qed.

  (* [comment removed for export] *)
  Lemma J6 : forall A7 m7 vm7 r7, ST 0 0 (o_naa o) (o_dnaa o) (o_px o) NF3 A7 m7 vm7 r7 ->
    realizes SEGS (mkCfg (mkst r7 (0x17088 : word) m7 al_rom) (with_vmmaps vm7 md)) S.
  Proof.
    intros A7 m7 vm7 r7 STk. pose proof STk as (RT & HW7 & R2 & R8 & R9 & R4 & R3 & RR & CE7 & RC7 & PX7 & Lcf & Lpix & SUB7 & KP7 & NF & PM7). prep.
    pose proof CF as (RC & Lcf0 & L0cf & PX & RC2 & Halp & LpixA & L0pix & OBA & ONAA & ODNAA & OPX & S01 & S12 & S23 & S34 & S45 & S5A & Lpix0 & Fba & Fb0 & Lcf2 & Lcf3 & Fnaa & Fdnaa & Fpx).
    pose proof (sub_live_trans _ _ _ S01 S12) as S02. pose proof (sub_live_trans _ _ _ S02 S23) as S03.
    pose proof (sub_live_trans _ _ _ S03 S34) as S04. pose proof (sub_live_trans _ _ _ S04 S45) as S05.
    pose proof (sub_live_trans _ _ _ S34 S45) as S35. pose proof (sub_live_trans _ _ _ S12 S23) as S13.
    pose proof (sub_live_trans _ _ _ S13 S35) as S15. pose proof (sub_live_trans _ _ _ S13 S34) as S14. pose proof (sub_live_trans _ _ _ S23 S34) as S24.
    pose proof (RECat_range m cf _ RC) as [Wcf0 Wcf]. cbn in Wcf. pose proof PX as (Wp0 & Wp64 & _).
    assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
    assert (Hcf : (0 <= cf < 2 ^ 64)%Z) by lia. assert (Hpix : (0 <= pix < 2 ^ 64)%Z) by lia.
    destruct (cd_6 al_rom r7 m7 cf ltac:(lia) ltac:(lia) R9) as (r8 & RUN8 & U2 & U1 & U10 & U9 & U8 & AG8).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact RUN8 |].
    assert (U2' : getr r8 2 = Z_to_bv 64 (s - 32)) by (rewrite U2; exact R2).
    assert (U4 : getr r8 4 = Z_to_bv 64 0x31b70) by (csr; reflexivity).
    assert (SL : slotok C A7 (s - 32) (cf + 64) (Some (Z_to_bv 64 cf, 88%Z))).
    { cbn. rewrite u_Z2bv by lia. split; [exact Lcf|]. split; [exact L0cf|]. lia. }
    assert (RD : rdn SEGS m7 (Z_to_bv 64 (cf + 64)) 8 = Some (Z_to_le_bytes 8 (o_naa o))).
    { eapply (REC_rd' SEGS _ _ (cf_flds 0 (o_tw o) (o_th o) 0 (o_naa o) (o_dnaa o) (o_px o)) 11 8); [exact RC7 | clear; cbn; lia | reflexivity | reflexivity | reflexivity]. }
    destruct ONAA as [Hz0 | [PTA Harr0]].
    - rewrite Hz0 in RD.
      apply (numaaDestroy_null_W C A7 m7 _ r8 (s - 32) (cf + 64) (Some (Z_to_bv 64 cf, 88%Z)) (Z_to_bv 64 0x17090) S CK HW7 U2'
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(lia) ltac:(lia) U1 ltac:(red; apply bv_eq; reflexivity) U10 SL (ALcfk 64 eq_refl) RD).
      intros m8 r9 HW8 CS8 PM8. replace (Z_to_bv 64 0x17090) with (0x17090 : word) by (apply bv_eq; reflexivity).
      apply (J7 A7 m8 vm7 r9). rewrite Hz0 in STk.
      apply (ST_null 0 0 0 (o_dnaa o) (o_px o) NF3 NF6 A7 m7 vm7 r7 m8 r9 0 STk); [intros q (X1 & _); exact X1 | exact HW8 | exact PM8 |].
      exists r8. split; [exact U2|]. split; [exact U9|]. split; [exact U8|]. split; [exact AG8 | exact CS8].
    - pose proof PTA as (RP & LpaA & L0pa & ARR).
      pose proof (RECat_range m _ _ RP) as [Wpa0 Wpa]. cbn in Wpa. pose proof (PTRA_wf m _ 1 0 _ RP) as (_ & _ & Warr & _).
      destruct (blk_range C A m md (Z_to_bv 64 (o_naa o)) 16 CK HWe LpaA ltac:(lia)) as [Gpa _]. rewrite u_Z2bv in Gpa by lia.
      assert (H1 : (0 <= o_naa o < 2 ^ 64)%Z) by lia.
      destruct (Fnaa ltac:(lia)) as (F1 & F2 & _).
      assert (NQ : forall y : Z, live (o_B3 o) (Z_to_bv 64 y) = None -> (0 <= y < 2 ^ 64)%Z -> y <> cf /\ y <> pix /\ NF3 (Z_to_bv 64 y)).
      { intros y Fy Hy. split; [intros ->; exact (live_apart (o_B3 o) (o_B3 o) _ _ 88%Z (sub_live_refl _) Lcf3 Fy eq_refl)|].
        split; [intros ->; exact (live_apart A0 (o_B3 o) _ _ 64%Z S03 Lpix0 Fy eq_refl)|].
        intros NZ. destruct (Fba NZ) as (_ & _ & Xa & Xr).
        split; [exact (not_eq_sym (live_apart (o_B1 o) (o_B3 o) _ _ _ S13 Xa Fy))|].
        split; [exact (not_eq_sym (live_apart (o_B1 o) (o_B3 o) _ _ _ S13 Xr Fy))|].
        intros Hnb. destruct (Fb0 NZ Hnb) as [_ Xb]. exact (not_eq_sym (live_apart (o_B2 o) (o_B3 o) _ _ _ S23 Xb Fy)). }
      destruct (NQ _ F1 H1) as (Nc1 & Np1 & Nf1). destruct (NQ _ F2 Warr) as (Nc2 & Np2 & Nf2).
      assert (PTA7 : ptra_at C A7 m7 (o_naa o) 1 (o_narr o)).
      { exact (ptra_at_transport C A A7 m m7 _ 1 _ PTA (KP7 _ H1 Nc1 Np1 (NF _ Nf1)) (KP7 _ Warr Nc2 Np2 (NF _ Nf2))). }
      apply (numaaDestroy_W C A7 m7 _ r8 (s - 32) (cf + 64) (o_naa o) 1 (o_narr o) (Some (Z_to_bv 64 cf, 88%Z)) (Z_to_bv 64 0x17090) S
               CK HW7 U2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) U1 ltac:(red; apply bv_eq; reflexivity) U4 U10 SL (ALcfk 64 eq_refl) RD Z0 PTA7).
      { intros p k E. injection E as <- <-.
        split; [exact (zneq_w cf _ Hcf H1 (not_eq_sym Nc1)) | exact (zneq_w cf _ Hcf Warr (not_eq_sym Nc2))]. }
      intros A8 m8 vm8 r9 HW8 CS8 L1 L2 LEQ8 SUB8 PD8 RD8 HRT8. rewrite with_vmmaps_twice in HW8. rewrite with_vmmaps_twice.
      replace (Z_to_bv 64 0x17090) with (0x17090 : word) by (apply bv_eq; reflexivity).
      assert (E8 : forall q : Z, (0 <= q < 2 ^ 64)%Z -> q <> o_naa o -> q <> o_narr o -> live A8 (Z_to_bv 64 q) = live A7 (Z_to_bv 64 q)).
      { intros q Hq X1 X2. apply LEQ8; [exact (zneq_w q _ Hq H1 X1) | exact (zneq_w q _ Hq Warr X2)]. }
      assert (Lcf8 : live A8 (Z_to_bv 64 cf) = Some 88%Z) by (rewrite (E8 cf Hcf (not_eq_sym Nc1) (not_eq_sym Nc2)); exact Lcf).
      assert (Lpix8 : live A8 (Z_to_bv 64 pix) = Some 64%Z) by (rewrite (E8 pix Hpix (not_eq_sym Np1) (not_eq_sym Np2)); exact Lpix).
      apply (J7 A8 m8 vm8 r9). split; [exact (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT (roomtr_wv _ _ _ _ _ _ _ HRT8) ltac:(lia) ltac:(lia))|]. split; [exact HW8|].
      split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|].
      split; [intros r Hr; transitivity (getr r7 r); [| exact (RR r Hr)]; cbn in Hr; repeat (destruct Hr as [<-|Hr]; [csr; reflexivity|]); destruct Hr|].
      split; [unfold cd_cells; apply (cellsZ_pd3 C A8 (s - 32) (cf + 64) m7 m8); [exact CK | exact PD8 | lia | | exact CE7]|].
      { destruct (blk_range C A7 m7 _ (Z_to_bv 64 cf) 88 CK HW7 Lcf ltac:(lia)) as [_ TOPc]. rewrite u_Z2bv in TOPc by lia. clear -HsR TOPc T1 Hlo PIN7. forall_cells. }
      split.
      { change (cf_flds 0 (o_tw o) (o_th o) 0 0 (o_dnaa o) (o_px o)) with (fld_set (cf_flds 0 (o_tw o) (o_th o) 0 (o_naa o) (o_dnaa o) (o_px o)) 11 0).
        apply (RECat_set_rdn SEGS m7 m8 cf _ 11 0 RC7); [clear; cbn; lia | clear; cbn; lia | | | exact RD8].
        - intros x Hx Hoff.
          assert (Q1 : (u (Z_to_bv 64 cf) <= u x < u (Z_to_bv 64 cf) + 88)%Z) by (clear -Hx Hcf; rewrite u_Z2bv by lia; cbn in Hx; lia).
          assert (Q2 : ~ inslot (cf + 64) x) by (clear -Hoff; unfold inslot; cbn in Hoff; lia).
          exact (POSTD_blk_byte C A8 (s - 32) (cf + 64) m7 m8 (Z_to_bv 64 cf) 88 x PD8 Lcf8 Q1 Q2).
        - intros x Hx.
          assert (Q1 : (u (Z_to_bv 64 cf) <= u x < u (Z_to_bv 64 cf) + 88)%Z) by (clear -Hx Hcf; rewrite u_Z2bv by lia; cbn in Hx; lia).
          destruct (blk_byte C A8 m8 _ (Z_to_bv 64 cf) 88 x CK HW8 Lcf8 Q1) as (_ & D & _). exact D. }
      assert (Kpix : keeps A7 A8 m7 m8 pix).
      { apply (keeps_step C A7 A8 m7 m8 _ (s - 32) (cf + 64) cf pix 88 CK HW8 PD8 Lcf8 Hcf ltac:(clear; lia) ltac:(clear; lia)); [rewrite Lpix8, Lpix; reflexivity | exact Hpix |].
        intros E. exact (live_apart A0 (o_B2 o) _ _ 64%Z S02 Lpix0 Lcf2 (f_equal (Z_to_bv 64) E)). }
      split; [apply (PIXat_frame m7 m8 pix _ PX7); destruct (Kpix 64%Z Lpix) as (_ & _ & M); exact M|].
      split; [exact Lcf8|]. split; [exact Lpix8|]. split; [exact (sub_live_trans _ _ _ SUB8 SUB7)|].
      split.
      { intros q Hq NEc NEp E8q k LAq. rewrite <- E8q in LAq.
        pose proof (SUB8 _ _ LAq) as L7q.
        assert (E78 : live A8 (Z_to_bv 64 q) = live A7 (Z_to_bv 64 q)) by (rewrite LAq, L7q; reflexivity).
        refine (keeps_trans A A7 A8 m m7 m8 q (KP7 q Hq NEc NEp ltac:(rewrite L7q, <- LAq; exact E8q)) _ k _); [| rewrite E8q in LAq; exact LAq].
        exact (keeps_step C A7 A8 m7 m8 _ (s - 32) (cf + 64) cf q 88 CK HW8 PD8 Lcf8 Hcf ltac:(clear; lia) ltac:(clear; lia) E78 Hq NEc). }
      split.
      { intros q (Xb & Xn). destruct (Xn ltac:(clear -Gpa; lia)) as (Y1 & Y2). rewrite (LEQ8 q Y1 Y2). apply NF. exact Xb. }
      eapply POSTM_trans; [exact PM7|]. apply (POSTM_mono C (c_A0 C) (s - 32) s); [lia|].
      apply (POSTD_POSTM_blk C (c_A0 C) A8 m8 _ (Z_to_bv 64 cf) 88 (s - 32) (cf + 64) m7 m8 CK HW8 Lcf8); [clear -Hcf; rewrite u_Z2bv by lia; lia | clear -Hcf; rewrite u_Z2bv by lia; lia | exact L0cf | exact (w_keep _ _ _ _ HW8) |].
      exact (POSTD_sub C A8 (c_A0 C) _ _ _ _ (w_keep _ _ _ _ HW8) PD8).
  Qed.

  (* [comment removed for export] *)
  Lemma J5 : forall A7 m7 vm7 r7, ST 0 0 (o_naa o) (o_dnaa o) (o_px o) NF3 A7 m7 vm7 r7 ->
    realizes SEGS (mkCfg (mkst r7 (0x17080 : word) m7 al_rom) (with_vmmaps vm7 md)) S.
  Proof.
    intros A7 m7 vm7 r7 STk. pose proof STk as (RT & HW7 & R2 & R8 & R9 & R4 & R3 & RR & CE7 & RC7 & PX7 & Lcf & Lpix & SUB7 & KP7 & NF & PM7). prep.
    pose proof CF as (RC & Lcf0 & L0cf & PX & _).
    pose proof (RECat_range m cf _ RC) as [Wcf0 Wcf]. cbn in Wcf.
    assert (Hcf : (0 <= cf < 2 ^ 64)%Z) by lia.
    destruct (cd_5 al_rom r7 m7 cf ltac:(lia) ltac:(lia) R9) as (r8 & RUN8 & U2 & U1 & U10 & U9 & U8 & AG8).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact RUN8 |].
    assert (U2' : getr r8 2 = Z_to_bv 64 (s - 32)) by (rewrite U2; exact R2).
    assert (SL : slotok C A7 (s - 32) (cf + 56) (Some (Z_to_bv 64 cf, 88%Z))).
    { cbn. rewrite u_Z2bv by lia. split; [exact Lcf|]. split; [exact L0cf|]. lia. }
    assert (RD : rdn SEGS m7 (Z_to_bv 64 (cf + 56)) 8 = Some (Z_to_le_bytes 8 0)).
    { eapply (REC_rd' SEGS _ _ (cf_flds 0 (o_tw o) (o_th o) 0 (o_naa o) (o_dnaa o) (o_px o)) 10 8); [exact RC7 | clear; cbn; lia | reflexivity | reflexivity | reflexivity]. }
    apply (pixaDestroy_null_W C A7 m7 _ r8 (s - 32) (cf + 56) (Some (Z_to_bv 64 cf, 88%Z)) (Z_to_bv 64 0x17088) S CK HW7 U2'
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(lia) ltac:(lia) U1 ltac:(red; apply bv_eq; reflexivity) U10 SL (ALcfk 56 eq_refl) RD).
    intros m8 r9 HW8 CS8 PM8. replace (Z_to_bv 64 0x17088) with (0x17088 : word) by (apply bv_eq; reflexivity).
    apply (J6 A7 m8 vm7 r9).
    apply (ST_null 0 0 (o_naa o) (o_dnaa o) (o_px o) NF3 NF3 A7 m7 vm7 r7 m8 r9 0 STk); [intros q X; exact X | exact HW8 | exact PM8 |].
    exists r8. split; [exact U2|]. split; [exact U9|]. split; [exact U8|]. split; [exact AG8 | exact CS8].
  Qed.

  (* [comment removed for export] *)
  Lemma J4 : forall A7 m7 vm7 r7, ST 0 0 (o_naa o) (o_dnaa o) (o_px o) NF3 A7 m7 vm7 r7 ->
    realizes SEGS (mkCfg (mkst r7 (0x17078 : word) m7 al_rom) (with_vmmaps vm7 md)) S.
  Proof.
    intros A7 m7 vm7 r7 STk. pose proof STk as (RT & HW7 & R2 & R8 & R9 & R4 & R3 & RR & CE7 & RC7 & PX7 & Lcf & Lpix & SUB7 & KP7 & NF & PM7). prep.
    pose proof CF as (RC & Lcf0 & L0cf & PX & _).
    pose proof (RECat_range m cf _ RC) as [Wcf0 Wcf]. cbn in Wcf.
    assert (Hcf : (0 <= cf < 2 ^ 64)%Z) by lia.
    destruct (cd_4 al_rom r7 m7 cf ltac:(lia) ltac:(lia) R9) as (r8 & RUN8 & U2 & U1 & U10 & U9 & U8 & AG8).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact RUN8 |].
    assert (U2' : getr r8 2 = Z_to_bv 64 (s - 32)) by (rewrite U2; exact R2).
    assert (SL : slotok C A7 (s - 32) (cf + 48) (Some (Z_to_bv 64 cf, 88%Z))).
    { cbn. rewrite u_Z2bv by lia. split; [exact Lcf|]. split; [exact L0cf|]. lia. }
    assert (RD : rdn SEGS m7 (Z_to_bv 64 (cf + 48)) 8 = Some (Z_to_le_bytes 8 0)).
    { eapply (REC_rd' SEGS _ _ (cf_flds 0 (o_tw o) (o_th o) 0 (o_naa o) (o_dnaa o) (o_px o)) 9 8); [exact RC7 | clear; cbn; lia | reflexivity | reflexivity | reflexivity]. }
    apply (pixaDestroy_null_W C A7 m7 _ r8 (s - 32) (cf + 48) (Some (Z_to_bv 64 cf, 88%Z)) (Z_to_bv 64 0x17080) S CK HW7 U2'
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(lia) ltac:(lia) U1 ltac:(red; apply bv_eq; reflexivity) U10 SL (ALcfk 48 eq_refl) RD).
    intros m8 r9 HW8 CS8 PM8. replace (Z_to_bv 64 0x17080) with (0x17080 : word) by (apply bv_eq; reflexivity).
    apply (J5 A7 m8 vm7 r9).
    apply (ST_null 0 0 (o_naa o) (o_dnaa o) (o_px o) NF3 NF3 A7 m7 vm7 r7 m8 r9 0 STk); [intros q X; exact X | exact HW8 | exact PM8 |].
    exists r8. split; [exact U2|]. split; [exact U9|]. split; [exact U8|]. split; [exact AG8 | exact CS8].
  Qed.

  (* [comment removed for export] *)
  Lemma J3 : forall A7 m7 vm7 r7, ST 0 (o_ba o) (o_naa o) (o_dnaa o) (o_px o) NF1 A7 m7 vm7 r7 ->
    realizes SEGS (mkCfg (mkst r7 (0x17070 : word) m7 al_rom) (with_vmmaps vm7 md)) S.
  Proof.
    intros A7 m7 vm7 r7 STk. pose proof STk as (RT & HW7 & R2 & R8 & R9 & R4 & R3 & RR & CE7 & RC7 & PX7 & Lcf & Lpix & SUB7 & KP7 & NF & PM7). prep.
    pose proof CF as (RC & Lcf0 & L0cf & PX & RC2 & Halp & LpixA & L0pix & OBA & ONAA & ODNAA & OPX & S01 & S12 & S23 & S34 & S45 & S5A & Lpix0 & Fba & Fb0 & Lcf2 & Lcf3 & Fnaa & Fdnaa & Fpx).
    pose proof (sub_live_trans _ _ _ S01 S12) as S02.
    pose proof (RECat_range m cf _ RC) as [Wcf0 Wcf]. cbn in Wcf. pose proof PX as (Wp0 & Wp64 & _).
    assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
    assert (Hcf : (0 <= cf < 2 ^ 64)%Z) by lia. assert (Hpix : (0 <= pix < 2 ^ 64)%Z) by lia.
    destruct (cd_3 al_rom r7 m7 cf ltac:(lia) ltac:(lia) R9) as (r8 & RUN8 & U2 & U1 & U10 & U9 & U8 & AG8).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact RUN8 |].
    assert (U2' : getr r8 2 = Z_to_bv 64 (s - 32)) by (rewrite U2; exact R2).
    assert (U4 : getr r8 4 = Z_to_bv 64 0x31b70) by (csr; reflexivity).
    assert (SL : slotok C A7 (s - 32) (cf + 40) (Some (Z_to_bv 64 cf, 88%Z))).
    { cbn. rewrite u_Z2bv by lia. split; [exact Lcf|]. split; [exact L0cf|]. lia. }
    assert (RD : rdn SEGS m7 (Z_to_bv 64 (cf + 40)) 8 = Some (Z_to_le_bytes 8 (o_ba o))).
    { eapply (REC_rd' SEGS _ _ (cf_flds 0 (o_tw o) (o_th o) (o_ba o) (o_naa o) (o_dnaa o) (o_px o)) 8 8); [exact RC7 | clear; cbn; lia | reflexivity | reflexivity | reflexivity]. }
    destruct OBA as [Hz0 | (BXA & Hbarr0 & Hnb)].
    - rewrite Hz0 in RD.
      apply (boxaDestroy_null_W C A7 m7 _ r8 (s - 32) (cf + 40) (Some (Z_to_bv 64 cf, 88%Z)) (Z_to_bv 64 0x17078) S CK HW7 U2'
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(lia) ltac:(lia) U1 ltac:(red; apply bv_eq; reflexivity) U10 SL (ALcfk 40 eq_refl) RD).
      intros m8 r9 HW8 CS8 PM8. replace (Z_to_bv 64 0x17078) with (0x17078 : word) by (apply bv_eq; reflexivity).
      apply (J4 A7 m8 vm7 r9). rewrite Hz0 in STk.
      apply (ST_null 0 0 (o_naa o) (o_dnaa o) (o_px o) NF1 NF3 A7 m7 vm7 r7 m8 r9 0 STk); [intros q _; exact I | exact HW8 | exact PM8 |].
      exists r8. split; [exact U2|]. split; [exact U9|]. split; [exact U8|]. split; [exact AG8 | exact CS8].
    - pose proof BXA as (RB & Halb & LbaA & L0ba & ARR).
      pose proof (RECat_range m _ _ RB) as [Wba0 Wba]. cbn in Wba. pose proof (BOXA_wf m _ _ 1 1 _ RB) as (_ & _ & Wbarr & _).
      destruct (blk_range C A m md (Z_to_bv 64 (o_ba o)) 24 CK HWe LbaA ltac:(lia)) as [Gba _]. rewrite u_Z2bv in Gba by lia.
      assert (H1 : (0 <= o_ba o < 2 ^ 64)%Z) by lia.
      destruct (Fba ltac:(lia)) as (F1 & F2 & G1 & G2).
      (* [comment removed for export] *)
      assert (NQ : forall (y : Z) k, live A0 (Z_to_bv 64 y) = None -> live (o_B1 o) (Z_to_bv 64 y) = Some k -> (0 <= y < 2 ^ 64)%Z -> y <> cf /\ y <> pix).
      { intros y k Fy Gy Hy. split; [intros ->; exact (live_apart (o_B1 o) (o_B2 o) _ _ k S12 Gy Lcf2 eq_refl)|].
        intros ->. rewrite Lpix0 in Fy. discriminate Fy. }
      destruct (NQ _ _ F1 G1 H1) as [Nc1 Np1]. destruct (NQ _ _ F2 G2 Wbarr) as [Nc2 Np2].
      assert (NB0 : o_nb o = 1%Z -> (0 <= o_b0 o < 2 ^ 64)%Z /\ o_b0 o <> cf /\ o_b0 o <> pix).
      { intros Hnb1. destruct (Fb0 ltac:(lia) Hnb1) as [Fb Gb].
        destruct ARR as [[_ Hn0] | (_ & _ & _ & _ & [Hn0 | (_ & _ & (BX & _) & _)])]; [lia | lia |].
        destruct BX as (bx & byy & bw & bh & RX). pose proof (RECat_range m _ _ RX) as [X0 X1]. cbn in X1.
        split; [lia|]. split; [intros E; rewrite E in Gb; exact (live_apart (o_B2 o) (o_B2 o) _ _ _ (sub_live_refl _) Gb Lcf2 eq_refl)|].
        intros E. rewrite E in Fb. pose proof (S01 _ _ Lpix0). congruence. }
      assert (BXA7 : boxa_at C A7 m7 (o_ba o) (o_nb o) 1 (o_barr o) (o_b0 o)).
      { apply (boxa_at_transport C A A7 m m7 _ _ 1 _ _ BXA (KP7 _ H1 Nc1 Np1 (NF _ I)) (KP7 _ Wbarr Nc2 Np2 (NF _ I))).
        intros Hnb1. destruct (NB0 Hnb1) as (Hb0 & Ncb & Npb). exact (KP7 _ Hb0 Ncb Npb (NF _ I)). }
      apply (boxaDestroy_W C A7 m7 _ r8 (s - 32) (cf + 40) (o_ba o) (o_nb o) 1 (o_barr o) (o_b0 o) (Some (Z_to_bv 64 cf, 88%Z)) (Z_to_bv 64 0x17078) S
               CK HW7 U2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) U1 ltac:(red; apply bv_eq; reflexivity) U4 U10 SL (ALcfk 40 eq_refl) RD Z0 BXA7).
      { intros p k E. injection E as <- <-.
        split; [exact (zneq_w cf _ Hcf H1 (not_eq_sym Nc1))|]. split; [exact (zneq_w cf _ Hcf Wbarr (not_eq_sym Nc2))|].
        intros Hnb1. destruct (NB0 Hnb1) as (Hb0 & Ncb & _). exact (zneq_w cf _ Hcf Hb0 (not_eq_sym Ncb)). }
      intros A8 m8 vm8 r9 HW8 CS8 L1 L2 L3 LEQ8 SUB8 PD8 RD8 HRT8. rewrite with_vmmaps_twice in HW8. rewrite with_vmmaps_twice.
      replace (Z_to_bv 64 0x17078) with (0x17078 : word) by (apply bv_eq; reflexivity).
      assert (E8 : forall q : Z, (0 <= q < 2 ^ 64)%Z -> q <> o_ba o -> q <> o_barr o -> (o_nb o = 1%Z -> q <> o_b0 o) -> live A8 (Z_to_bv 64 q) = live A7 (Z_to_bv 64 q)).
      { intros q Hq X1 X2 X3. apply LEQ8; [exact (zneq_w q _ Hq H1 X1) | exact (zneq_w q _ Hq Wbarr X2) |].
        intros Hnb1. destruct (NB0 Hnb1) as (Hb0 & _). exact (zneq_w q _ Hq Hb0 (X3 Hnb1)). }
      assert (Lcf8 : live A8 (Z_to_bv 64 cf) = Some 88%Z).
      { rewrite (E8 cf Hcf (not_eq_sym Nc1) (not_eq_sym Nc2)); [exact Lcf|]. intros Hnb1. destruct (NB0 Hnb1) as (_ & Ncb & _). exact (not_eq_sym Ncb). }
      assert (Lpix8 : live A8 (Z_to_bv 64 pix) = Some 64%Z).
      { rewrite (E8 pix Hpix (not_eq_sym Np1) (not_eq_sym Np2)); [exact Lpix|]. intros Hnb1. destruct (NB0 Hnb1) as (_ & _ & Npb). exact (not_eq_sym Npb). }
      apply (J4 A8 m8 vm8 r9). split; [exact (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT (roomtr_wv _ _ _ _ _ _ _ HRT8) ltac:(lia) ltac:(lia))|]. split; [exact HW8|].
      split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|].
      split; [intros r Hr; transitivity (getr r7 r); [| exact (RR r Hr)]; cbn in Hr; repeat (destruct Hr as [<-|Hr]; [csr; reflexivity|]); destruct Hr|].
      split; [unfold cd_cells; apply (cellsZ_pd3 C A8 (s - 32) (cf + 40) m7 m8); [exact CK | exact PD8 | lia | | exact CE7]|].
      { destruct (blk_range C A7 m7 _ (Z_to_bv 64 cf) 88 CK HW7 Lcf ltac:(lia)) as [_ TOPc]. rewrite u_Z2bv in TOPc by lia. clear -HsR TOPc T1 Hlo PIN7. forall_cells. }
      split.
      { change (cf_flds 0 (o_tw o) (o_th o) 0 (o_naa o) (o_dnaa o) (o_px o)) with (fld_set (cf_flds 0 (o_tw o) (o_th o) (o_ba o) (o_naa o) (o_dnaa o) (o_px o)) 8 0).
        apply (RECat_set_rdn SEGS m7 m8 cf _ 8 0 RC7); [clear; cbn; lia | clear; cbn; lia | | | exact RD8].
        - intros x Hx Hoff.
          assert (Q1 : (u (Z_to_bv 64 cf) <= u x < u (Z_to_bv 64 cf) + 88)%Z) by (clear -Hx Hcf; rewrite u_Z2bv by lia; cbn in Hx; lia).
          assert (Q2 : ~ inslot (cf + 40) x) by (clear -Hoff; unfold inslot; cbn in Hoff; lia).
          exact (POSTD_blk_byte C A8 (s - 32) (cf + 40) m7 m8 (Z_to_bv 64 cf) 88 x PD8 Lcf8 Q1 Q2).
        - intros x Hx.
          assert (Q1 : (u (Z_to_bv 64 cf) <= u x < u (Z_to_bv 64 cf) + 88)%Z) by (clear -Hx Hcf; rewrite u_Z2bv by lia; cbn in Hx; lia).
          destruct (blk_byte C A8 m8 _ (Z_to_bv 64 cf) 88 x CK HW8 Lcf8 Q1) as (_ & D & _). exact D. }
      assert (Kpix : keeps A7 A8 m7 m8 pix).
      { apply (keeps_step C A7 A8 m7 m8 _ (s - 32) (cf + 40) cf pix 88 CK HW8 PD8 Lcf8 Hcf ltac:(clear; lia) ltac:(clear; lia)); [rewrite Lpix8, Lpix; reflexivity | exact Hpix |].
        intros E. exact (live_apart A0 (o_B2 o) _ _ 64%Z S02 Lpix0 Lcf2 (f_equal (Z_to_bv 64) E)). }
      split; [apply (PIXat_frame m7 m8 pix _ PX7); destruct (Kpix 64%Z Lpix) as (_ & _ & M); exact M|].
      split; [exact Lcf8|]. split; [exact Lpix8|]. split; [exact (sub_live_trans _ _ _ SUB8 SUB7)|].
      split.
      { intros q Hq NEc NEp E8q k LAq. rewrite <- E8q in LAq.
        pose proof (SUB8 _ _ LAq) as L7q.
        assert (E78 : live A8 (Z_to_bv 64 q) = live A7 (Z_to_bv 64 q)) by (rewrite LAq, L7q; reflexivity).
        refine (keeps_trans A A7 A8 m m7 m8 q (KP7 q Hq NEc NEp ltac:(rewrite L7q, <- LAq; exact E8q)) _ k _); [| rewrite E8q in LAq; exact LAq].
        exact (keeps_step C A7 A8 m7 m8 _ (s - 32) (cf + 40) cf q 88 CK HW8 PD8 Lcf8 Hcf ltac:(clear; lia) ltac:(clear; lia) E78 Hq NEc). }
      split.
      { intros q Xb. destruct (Xb ltac:(clear -Gba; lia)) as (Y1 & Y2 & Y3). rewrite (LEQ8 q Y1 Y2 Y3). apply NF. exact I. }
      eapply POSTM_trans; [exact PM7|]. apply (POSTM_mono C (c_A0 C) (s - 32) s); [lia|].
      apply (POSTD_POSTM_blk C (c_A0 C) A8 m8 _ (Z_to_bv 64 cf) 88 (s - 32) (cf + 40) m7 m8 CK HW8 Lcf8); [clear -Hcf; rewrite u_Z2bv by lia; lia | clear -Hcf; rewrite u_Z2bv by lia; lia | exact L0cf | exact (w_keep _ _ _ _ HW8) |].
      exact (POSTD_sub C A8 (c_A0 C) _ _ _ _ (w_keep _ _ _ _ HW8) PD8).
  Qed.


  (* [comment removed for export] *)
  Lemma J2 : forall A7 m7 vm7 r7, ST 0 (o_ba o) (o_naa o) (o_dnaa o) (o_px o) NF1 A7 m7 vm7 r7 ->
    realizes SEGS (mkCfg (mkst r7 (0x17068 : word) m7 al_rom) (with_vmmaps vm7 md)) S.
  Proof.
    intros A7 m7 vm7 r7 STk. pose proof STk as (RT & HW7 & R2 & R8 & R9 & R4 & R3 & RR & CE7 & RC7 & PX7 & Lcf & Lpix & SUB7 & KP7 & NF & PM7). prep.
    pose proof CF as (RC & Lcf0 & L0cf & PX & _).
    pose proof (RECat_range m cf _ RC) as [Wcf0 Wcf]. cbn in Wcf.
    assert (Hcf : (0 <= cf < 2 ^ 64)%Z) by lia.
    destruct (cd_2 al_rom r7 m7 cf ltac:(lia) ltac:(lia) R9) as (r8 & RUN8 & U2 & U1 & U10 & U9 & U8 & AG8).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact RUN8 |].
    assert (U2' : getr r8 2 = Z_to_bv 64 (s - 32)) by (rewrite U2; exact R2).
    assert (SL : slotok C A7 (s - 32) (cf + 8) (Some (Z_to_bv 64 cf, 88%Z))).
    { cbn. rewrite u_Z2bv by lia. split; [exact Lcf|]. split; [exact L0cf|]. lia. }
    assert (RD : rdn SEGS m7 (Z_to_bv 64 (cf + 8)) 8 = Some (Z_to_le_bytes 8 0)).
    { eapply (REC_rd' SEGS _ _ (cf_flds 0 (o_tw o) (o_th o) (o_ba o) (o_naa o) (o_dnaa o) (o_px o)) 1 8); [exact RC7 | clear; cbn; lia | reflexivity | reflexivity | reflexivity]. }
    apply (pixDestroy_null_W C A7 m7 _ r8 (s - 32) (cf + 8) (Some (Z_to_bv 64 cf, 88%Z)) (Z_to_bv 64 0x17070) S CK HW7 U2'
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(lia) ltac:(lia) U1 ltac:(red; apply bv_eq; reflexivity) U10 SL (ALcfk 8 eq_refl) RD).
    intros m8 r9 HW8 CS8 PM8 _. replace (Z_to_bv 64 0x17070) with (0x17070 : word) by (apply bv_eq; reflexivity).
    apply (J3 A7 m8 vm7 r9).
    apply (ST_null 0 (o_ba o) (o_naa o) (o_dnaa o) (o_px o) NF1 NF1 A7 m7 vm7 r7 m8 r9 0 STk); [intros q X; exact X | exact HW8 | exact PM8 |].
    exists r8. split; [exact U2|]. split; [exact U9|]. split; [exact U8|]. split; [exact AG8 | exact CS8].
  Qed.

  (* [comment removed for export] *)
  Lemma l_colorfillDestroy_main : getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 cf) ->
    realizes SEGS (mkCfg (mkst regs (0x17030 : word) m al_rom) md) S.
  Proof.
    intros H1 H10 Rpp. prep.
    pose proof CF as (RC & Lcf0 & L0cf & PX & RC2 & Halp & LpixA & L0pix & OBA & ONAA & ODNAA & OPX & S01 & S12 & S23 & S34 & S45 & S5A & Lpix0 & Fba & Fb0 & Lcf2 & Lcf3 & _).
    pose proof (sub_live_trans _ _ _ S01 S12) as S02.
    pose proof (RECat_range m cf _ RC) as [Wcf0 Wcf]. cbn in Wcf. pose proof PX as (Wp0 & Wp64 & _).
    assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
    assert (Hcf : (0 <= cf < 2 ^ 64)%Z) by lia. assert (Hpix : (0 <= pix < 2 ^ 64)%Z) by lia.
    destruct (blk_range C A m md (Z_to_bv 64 cf) 88 CK HWe Lcf0 ltac:(lia)) as [Gcf TOPcf]. rewrite u_Z2bv in Gcf, TOPcf by lia.
    destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HWe LpixA ltac:(lia)) as [Gpix TOPpix]. rewrite u_Z2bv in Gpix, TOPpix by lia.
    assert (NEcp : cf <> pix) by (intros E; exact (live_apart A0 (o_B2 o) _ _ 64%Z S02 Lpix0 Lcf2 (eq_sym (f_equal (Z_to_bv 64) E)))).
    pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HWe) Lcf0 LpixA (zneq_w cf pix Hcf Hpix NEcp)) as Dcp.
    rewrite !u_Z2bv in Dcp by lia. change (round16 88) with 96%Z in Dcp. change (round16 64) with 64%Z in Dcp.
    (* [comment removed for export] *)
    assert (ALcf : (cf mod 8 = 0)%Z).
    { pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HWe) Lcf0) as (_ & AL16 & _). rewrite u_Z2bv in AL16 by lia. exact (mod16_mod8 _ AL16). }
    destruct (cd_A al_rom regs m s pp cf ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALpp
                (W_sok_win C A m md (s - 32) 32 CK HWe ltac:(lia) ltac:(cbn; lia)) Rpp ltac:(lia) H2 H1 H10)
      as (r1 & RUN1 & Q2 & Q8 & Q9 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWe)) | exact (mp_lazy _ (w_pure _ _ _ _ HWe)) | exact RUN1 |].
    assert (WP0 : W C A (cdF m s ret regs) md /\ POSTM C (c_A0 C) s m (cdF m s ret regs)).
    { unfold cdF. do 3 (apply (WP_win C A (c_A0 C) m _ _ _ _ s CK); [| exact (W_sub0 _ _ _ _ HWe) | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia]).
      split; [exact HWe | apply POSTM_refl]. }
    destruct WP0 as [HW0 PM0].
    assert (RC0 : RECat (cdF m s ret regs) cf (cf_flds pix (o_tw o) (o_th o) (o_ba o) (o_naa o) (o_dnaa o) (o_px o))).
    { apply (RECat_frame m _ cf _ RC). intros x Hx. cbn in Hx. apply cdF_out; lia. }
    assert (PX0 : PIXat (cdF m s ret regs) pix v).
    { apply (PIXat_frame m _ pix v PX). intros x Hx. apply cdF_out; lia. }
    destruct (cd_1 al_rom r1 (cdF m s ret regs) cf ltac:(lia) ltac:(lia) ALcf Q9) as (r2 & RUN2 & U2 & U1 & U10 & U9 & U8 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN2 |].
    assert (U2' : getr r2 2 = Z_to_bv 64 (s - 32)) by (rewrite U2; exact Q2).
    assert (SL : slotok C A (s - 32) cf (Some (Z_to_bv 64 cf, 88%Z))).
    { cbn. rewrite u_Z2bv by lia. split; [exact Lcf0|]. split; [exact L0cf|]. lia. }
    assert (RD : rdn SEGS (cdF m s ret regs) (Z_to_bv 64 cf) 8 = Some (Z_to_le_bytes 8 pix)).
    { eapply (REC_rd' SEGS _ _ (cf_flds pix (o_tw o) (o_th o) (o_ba o) (o_naa o) (o_dnaa o) (o_px o)) 0 8); [exact RC0 | clear; cbn; lia | reflexivity | cbn [fld_off cf_flds Z.of_nat]; f_equal; clear; lia | reflexivity]. }
    apply (pixDestroy_dec_W C A (cdF m s ret regs) md r2 (s - 32) cf pix v (Some (Z_to_bv 64 cf, 88%Z)) (Z_to_bv 64 0x17068) S CK HW0 U2'
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(lia) ltac:(lia) U1 ltac:(red; apply bv_eq; reflexivity) U10 SL ALcf RD PX0 RC2 LpixA L0pix).
    { intros p k E. injection E as <- <-. exact (zneq_w cf pix Hcf Hpix NEcp). }
    intros m1 r3 HW1 CS1 PX1 RD1 AG MG. replace (Z_to_bv 64 0x17068) with (0x17068 : word) by (apply bv_eq; reflexivity).
    rewrite <- (with_vmmaps_same md). apply (J2 A m1 (m_vmmaps md) r3).
    split; [apply roomtr_refl; lia|]. split; [rewrite with_vmmaps_same; exact HW1|].
    split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [csr; reflexivity|].
    split; [intros r Hr; cbn in Hr; repeat (destruct Hr as [<-|Hr]; [csr; reflexivity|]); destruct Hr|].
    split.
    { unfold cd_cells. apply (cellsZ_keep (cdF m s ret regs) m1); [| exact (cdF_cells m s ret regs ltac:(lia) ltac:(lia))].
      clear -HsR TOPpix TOPcf T1 Hlo PIN7 AG.
      repeat (apply Forall_cons; [cbn [fst snd]; split; [lia|]; split; [lia|]; intros x Hx; apply AG; [lia | lia | unfold inslot; lia] |]). apply Forall_nil. }
    split.
    { change (cf_flds 0 (o_tw o) (o_th o) (o_ba o) (o_naa o) (o_dnaa o) (o_px o)) with (fld_set (cf_flds pix (o_tw o) (o_th o) (o_ba o) (o_naa o) (o_dnaa o) (o_px o)) 0 0).
      apply (RECat_set_rdn SEGS (cdF m s ret regs) m1 cf _ 0 0 RC0); [clear; cbn; lia | clear; cbn; lia | | |].
      - intros x Hx Hoff. cbn [flds_len cf_flds fld_off fld_get fst Nat.add] in Hx, Hoff.
        apply AG; [clear -Hx TOPcf T1 Hlo PIN7; lia | clear -Hx Dcp; lia | clear -Hoff; unfold inslot; lia].
      - intros x Hx.
        assert (Q1 : (u (Z_to_bv 64 cf) <= u x < u (Z_to_bv 64 cf) + 88)%Z) by (clear -Hx Hcf; rewrite u_Z2bv by lia; cbn in Hx; lia).
        destruct (blk_byte C A m1 _ (Z_to_bv 64 cf) 88 x CK HW1 Lcf0 Q1) as (_ & D & _). exact D.
      - cbn [fld_off fld_get cf_flds fst Z.of_nat Nat.add]. replace (o_cf o + Z.of_nat 0)%Z with (o_cf o) by (clear; lia). exact RD1. }
    split; [exact PX1|].
    split; [exact Lcf0|]. split; [exact LpixA|]. split; [apply sub_live_refl|].
    split.
    { intros q Hq NEc NEp _. apply (keeps_agree C A A m m1 md q HW1 eq_refl Hq). intros k x L Hx.
      destruct (blk_range C A m md (Z_to_bv 64 q) k CK HWe L ltac:(destruct (Z_lt_le_dec 0 k); [lia | exfalso; clear -Hx l; lia])) as [Gq TOPq]. rewrite u_Z2bv in Gq, TOPq by lia.
      pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HWe) L LpixA (zneq_w q pix Hq Hpix NEp)) as D1.
      pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HWe) L Lcf0 (zneq_w q cf Hq Hcf NEc)) as D2.
      pose proof (round16_ge k ltac:(clear -Hx; lia)) as RG.
      rewrite !u_Z2bv in D1, D2 by lia. change (round16 88) with 96%Z in D2. change (round16 64) with 64%Z in D1.
      rewrite AG; [apply cdF_out; clear -Hx TOPq T1 Hlo PIN7 HsR; lia | clear -Hx TOPq T1 Hlo PIN7; lia | clear -Hx D1 RG; lia | clear -Hx D2 RG; unfold inslot; lia]. }
    split; [intros q _; reflexivity|].
    eapply POSTM_trans; [exact PM0|].
    apply (POSTM_local C (c_A0 C) A (cdF m s ret regs) md m1 s CK HW0 (W_sub0 _ _ _ _ HWe)).
    intros a Ha. destruct (Z_lt_le_dec (u a) (s - 64)) as [Blo|Bhi]; [| destruct (Z_lt_le_dec (u a) (s - 32)) as [Bmid|Bhi2]; [left; unfold scratch; lia|]].
    - (* [comment removed for export] *)
      right. destruct (Sumbool.sumbool_and _ _ _ _ (Z_le_dec (pix + 20) (u a)) (Z_lt_dec (u a) (pix + 24))) as [[P1 P2] | P].
      + exists (Z_to_bv 64 pix), 64%Z. split; [exact LpixA|]. split; [exact L0pix|]. rewrite u_Z2bv by lia. lia.
      + destruct (Sumbool.sumbool_and _ _ _ _ (Z_le_dec cf (u a)) (Z_lt_dec (u a) (cf + 8))) as [[C1 C2] | Cn].
        * exists (Z_to_bv 64 cf), 88%Z. split; [exact Lcf0|]. split; [exact L0cf|]. rewrite u_Z2bv by lia. lia.
        * exfalso. apply Ha. apply AG; [lia | lia | unfold inslot; lia].
    - exfalso. apply Ha. apply AG; [lia | lia | unfold inslot; lia].
  Qed.
End Walk.

(* [comment removed for export] *)
Theorem l_colorfillDestroy_null_W : forall C A m md regs (s pp : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pp -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> (pp mod 8 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x17030 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 Hpp Hpphi ALpp Rpp HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU8] in *.
  destruct (cd_A al_rom regs m s pp 0 ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALpp
              (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp ltac:(lia) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (cdF m s ret regs) md /\ POSTM C A s m (cdF m s ret regs)) by (unfold cdF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact (cd_Z al_rom r1 _ Q9) |].
  destruct (cd_epi al_rom r1 (cdF m s ret regs) s ret regs ltac:(lia) ltac:(lia) Hret (cdF_cells m s ret regs ltac:(lia) ltac:(lia)) Q2)
    as (r6 & RUN6 & V2 & V1 & V8 & V9 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN6 |].
  apply (HK _ r6 HW1); [| exact PM1].
  apply cs_kept_intro; rewrite ?V2, ?V8, ?V9, ?H2; try reflexivity.
  all: rewrite (AG6 _) by notin_lit; rewrite (AG1 _) by notin_lit; reflexivity.
Qed.
End CfDestroy.
