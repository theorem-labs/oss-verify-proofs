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
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptBilSegs.
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

Ltac ncv_tac :=
  ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; bw_norm;
  lazymatch goal with |- ext_val false 0 4 (Z_to_bv 64 ?X) = Z_to_bv 64 (nc_val ?mn ?mx ?i) =>
    let EQ := fresh "EQ" in
    assert (EQ : X = nc_val mn mx i)
      by (unfold nc_val; first [ lazymatch goal with |- (Z.quot ?a 9 + ?b = ?d + Z.quot ?c 9)%Z => replace a with c by lia; lia end
                               | (rewrite Z.mul_0_r, Z.quot_0_l by lia; lia) | lia ]);
    rewrite <- EQ; rewrite ext_val_zx_id by (rewrite u_Z2bv by lia; ex_pow2; lia); reflexivity
  end.
Ltac bcellV HK Hlf regs rb rk tacV :=
  let N := fresh "C" in
  lazymatch goal with
  | |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some (Z_to_le_bytes ?n ?z) =>
      exB_cell HK Hlf rb rk n a z N ltac:(exb_scs regs) ltac:(exB_tacA idtac) tacV; exact N
  end.
Ltac bcellE HK Hlf regs rb rk :=
  let N := fresh "C" in
  lazymatch goal with
  | |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some (Z_to_le_bytes ?n ?z) =>
      exB_cell HK Hlf rb rk n a z N ltac:(exb_scs regs) ltac:(exB_tacA ltac:(rewrite ?alu_add, ?m_mul, ?zbv_mul, ?zbv_add))
        ltac:(exB_tacV idtac); exact N
  end.
Ltac fr_lit := apply fr_get_lit; vm_compute; reflexivity.
Ltac sltu1 := rewrite v_sltu_Z by lia;
  lazymatch goal with |- context [(0 <? ?b)%Z] => replace (0 <? b)%Z with true by (symmetry; apply Z.ltb_lt; lia) end;
  first [ reflexivity | (vm_compute; reflexivity) ].
Ltac bcell HK Hlf regs rb rk :=
  let N := fresh "C" in
  lazymatch goal with
  | |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some (Z_to_le_bytes ?n ?z) =>
      exB_cell HK Hlf rb rk n a z N ltac:(exb_scs regs) ltac:(exB_tacA idtac) ltac:(exB_tacV idtac); exact N
  end.

Lemma bc_E : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s pixs bsc bil minv maxv : Z),
  frm_zero cs ->
  (4096 + 320 <= s <= 2 ^ 47)%Z ->
  (4096 <= pixs)%Z ->
  (pixs + 64 <= s - 320)%Z ->
  (pixs mod 16 = 0)%Z ->
  (0 <= bsc < 2 ^ 64)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 320)%Z ->
  (bil mod 16 = 0)%Z ->
  (bil + 104 <= pixs \/ pixs + 64 <= bil)%Z ->
  (0 <= minv <= 255)%Z ->
  (0 <= maxv <= 255)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 148)) 4 = Some (Z_to_le_bytes 4 minv) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 4 = Some (Z_to_le_bytes 4 maxv) ->
  rdn SEGS m (Z_to_bv 64 (s - 296)) 8 = Some (Z_to_le_bytes 8 bsc) ->
  rdn SEGS m (Z_to_bv 64 (s - 288)) 8 = Some (Z_to_le_bytes 8 10) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
  store_ok SEGS m (Z_to_bv 64 bil) 104 = true ->
  store_ok SEGS m (Z_to_bv 64 (pixs + 20)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 304)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  getr regs 10 = Z_to_bv 64 bil ->
  getr regs 9 = Z_to_bv 64 bsc ->
  getr regs 22 = Z_to_bv 64 1 ->
  getr regs 24 = Z_to_bv 64 pixs ->
  reg_get fr 8 = Z_to_bv 64 0xffffffff41200000 ->
  reg_get fr 9 = Z_to_bv 64 0xffffffff40a00000 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x39a18) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x3c0f8) M' rom /\ frm_zero cs' /\
      rinv [(bil, 104%Z); ((pixs + 20)%Z, 4%Z); ((s - 304)%Z, 8%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 bil) 8 = Some (Z_to_le_bytes 8 pixs) /\ rdn SEGS M' (Z_to_bv 64 (bil + 8)) 8 = Some (Z_to_le_bytes 8 bsc) /\
      rdn SEGS M' (Z_to_bv 64 (bil + 16)) 4 = Some (Z_to_le_bytes 4 1) /\ rdn SEGS M' (Z_to_bv 64 (bil + 48)) 4 = Some (Z_to_le_bytes 4 minv) /\
      rdn SEGS M' (Z_to_bv 64 (bil + 52)) 4 = Some (Z_to_le_bytes 4 maxv) /\ rdn SEGS M' (Z_to_bv 64 (bil + 56)) 4 = Some (Z_to_le_bytes 4 10) /\
      rdn SEGS M' (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) /\ rdn SEGS M' (Z_to_bv 64 (s - 304)) 8 = Some (Z_to_le_bytes 8 bil) /\
      getr regs' 1 = Z_to_bv 64 0x39a74 /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 10 = Z_to_bv 64 10 /\ getr regs' 11 = Z_to_bv 64 4 /\
      getr regs' 8 = Z_to_bv 64 bil /\ getr regs' 9 = Z_to_bv 64 10 /\
      regs_agree (fun r => In r [1; 8; 9; 10; 11; 12]%list) regs regs' /\
      (forall r : reg, reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s pixs bsc bil minv maxv FZ Hs Hp1 Hp2 ALp Hb Hl1 Hl2 ALl APlp Hmin Hmax Cmin Cmax Cbsc Cnc Crc SOKl SOKr SOKf
    H2 H10 H9 H22 H24 F8 F9.
  ex_entry regs [(s - 320)%Z; bil; pixs; bsc; minv; maxv; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 320)%Z; bil; pixs; bsc; minv; maxv; bv_unsigned (reg_get fr 8); bv_unsigned (reg_get fr 9)]) m
     [KRange (EVar 32) 4096 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KRange (EVar 34) 4096 (2 ^ 47);
      KRange (EVar 35) 0 (2 ^ 64 - 1); KRange (EVar 36) 0 255; KRange (EVar 37) 0 255;
      KAlign (EVar 33) 16; KAlign (EVar 34) 16;
      KWr (SA (EVar 33) 0) 104; KWr (SA (EVar 34) 20) 4; KWr (SA (EVar 32) 16) 8;
      KWord (SA (EVar 32) 172) 4 (EVar 36); KWord (SA (EVar 32) 168) 4 (EVar 37);
      KWord (SA (EVar 32) 24) 8 (EVar 35); KWord (SA (EVar 32) 32) 8 (ELit 10);
      KWord (SA (EVar 34) 20) 4 (ELit 1);
      KDisj (SA (EVar 33) 0) 104 (SA (EVar 32) 0) 320; KDisj (SA (EVar 34) 0) 64 (SA (EVar 32) 0) 320;
      KDisj (SA (EVar 33) 0) 104 (SA (EVar 34) 0) 64]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adrive 4%nat 400%nat [0x3c0f8%Z] [(8%nat, 38%nat); (9%nat, 39%nat)] HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 4 eexists; split; [reflexivity|].
  split; [exact FZ|].
  split; [exB_rinv_tac Hlf [(bil, 104%Z); ((pixs + 20)%Z, 4%Z); ((s - 304)%Z, 8%Z)]; exB_reg_tac idtac|].
  split; [bcell HK Hlf regs (EVar 33) 0%Z|]. split; [bcell HK Hlf regs (EVar 33) 8%Z|].
  split; [bcell HK Hlf regs (EVar 33) 16%Z|]. split; [bcell HK Hlf regs (EVar 33) 48%Z|].
  split; [bcell HK Hlf regs (EVar 33) 52%Z|]. split; [bcell HK Hlf regs (EVar 33) 56%Z|].
  split; [bcell HK Hlf regs (EVar 34) 20%Z|]. split; [bcell HK Hlf regs (EVar 32) 16%Z|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR' | ex_agree HR HR' | (intros r; apply fr_kept; cbn; tauto) ].
Qed.


#[local] Ltac exB_sc_hook ::= bw_hook.
Lemma bc_F : forall (fx : FPState) regs (m : word -> option byte) (s bil nc minv maxv : Z),
  (4096 + 320 <= s <= 2 ^ 47)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 320)%Z ->
  (4096 <= nc)%Z ->
  (nc + 40 <= s - 320)%Z ->
  (nc mod 16 = 0)%Z ->
  (bil + 104 <= nc \/ nc + 40 <= bil)%Z ->
  (0 <= minv <= 255)%Z ->
  (0 <= maxv <= 255)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 148)) 4 = Some (Z_to_le_bytes 4 minv) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 4 = Some (Z_to_le_bytes 4 maxv) ->
  rdn SEGS m (Z_to_bv 64 (s - 304)) 8 = Some (Z_to_le_bytes 8 bil) ->
  store_ok SEGS m (Z_to_bv 64 nc) 40 = true ->
  store_ok SEGS m (Z_to_bv 64 (bil + 64)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 248)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  getr regs 10 = Z_to_bv 64 nc ->
  getr regs 9 = Z_to_bv 64 10 ->
  frm_zero (@fp_csr fx) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x39a74) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x3c0f8) M' rom /\
      rinv [(nc, 40%Z); ((bil + 64)%Z, 8%Z); ((s - 248)%Z, 8%Z)] m M' /\
      (forall j, (0 <= j < 10)%Z -> rdn SEGS M' (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) /\
      rdn SEGS M' (Z_to_bv 64 (bil + 64)) 8 = Some (Z_to_le_bytes 8 nc) /\ rdn SEGS M' (Z_to_bv 64 (s - 248)) 8 = Some (Z_to_le_bytes 8 nc) /\
      getr regs' 1 = Z_to_bv 64 0x39b14 /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 10 = Z_to_bv 64 256 /\ getr regs' 11 = Z_to_bv 64 4 /\
      getr regs' 8 = Z_to_bv 64 9 /\ getr regs' 9 = Z_to_bv 64 nc /\
      regs_agree (fun r => In r [1; 5; 8; 9; 10; 11; 12; 14; 15; 16; 17]%list) regs regs').
Proof.
  intros fx regs m s bil nc minv maxv Hs Hb1 Hb2 Hn1 Hn2 ALn APbn Hmin Hmax Cmin Cmax Cbil SOKn SOKb SOKf H2 H10 H9 FZ.
  ex_entry regs [(s - 320)%Z; bil; nc; minv; maxv] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 320)%Z; bil; nc; minv; maxv]) m
     [KRange (EVar 32) 4096 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KRange (EVar 34) 4096 (2 ^ 47);
      KRange (EVar 35) 0 255; KRange (EVar 36) 0 255; KAlign (EVar 34) 16;
      KWr (SA (EVar 34) 0) 40; KWr (SA (EVar 33) 64) 8; KWr (SA (EVar 32) 72) 8;
      KWord (SA (EVar 32) 172) 4 (EVar 35); KWord (SA (EVar 32) 168) 4 (EVar 36); KWord (SA (EVar 32) 16) 8 (EVar 33);
      KDisj (SA (EVar 34) 0) 40 (SA (EVar 32) 0) 320; KDisj (SA (EVar 33) 0) 104 (SA (EVar 32) 0) 320;
      KDisj (SA (EVar 33) 0) 104 (SA (EVar 34) 0) 40]) by (ex_know regs).
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  exb_open HR HK ST.
  exb_adriveS 8%nat 2000%nat [0x3c0f8%Z] (SCR (repeat false 60) [] []) (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [(nc, 40%Z); ((bil + 64)%Z, 8%Z); ((s - 248)%Z, 8%Z)]; exB_reg_tac idtac|].
  split.
  { intros j Hj. pose proof (nc_val_rng minv maxv j Hmin Hmax ltac:(lia)) as NV.
    assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9)%Z as JJ by lia.
    destruct JJ as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]];
      cbn [Z.mul Pos.mul] in *;
      lazymatch goal with |- rdn _ _ (Z_to_bv 64 (_ + ?k)) _ = _ => bcellV HK Hlf regs (EVar 34) k ltac:(ncv_tac) end. }
  split; [bcell HK Hlf regs (EVar 33) 64%Z|]. split; [bcell HK Hlf regs (EVar 32) 72%Z|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR' | ex_agree HR HR' ].
Qed.

Lemma bc_G2 : forall (fx : FPState) regs (m : word -> option byte) (s bil kx maxv : Z),
  (4096 + 320 <= s <= 2 ^ 47)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 320)%Z ->
  (4096 <= kx)%Z ->
  (kx + 1024 <= s - 320)%Z ->
  (kx mod 16 = 0)%Z ->
  (bil + 104 <= kx \/ kx + 1024 <= bil)%Z ->
  (0 <= maxv <= 255)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 288)) 8 = Some (Z_to_le_bytes 8 10) ->
  rdn SEGS m (Z_to_bv 64 (s - 304)) 8 = Some (Z_to_le_bytes 8 bil) ->
  store_ok SEGS m (Z_to_bv 64 kx) 1024 = true ->
  store_ok SEGS m (Z_to_bv 64 (bil + 72)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  getr regs 10 = Z_to_bv 64 kx ->
  getr regs 16 = Z_to_bv 64 maxv ->
  frm_zero (@fp_csr fx) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x39bd4) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x3c0f8) M' rom /\
      rinv [((kx + 4 * maxv)%Z, 4%Z); ((bil + 72)%Z, 8%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (kx + 4 * maxv)) 4 = Some (Z_to_le_bytes 4 8) /\ rdn SEGS M' (Z_to_bv 64 (bil + 72)) 8 = Some (Z_to_le_bytes 8 kx) /\
      getr regs' 1 = Z_to_bv 64 0x39c28 /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 10 = Z_to_bv 64 256 /\ getr regs' 11 = Z_to_bv 64 4 /\
      regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs').
Proof.
  intros fx regs m s bil kx maxv Hs Hb1 Hb2 Hk1 Hk2 ALk APbk Hmax Cnc Cbil SOKk SOKb H2 H10 H16 FZ.
  ex_entry regs [(s - 320)%Z; bil; kx; maxv] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 320)%Z; bil; kx; maxv]) m
     [KRange (EVar 32) 4096 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KRange (EVar 34) 4096 (2 ^ 47);
      KRange (EVar 35) 0 255; KAlign (EVar 34) 16;
      KWr (SA (EVar 34) 0) 1024; KWr (SA (EVar 33) 72) 8;
      KWord (SA (EVar 32) 32) 8 (ELit 10); KWord (SA (EVar 32) 16) 8 (EVar 33);
      KDisj (SA (EVar 34) 0) 1024 (SA (EVar 32) 0) 320; KDisj (SA (EVar 33) 0) 104 (SA (EVar 32) 0) 320;
      KDisj (SA (EVar 33) 0) 104 (SA (EVar 34) 0) 1024]) by (ex_know regs).
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  exb_open HR HK ST.
  exb_adriveS 8%nat 400%nat [0x3c0f8%Z] (SCR (repeat false 8) [] []) (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((kx + 4 * maxv)%Z, 4%Z); ((bil + 72)%Z, 8%Z)]; exB_reg_tac ltac:(rewrite ?alu_add, ?m_mul, ?zbv_mul, ?zbv_add)|].
  split; [bcellE HK Hlf regs (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) 0%Z|].
  split; [bcell HK Hlf regs (EVar 33) 72%Z|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR' | ex_agree HR HR' ].
Qed.

Lemma bc_H2 : forall (fx : FPState) regs (m : word -> option byte) (s bil kf maxv : Z),
  (4096 + 320 <= s <= 2 ^ 47)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 320)%Z ->
  (4096 <= kf)%Z ->
  (kf + 1024 <= s - 320)%Z ->
  (kf mod 16 = 0)%Z ->
  (bil + 104 <= kf \/ kf + 1024 <= bil)%Z ->
  (0 <= maxv <= 255)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 304)) 8 = Some (Z_to_le_bytes 8 bil) ->
  store_ok SEGS m (Z_to_bv 64 kf) 1024 = true ->
  store_ok SEGS m (Z_to_bv 64 (bil + 80)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  getr regs 10 = Z_to_bv 64 kf ->
  getr regs 11 = Z_to_bv 64 maxv ->
  getr regs 28 = Z_to_bv 64 11 ->
  frm_zero (@fp_csr fx) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x39d98) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x3c0f8) M' rom /\
      rinv [((kf + 4 * maxv)%Z, 4%Z); ((bil + 80)%Z, 8%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (kf + 4 * maxv)) 4 = Some (Z_to_le_bytes 4 0x3f800000) /\ rdn SEGS M' (Z_to_bv 64 (bil + 80)) 8 = Some (Z_to_le_bytes 8 kf) /\
      getr regs' 1 = Z_to_bv 64 0x39de8 /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 10 = Z_to_bv 64 11 /\ getr regs' 11 = Z_to_bv 64 4 /\
      regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs').
Proof.
  intros fx regs m s bil kf maxv Hs Hb1 Hb2 Hk1 Hk2 ALk APbk Hmax Cbil SOKk SOKb H2 H10 H11 H28 FZ.
  ex_entry regs [(s - 320)%Z; bil; kf; maxv] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 320)%Z; bil; kf; maxv]) m
     [KRange (EVar 32) 4096 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KRange (EVar 34) 4096 (2 ^ 47);
      KRange (EVar 35) 0 255; KAlign (EVar 34) 16;
      KWr (SA (EVar 34) 0) 1024; KWr (SA (EVar 33) 80) 8; KWord (SA (EVar 32) 16) 8 (EVar 33);
      KDisj (SA (EVar 34) 0) 1024 (SA (EVar 32) 0) 320; KDisj (SA (EVar 33) 0) 104 (SA (EVar 32) 0) 320;
      KDisj (SA (EVar 33) 0) 104 (SA (EVar 34) 0) 1024]) by (ex_know regs).
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  exb_open HR HK ST.
  exb_adriveS 8%nat 400%nat [0x3c0f8%Z] (SCR (repeat false 8) [] []) (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((kf + 4 * maxv)%Z, 4%Z); ((bil + 80)%Z, 8%Z)]; exB_reg_tac ltac:(rewrite ?alu_add, ?m_mul, ?zbv_mul, ?zbv_add)|].
  split; [bcellE HK Hlf regs (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 35))) 0%Z|].
  split; [bcell HK Hlf regs (EVar 33) 80%Z|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR' | ex_agree HR HR' ].
Qed.

Lemma bc_I : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s spat : Z),
  frm_zero cs ->
  (4096 + 320 <= s <= 2 ^ 47)%Z ->
  (4096 <= spat)%Z ->
  (spat + 44 <= 2 ^ 47)%Z ->
  (spat mod 16 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 272)) 8 = Some (Z_to_le_bytes 8 11) ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  getr regs 10 = Z_to_bv 64 spat ->
  reg_get fr 9 = Z_to_bv 64 0xffffffff40a00000 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x39de8) m rom)
    (fun fin => exists fr' cs' regs', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x39e20) m rom /\ frm_zero cs' /\
      getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 8 = Z_to_bv 64 0 /\ getr regs' 9 = Z_to_bv 64 1 /\ getr regs' 18 = Z_to_bv 64 11 /\
      getr regs' 19 = Z_to_bv 64 spat /\ getr regs' 20 = Z_to_bv 64 1 /\ getr regs' 21 = Z_to_bv 64 spat /\ getr regs' 23 = Z_to_bv 64 spat /\
      regs_agree (fun r => In r [8; 9; 10; 18; 19; 20; 21; 23]%list) regs regs' /\
      reg_get fr' 9 = Z_to_bv 64 0xffffffff42480000 /\ reg_get fr' 18 = Z_to_bv 64 0x4024000000000000 /\
      (forall r : reg, ~ In (ridx r) [9; 15; 18]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s spat FZ Hs Hp1 Hp2 ALp C11 H2 H10 F9.
  ex_entry regs [(s - 320)%Z; spat] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 320)%Z; spat]) m
     [KRange (EVar 32) 4096 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 16;
      KWord (SA (EVar 32) 48) 8 (ELit 11)]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adriveS 8%nat 400%nat [0x39e20%Z] (SCR (repeat false 8) [] []) (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 3 eexists; split; [reflexivity|].
  split; [assumption|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR' | ex_agree HR HR' | fr_lit | exB_fr_kept ].
  all: sltu1.
Qed.

Lemma bc_J : forall (fx : FPState) regs (m : word -> option byte) (s bil spat : Z),
  (4096 + 320 <= s <= 2 ^ 47)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 320)%Z ->
  (0 <= spat < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 304)) 8 = Some (Z_to_le_bytes 8 bil) ->
  store_ok SEGS m (Z_to_bv 64 (bil + 32)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  getr regs 21 = Z_to_bv 64 spat ->
  frm_zero (@fp_csr fx) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x39e68) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x3c0f8) M' rom /\
      rinv [((bil + 32)%Z, 8%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (bil + 32)) 8 = Some (Z_to_le_bytes 8 spat) /\
      getr regs' 1 = Z_to_bv 64 0x39e80 /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 10 = Z_to_bv 64 256 /\ getr regs' 11 = Z_to_bv 64 4 /\
      getr regs' 8 = Z_to_bv 64 256 /\ regs_agree (fun r => In r [1; 8; 10; 11]%list) regs regs').
Proof.
  intros fx regs m s bil spat Hs Hb1 Hb2 Hsp Cbil SOKb H2 H21 FZ.
  ex_entry regs [(s - 320)%Z; bil; spat] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 320)%Z; bil; spat]) m
     [KRange (EVar 32) 4096 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47);
      KWr (SA (EVar 33) 32) 8; KWord (SA (EVar 32) 16) 8 (EVar 33);
      KDisj (SA (EVar 33) 0) 104 (SA (EVar 32) 0) 320]) by (ex_know regs).
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  exb_open HR HK ST.
  exb_adriveS 8%nat 400%nat [0x3c0f8%Z] (SCR (repeat false 8) [] []) (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((bil + 32)%Z, 8%Z)]; exB_reg_tac idtac|].
  split; [bcell HK Hlf regs (EVar 33) 32%Z|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR' | ex_agree HR HR' ].
Qed.

Lemma bc_K : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s rng : Z),
  frm_zero cs ->
  (4096 + 320 <= s <= 2 ^ 47)%Z ->
  (4096 <= rng)%Z ->
  (rng + 1024 <= 2 ^ 47)%Z ->
  (rng mod 16 = 0)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  getr regs 10 = Z_to_bv 64 rng ->
  getr regs 8 = Z_to_bv 64 256 ->
  reg_get fr 8 = Z_to_bv 64 0xffffffff41200000 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x39e80) m rom)
    (fun fin => exists fr' cs' regs', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x39eb0) m rom /\ frm_zero cs' /\
      getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 8 = Z_to_bv 64 256 /\ getr regs' 9 = Z_to_bv 64 0 /\ getr regs' 18 = Z_to_bv 64 1 /\
      getr regs' 19 = Z_to_bv 64 1 /\ getr regs' 23 = Z_to_bv 64 rng /\ getr regs' 25 = Z_to_bv 64 rng /\ getr regs' 26 = Z_to_bv 64 rng /\
      regs_agree (fun r => In r [9; 10; 18; 19; 23; 25; 26]%list) regs regs' /\
      reg_get fr' 8 = Z_to_bv 64 0xffffffff43480000 /\
      (forall r : reg, ~ In (ridx r) [8; 14; 15]%nat -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s rng FZ Hs Hr1 Hr2 ALr H2 H10 H8 F8.
  ex_entry regs [(s - 320)%Z; rng] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 320)%Z; rng]) m
     [KRange (EVar 32) 4096 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 16]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adriveS 8%nat 400%nat [0x39eb0%Z] (SCR (repeat false 8) [] []) (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 3 eexists; split; [reflexivity|].
  split; [assumption|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR' | ex_agree HR HR' | fr_lit | exB_fr_kept ].
  all: sltu1.
Qed.

Lemma bc_L : forall (fx : FPState) regs (m : word -> option byte) (s bil rng : Z),
  (4096 + 320 <= s <= 2 ^ 47)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 320)%Z ->
  (0 <= rng < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 304)) 8 = Some (Z_to_le_bytes 8 bil) ->
  rdn SEGS m (Z_to_bv 64 (s - 288)) 8 = Some (Z_to_le_bytes 8 10) ->
  store_ok SEGS m (Z_to_bv 64 (bil + 40)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 320) ->
  getr regs 23 = Z_to_bv 64 rng ->
  frm_zero (@fp_csr fx) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x39eec) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x18258) M' rom /\
      rinv [((bil + 40)%Z, 8%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (bil + 40)) 8 = Some (Z_to_le_bytes 8 rng) /\
      getr regs' 1 = Z_to_bv 64 0x39efc /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 10 = Z_to_bv 64 10 /\
      regs_agree (fun r => In r [1; 10]%list) regs regs').
Proof.
  intros fx regs m s bil rng Hs Hb1 Hb2 Hr Cbil Cnc SOKb H2 H23 FZ.
  ex_entry regs [(s - 320)%Z; bil; rng] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 320)%Z; bil; rng]) m
     [KRange (EVar 32) 4096 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47);
      KWr (SA (EVar 33) 40) 8; KWord (SA (EVar 32) 16) 8 (EVar 33); KWord (SA (EVar 32) 32) 8 (ELit 10);
      KDisj (SA (EVar 33) 0) 104 (SA (EVar 32) 0) 320]) by (ex_know regs).
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  exb_open HR HK ST.
  exb_adriveS 8%nat 400%nat [0x18258%Z] (SCR (repeat false 8) [] []) (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eexists; split; [exact Hms|].
  do 2 eexists; split; [reflexivity|].
  split; [exB_rinv_tac Hlf [((bil + 40)%Z, 8%Z)]; exB_reg_tac idtac|].
  split; [bcell HK Hlf regs (EVar 33) 40%Z|].
  repeat match goal with |- _ /\ _ => split end.
  all: first [ ex_reg regs HR' | ex_agree HR HR' ].
Qed.

End Segs.
