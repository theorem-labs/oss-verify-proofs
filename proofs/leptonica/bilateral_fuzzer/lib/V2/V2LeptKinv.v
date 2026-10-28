(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib LeptExecB LeptEdgeFP.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import FpBound FpReal.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptErr V2LeptCmap2 V2LeptKernCreateS V2LeptKernCreateS1 V2LeptKernDestroyS V2LeptKinvSegs V2LeptBl3_iface V2LeptKvals V2KernUb V2LeptKobjLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomK LeptRoomBL LeptRop2Arith LeptRgbLib.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section KinvW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition f15_only (fr fr' : bvmap 5 word) : Prop := forall r : reg, r <> 15%bv -> reg_get fr' r = reg_get fr r.
Lemma f15_only_refl : forall fr, f15_only fr fr.
Proof. intros fr r _. reflexivity. Qed.
Lemma f15_only_set : forall fr fr' v, f15_only fr fr' -> f15_only fr (bvmap_set 15 v fr').
Proof.
  intros fr fr' v H r Hr. unfold reg_get at 1.
  rewrite bvmap_get_set_other by (intros E; apply Hr; first [exact E | symmetry; exact E]). exact (H r Hr).
Qed.
Lemma f15_only_trans : forall fr1 fr2 fr3, f15_only fr1 fr2 -> f15_only fr2 fr3 -> f15_only fr1 fr3.
Proof. intros fr1 fr2 fr3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
Lemma f15_only_fs : forall fr fr', f15_only fr fr' -> forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r.
Proof.
  intros fr fr' H r Hr. apply H. intros ->. vm_compute in Hr. intuition discriminate.
Qed.

Definition kcp (bs : list byte) : list byte := Z_to_le_bytes 4 (u (low32 (nan_box (bv_extract 0 32 (le_bytes_to_word bs))))).
Lemma kcp_val : forall z, (0 <= z < 2 ^ 32)%Z -> kcp (Z_to_le_bytes 4 z) = Z_to_le_bytes 4 z.
Proof.
  intros z Hz. unfold kcp. rewrite fpv_low32_box, fpv_cell_load by lia.
  rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | unfold bv_modulus; lia].
Qed.

Lemma kc_col : forall (k : nat) fr cs regs M (sx j a7 rs keld arrd i rd : Z),
  (1 <= sx < 2 ^ 31)%Z -> (0 <= j < sx)%Z -> Z.of_nat k = (sx - j)%Z ->
  (0 <= a7)%Z -> (a7 + 8 < 2 ^ 64)%Z -> (1 <= rs)%Z -> (rs + 4 * sx < 2 ^ 64)%Z -> (rs mod 4 = 0)%Z ->
  (0 <= keld)%Z -> (keld + 24 < 2 ^ 64)%Z -> (1 <= arrd)%Z -> (0 <= i < 2 ^ 31)%Z -> (arrd + 8 * i + 8 < 2 ^ 64)%Z -> (arrd mod 8 = 0)%Z ->
  (1 <= rd)%Z -> (rd + 4 * sx < 2 ^ 64)%Z -> (rd mod 4 = 0)%Z ->
  (rs + 4 * sx <= rd \/ rd + 4 * sx <= rs)%Z -> (a7 + 8 <= rd \/ rd + 4 * sx <= a7)%Z ->
  (keld + 24 <= rd \/ rd + 4 * sx <= keld + 16)%Z -> (arrd + 8 * i + 8 <= rd \/ rd + 4 * sx <= arrd + 8 * i)%Z ->
  rdn SEGS M (Z_to_bv 64 a7) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 rs)) ->
  rdn SEGS M (Z_to_bv 64 (keld + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arrd)) ->
  rdn SEGS M (Z_to_bv 64 (arrd + 8 * i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 rd)) ->
  (forall a, (rs <= a < rs + 4 * sx)%Z -> M (Z_to_bv 64 a) <> None) ->
  store_ok SEGS M (Z_to_bv 64 rd) (Z.to_nat (4 * sx)) = true ->
  getr regs 10 = Z_to_bv 64 keld -> getr regs 12 = Z_to_bv 64 (sx - 1) -> getr regs 14 = Z_to_bv 64 (4 * sx) -> getr regs 17 = Z_to_bv 64 a7 ->
  getr regs 6 = Z_to_bv 64 j -> getr regs 5 = Z_to_bv 64 (4 * j) -> getr regs 7 = Z_to_bv 64 (8 * i) ->
  exists fr' regs' M',
    msteps SEGS (@mkst (mkFP fr cs) regs (0x38f58 : word) M al_rom) (@mkst (mkFP fr' cs) regs' (0x39004 : word) M' al_rom)
    /\ winside (rd + 4 * j) (rd + 4 * sx) M M' /\ f15_only fr fr'
    /\ (forall q bs, (j <= q < sx)%Z -> rdn SEGS M (Z_to_bv 64 (rs + 4 * (sx - 1 - q))) 4 = Some bs ->
          rdn SEGS M' (Z_to_bv 64 (rd + 4 * q)) 4 = Some (kcp bs))
    /\ regs_agree (fun x => In x [5; 6; 18; 28; 29; 30; 31]%list) regs regs'.
Proof.
  induction k as [| k IH];
    intros fr cs regs M sx j a7 rs keld arrd i rd Hsx Hj Hk Ha7 Ha7b Hrs Hrsb ALs Hkd Hkdb Had Hi Hadb ALa Hrd Hrdb ALd
      Ds D7 Dk Da R7 Rk Ra DEF SOK H10 H12 H14 H17 H6 H5 H7; [lia |].
  destruct (OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica.PFLib.rdn_defined SEGS M (rs + 4 * (sx - 1 - j))%Z 4%nat
              ltac:(lia) ltac:(lia) ltac:(intros t Ht; apply DEF; lia)) as (bs0 & Rz & Lz).
  assert (SOKj : store_ok SEGS M (Z_to_bv 64 (rd + 4 * j)) 4 = true).
  { apply (store_ok_sub SEGS M (Z_to_bv 64 rd) _ (Z.to_nat (4 * sx)) 4%nat);
      [rewrite u_Z2bv, Z2Nat.id by lia; lia | exact SOK | rewrite !u_Z2bv by lia; lia | rewrite !u_Z2bv, Z2Nat.id by lia; lia]. }
  assert (WI1 : winside (rd + 4 * j) (rd + 4 * j + 4) M (wbytes M (Z_to_bv 64 (rd + 4 * j)) (kcp bs0))).
  { apply winside_one; unfold kcp; rewrite ?length_Z_to_le_bytes, ?u_Z2bv by lia; lia. }
  assert (HIT : rdn SEGS (wbytes M (Z_to_bv 64 (rd + 4 * j)) (kcp bs0)) (Z_to_bv 64 (rd + 4 * j)) 4 = Some (kcp bs0)).
  { assert (X := OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.SeqExec.rdn_wbytes_hit SEGS (kcp bs0) M (Z_to_bv 64 (rd + 4 * j))
                   ltac:(unfold kcp; rewrite length_Z_to_le_bytes, u_Z2bv by lia; lia)).
    unfold kcp in X |- *. rewrite length_Z_to_le_bytes in X. exact X. }
  assert (K : forall (a : Z) (n : nat) bs, (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z -> (rd + 4 * j + 4 <= a \/ a + Z.of_nat n <= rd + 4 * j)%Z ->
                rdn SEGS M (Z_to_bv 64 a) n = Some bs -> rdn SEGS (wbytes M (Z_to_bv 64 (rd + 4 * j)) (kcp bs0)) (Z_to_bv 64 a) n = Some bs).
  { intros a n bs Ha Han Hd R. exact (winside_rdn SEGS _ _ M _ a n bs WI1 ltac:(lia) Ha Han Hd R). }
  destruct (Z.eq_dec (j + 1) sx) as [Last | NL].
  - destruct (ki_I al_rom true fr cs regs M sx j a7 rs keld arrd i rd bs0 Hsx Hj Last Ha7 Ha7b Hrs Hrsb ALs
                Hkd Hkdb Had Hi Hadb ALa Hrd Hrdb ALd R7 Rk Ra Rz SOKj H10 H12 H14 H17 H6 H5 H7) as (r1 & MS & G6 & G5 & AG).
    exists (bvmap_set 15%bv (nan_box (bv_extract 0%N 32%N (le_bytes_to_word bs0))) fr), r1, (wbytes M (Z_to_bv 64 (rd + 4 * j)) (kcp bs0)).
    split; [exact MS |].
    split; [apply (winside_mono _ _ _ _ _ _ WI1); lia |].
    split; [apply f15_only_set, f15_only_refl |].
    split; [| exact AG].
    intros q bs Hq Rq. assert (Eq : q = j) by lia. subst q.
    rewrite Rz in Rq. injection Rq as <-. exact HIT.
  - destruct (ki_I al_rom false fr cs regs M sx j a7 rs keld arrd i rd bs0 Hsx Hj ltac:(cbn; lia) Ha7 Ha7b Hrs Hrsb ALs
                Hkd Hkdb Had Hi Hadb ALa Hrd Hrdb ALd R7 Rk Ra Rz SOKj H10 H12 H14 H17 H6 H5 H7) as (r1 & MS & G6 & G5 & AG).
    assert (R7' := K a7 8%nat _ ltac:(lia) ltac:(lia) ltac:(lia) R7).
    assert (Rk' := K (keld + 16)%Z 8%nat _ ltac:(lia) ltac:(lia) ltac:(lia) Rk).
    assert (Ra' := K (arrd + 8 * i)%Z 8%nat _ ltac:(lia) ltac:(lia) ltac:(lia) Ra).
    assert (DEF1 : forall a, (rs <= a < rs + 4 * sx)%Z -> wbytes M (Z_to_bv 64 (rd + 4 * j)) (kcp bs0) (Z_to_bv 64 a) <> None).
    { intros a Ha. rewrite (winside_out _ _ M _ (Z_to_bv 64 a) WI1 ltac:(lia) ltac:(rewrite u_Z2bv by lia; lia)). exact (DEF a Ha). }
    assert (SOK1 : store_ok SEGS (wbytes M (Z_to_bv 64 (rd + 4 * j)) (kcp bs0)) (Z_to_bv 64 rd) (Z.to_nat (4 * sx)) = true)
      by exact (store_ok_mono SEGS _ M _ _ (winside_grows _ _ _ _ WI1) SOK).
    assert (G10 : getr r1 10 = Z_to_bv 64 keld) by (rewrite (AG 10%bv) by (cbv; intuition discriminate); exact H10).
    assert (G12 : getr r1 12 = Z_to_bv 64 (sx - 1)) by (rewrite (AG 12%bv) by (cbv; intuition discriminate); exact H12).
    assert (G14 : getr r1 14 = Z_to_bv 64 (4 * sx)) by (rewrite (AG 14%bv) by (cbv; intuition discriminate); exact H14).
    assert (G17 : getr r1 17 = Z_to_bv 64 a7) by (rewrite (AG 17%bv) by (cbv; intuition discriminate); exact H17).
    assert (G7 : getr r1 7 = Z_to_bv 64 (8 * i)) by (rewrite (AG 7%bv) by (cbv; intuition discriminate); exact H7).
    destruct (IH (bvmap_set 15%bv (nan_box (bv_extract 0%N 32%N (le_bytes_to_word bs0))) fr) cs r1 (wbytes M (Z_to_bv 64 (rd + 4 * j)) (kcp bs0))
                sx (j + 1)%Z a7 rs keld arrd i rd Hsx ltac:(lia) ltac:(lia) Ha7 Ha7b Hrs Hrsb ALs Hkd Hkdb Had Hi Hadb ALa Hrd Hrdb ALd
                Ds D7 Dk Da R7' Rk' Ra' DEF1 SOK1 G10 G12 G14 G17 G6 G5 G7) as (fr2 & r2 & M2 & MS2 & WI2 & F2 & V2 & AG2).
    exists fr2, r2, M2.
    split; [eapply msteps_trans; [exact MS | exact MS2] |].
    split; [eapply winside_trans; [apply (winside_mono _ _ _ _ _ _ WI1); lia | apply (winside_mono _ _ _ _ _ _ WI2); lia] |].
    split; [exact (f15_only_trans _ _ _ (f15_only_set _ _ _ (f15_only_refl fr)) F2) |].
    split.
    + intros q bs Hq Rq. destruct (Z.eq_dec q j) as [-> | Ne].
      * rewrite Rz in Rq. injection Rq as <-.
        exact (winside_rdn SEGS _ _ _ M2 (rd + 4 * j)%Z 4%nat _ WI2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HIT).
      * apply (V2 q bs ltac:(lia)). exact (K (rs + 4 * (sx - 1 - q))%Z 4%nat _ ltac:(lia) ltac:(lia) ltac:(lia) Rq).
    + intros r Hr. rewrite (AG2 r Hr). exact (AG r Hr).
Qed.

(* [comment removed for export] *)
Lemma ki_col : forall (k : nat) fr cs regs M (sx j a7 rs keld arrd i rd : Z),
  (1 <= sx < 2 ^ 31)%Z -> (0 <= j < sx)%Z -> Z.of_nat k = (sx - j)%Z ->
  (0 <= a7)%Z -> (a7 + 8 < 2 ^ 64)%Z -> (1 <= rs)%Z -> (rs + 4 * sx < 2 ^ 64)%Z -> (rs mod 4 = 0)%Z ->
  (0 <= keld)%Z -> (keld + 24 < 2 ^ 64)%Z -> (1 <= arrd)%Z -> (0 <= i < 2 ^ 31)%Z -> (arrd + 8 * i + 8 < 2 ^ 64)%Z -> (arrd mod 8 = 0)%Z ->
  (1 <= rd)%Z -> (rd + 4 * sx < 2 ^ 64)%Z -> (rd mod 4 = 0)%Z ->
  (rs + 4 * sx <= rd \/ rd + 4 * sx <= rs)%Z -> (a7 + 8 <= rd \/ rd + 4 * sx <= a7)%Z ->
  (keld + 24 <= rd \/ rd + 4 * sx <= keld + 16)%Z -> (arrd + 8 * i + 8 <= rd \/ rd + 4 * sx <= arrd + 8 * i)%Z ->
  rdn SEGS M (Z_to_bv 64 a7) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 rs)) ->
  rdn SEGS M (Z_to_bv 64 (keld + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arrd)) ->
  rdn SEGS M (Z_to_bv 64 (arrd + 8 * i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 rd)) ->
  (forall a, (rs <= a < rs + 4 * sx)%Z -> M (Z_to_bv 64 a) <> None) ->
  store_ok SEGS M (Z_to_bv 64 rd) (Z.to_nat (4 * sx)) = true ->
  getr regs 10 = Z_to_bv 64 keld -> getr regs 12 = Z_to_bv 64 (sx - 1) -> getr regs 14 = Z_to_bv 64 (4 * sx) -> getr regs 17 = Z_to_bv 64 a7 ->
  getr regs 6 = Z_to_bv 64 j -> getr regs 5 = Z_to_bv 64 (4 * j) -> getr regs 7 = Z_to_bv 64 (8 * i) ->
  exists fr' regs' M',
    msteps SEGS (@mkst (mkFP fr cs) regs (0x38f58 : word) M al_rom) (@mkst (mkFP fr' cs) regs' (0x39004 : word) M' al_rom)
    /\ winside rd (rd + 4 * sx) M M' /\ f15_only fr fr'
    /\ (forall q bs, (j <= q < sx)%Z -> rdn SEGS M (Z_to_bv 64 (rs + 4 * (sx - 1 - q))) 4 = Some bs ->
          rdn SEGS M' (Z_to_bv 64 (rd + 4 * q)) 4 = Some (kcp bs))
    /\ regs_agree (fun x => In x [5; 6; 18; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros k fr cs regs M sx j a7 rs keld arrd i rd. intros.
  pose proof (kc_col k fr cs regs M sx j a7 rs keld arrd i rd) as KC.
  repeat (specialize (KC ltac:(assumption))).
  destruct KC as (fr' & regs' & M' & MS & WI & F & V & AG).
  exists fr', regs', M'.
  split; [exact MS |].
  split; [apply (winside_mono _ _ _ _ _ _ WI); lia |].
  split; [exact F |].
  split; [exact V | exact AG].
Qed.

(* [comment removed for export] *)
Definition KI (M : word -> option byte) (kels arrs : Z) (rowss : Z -> Z) (keld arrd : Z) (rowsd : Z -> Z) (sy sx cyd cxd : Z) : Prop :=
  rdn SEGS M (Z_to_bv 64 (kels + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arrs)) /\
  (forall r, (0 <= r < sy)%Z -> rdn SEGS M (Z_to_bv 64 (arrs + 8 * r)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (rowss r)))) /\
  (forall r a, (0 <= r < sy)%Z -> (rowss r <= a < rowss r + 4 * sx)%Z -> M (Z_to_bv 64 a) <> None) /\
  rdn SEGS M (Z_to_bv 64 (keld + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arrd)) /\
  (forall i, (0 <= i < sy)%Z -> rdn SEGS M (Z_to_bv 64 (arrd + 8 * i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (rowsd i)))) /\
  rdn SEGS M (Z_to_bv 64 keld) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 sy)) /\
  rdn SEGS M (Z_to_bv 64 (keld + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 sx)) /\
  korg M keld cyd cxd.

(* [comment removed for export] *)
Definition KG (C : lctx) (A A1 : AS) (kels arrs : Z) (rowss : Z -> Z) (keld arrd : Z) (rowsd : Z -> Z) (sy sx : Z) : Prop :=
  (4096 <= kels)%Z /\ (kels + 24 <= alloc_top (c_vm C))%Z /\ live A (Z_to_bv 64 kels) = Some 24%Z /\
  (4096 <= arrs)%Z /\ (arrs + 8 * sy <= alloc_top (c_vm C))%Z /\ live A (Z_to_bv 64 arrs) = Some (8 * sy)%Z /\ (arrs mod 8 = 0)%Z /\
  (forall r, (0 <= r < sy)%Z -> (4096 <= rowss r)%Z /\ (rowss r + 4 * sx <= alloc_top (c_vm C))%Z /\ live A (Z_to_bv 64 (rowss r)) = Some (4 * sx)%Z /\
                                (rowss r mod 4 = 0)%Z) /\
  (4096 <= keld)%Z /\ (keld + 24 <= alloc_top (c_vm C))%Z /\ live A1 (Z_to_bv 64 keld) = Some 24%Z /\ live A (Z_to_bv 64 keld) = None /\
  (4096 <= arrd)%Z /\ (arrd + 8 * sy <= alloc_top (c_vm C))%Z /\ live A1 (Z_to_bv 64 arrd) = Some (8 * sy)%Z /\ live A (Z_to_bv 64 arrd) = None /\
  (arrd mod 8 = 0)%Z /\
  (forall i, (0 <= i < sy)%Z -> (4096 <= rowsd i)%Z /\ (rowsd i + 4 * sx <= alloc_top (c_vm C))%Z /\ live A1 (Z_to_bv 64 (rowsd i)) = Some (4 * sx)%Z /\
                                live A (Z_to_bv 64 (rowsd i)) = None /\ live (c_A0 C) (Z_to_bv 64 (rowsd i)) = None /\ rowsd i <> arrd /\ rowsd i <> keld /\
                                (rowsd i mod 4 = 0)%Z) /\
  (forall i i', (0 <= i < sy)%Z -> (0 <= i' < sy)%Z -> i <> i' -> rowsd i <> rowsd i') /\
  sub_live A A1.

Definition KV (m M : word -> option byte) (rowss rowsd : Z -> Z) (sy sx n : Z) : Prop :=
  forall i q bs, (0 <= i < n)%Z -> (0 <= q < sx)%Z ->
    rdn SEGS m (Z_to_bv 64 (rowss (sy - 1 - i)%Z + 4 * (sx - 1 - q))%Z) 4 = Some bs ->
    rdn SEGS M (Z_to_bv 64 (rowsd i + 4 * q)%Z) 4 = Some (kcp bs).

Lemma KV_zero : forall m M rowss rowsd sy sx, KV m M rowss rowsd sy sx 0.
Proof. intros m M rowss rowsd sy sx i q bs Hi. lia. Qed.

Lemma kvals_ext : forall M h w rows (f g : Z -> Z -> Z), (forall i j, f i j = g i j) -> kvals M h w rows f -> kvals M h w rows g.
Proof. intros M h w rows f g E K i j Hi Hj. rewrite <- (E i j). exact (K i j Hi Hj). Qed.

Lemma KV_kvals : forall m M rowss rowsd sy sx vs, KV m M rowss rowsd sy sx sy -> kvals m sy sx rowss vs ->
  kvals M sy sx rowsd (fun i j => vs (sy - 1 - i)%Z (sx - 1 - j)%Z).
Proof.
  intros m M rowss rowsd sy sx vs V K i j Hi Hj.
  destruct (K (sy - 1 - i)%Z (sx - 1 - j)%Z ltac:(lia) ltac:(lia)) as [R FBv]. split; [|exact FBv].
  rewrite (V i j _ Hi Hj R). f_equal. apply kcp_val. destruct FBv as [Hr _].
  assert (EW : fp_width fmt_single = 32%Z) by (vm_compute; reflexivity). rewrite EW in Hr. lia.
Qed.

Lemma KI_out : forall M M' kels arrs rowss keld arrd rowsd sy sx cyd cxd (lo hi top : Z),
  KI M kels arrs rowss keld arrd rowsd sy sx cyd cxd ->
  (forall x : word, ~ (lo <= u x < hi)%Z -> M' x = M x) -> mem_grows M M' -> (0 <= lo)%Z -> (hi <= top)%Z -> (top + 64 <= 2 ^ 64)%Z ->
  (1 <= kels)%Z -> (kels + 24 <= top)%Z -> (1 <= arrs)%Z -> (arrs + 8 * sy <= top)%Z -> (1 <= keld)%Z -> (keld + 24 <= top)%Z -> (1 <= arrd)%Z -> (arrd + 8 * sy <= top)%Z ->
  (hi <= kels \/ kels + 24 <= lo)%Z -> (hi <= arrs \/ arrs + 8 * sy <= lo)%Z -> (hi <= keld \/ keld + 24 <= lo)%Z -> (hi <= arrd \/ arrd + 8 * sy <= lo)%Z ->
  KI M' kels arrs rowss keld arrd rowsd sy sx cyd cxd.
Proof.
  intros M M' kels arrs rowss keld arrd rowsd sy sx cyd cxd lo hi top (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8a & R8b) OUT MG
    Hlo Hhi Htop Hk1 Hk2 Ha1 Ha2 Hd1 Hd2 Hb1 Hb2 Dk Da Dd Db.
  assert (T : forall (a : Z) (n : nat), (0 <= a)%Z -> (a + Z.of_nat n <= top)%Z -> (a + Z.of_nat n <= lo \/ hi <= a)%Z ->
            rdn SEGS M' (Z_to_bv 64 a) n = rdn SEGS M (Z_to_bv 64 a) n).
  { intros a n Ha Han D. apply rdn_ext.
    - rewrite u_Z2bv by lia. lia.
    - intros x Hx. rewrite u_Z2bv in Hx by lia. apply OUT. lia. }
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - rewrite T by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact R1.
  - intros r Hr. rewrite T by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact (R2 r Hr).
  - intros r a Hr Ha. apply MG. exact (R3 r a Hr Ha).
  - rewrite T by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact R4.
  - intros i Hi. rewrite T by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact (R5 i Hi).
  - rewrite T by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact R6.
  - rewrite T by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact R7.
  - rewrite T by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact R8a.
  - rewrite T by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact R8b.
Qed.

Definition KREGS : list reg := [5; 6; 7; 13; 17; 18; 28; 29; 30; 31]%bv.

Lemma kt_ag_keep : forall (L : list reg) regs regs' (r : reg) (v : word),
  regs_agree (fun x => In x L) regs regs' -> existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = false ->
  getr regs r = v -> getr regs' r = v.
Proof.
  intros L regs regs' r v AG E H. rewrite AG; [exact H|]. intros Hin.
  assert (T : existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = true).
  { apply existsb_exists. exists r. split; [exact Hin | apply Z.eqb_refl]. }
  congruence.
Qed.
Ltac ktk AG := apply (kt_ag_keep _ _ _ _ _ AG); [vm_compute; reflexivity |].
Ltac ktcs := first [ left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
                   | right; right; right; left; reflexivity | right; right; right; right; left; reflexivity
                   | right; right; right; right; right; vm_compute; split; discriminate ].
Ltac ktlen := rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Ltac ktwsw CK := repeat (apply W_store_win; [exact CK | | rewrite u_Z2bv by lia; lia | ktlen]).
Ltac ktin := cbn [In]; repeat first [left; reflexivity | right].

Lemma kt_mod8 : forall z, (z mod 16 = 0)%Z -> (z mod 8 = 0)%Z.
Proof.
  intros z H. rewrite (Z.div_mod z 16) by lia. rewrite H, Z.add_0_r.
  replace (16 * (z / 16))%Z with ((2 * (z / 16)) * 8)%Z by ring. apply Z.mod_mul. lia.
Qed.
Lemma kt_mod4 : forall z, (z mod 16 = 0)%Z -> (z mod 4 = 0)%Z.
Proof.
  intros z H. rewrite (Z.div_mod z 16) by lia. rewrite H, Z.add_0_r.
  replace (16 * (z / 16))%Z with ((4 * (z / 16)) * 4)%Z by ring. apply Z.mod_mul. lia.
Qed.

Lemma kt_sok_blk : forall C A m md (p : word) (k a : Z) (n : nat), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + Z.of_nat n <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof.
  intros C A m md p k a n CK HW L Hlo Hhi Hk. pose proof (u64_range p). rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
  destruct (blk_byte C A m md p k x CK HW L ltac:(lia)) as (_ & D & _). exact (D E).
Qed.

Lemma kt_kern_mem : forall C A A' m m' kel arr h w rows, kern C A A' m kel arr h w rows ->
  rdn SEGS m' (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
  rdn SEGS m' (Z_to_bv 64 (kel + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
  rdn SEGS m' (Z_to_bv 64 (kel + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr)) ->
  (forall i, (0 <= i < h)%Z -> rdn SEGS m' (Z_to_bv 64 (arr + 8 * i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (rows i)))) ->
  kern C A A' m' kel arr h w rows.
Proof.
  intros C A A' m m' kel arr h w rows K R1 R2 R3 R4.
  destruct K as (K1 & K2 & K3 & K4 & K5 & K6 & _ & _ & _ & K10 & K11 & K12 & K13 & K14 & K15 & K16 & KR & KD & KL).
  refine (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 (conj K6 (conj R1 (conj R2 (conj R3
          (conj K10 (conj K11 (conj K12 (conj K13 (conj K14 (conj K15 (conj K16 (conj _ (conj KD KL)))))))))))))))))).
  intros i Hi. destruct (KR i Hi) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & _).
  exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 (conj X8 (R4 i Hi))))))))).
Qed.

Lemma kr2_apart : forall C A m md (p q n k : Z), Cok C -> W C A m md ->
  live A (Z_to_bv 64 p) = Some n -> live A (Z_to_bv 64 q) = Some k -> p <> q ->
  (0 <= p < 2 ^ 64)%Z -> (0 <= q < 2 ^ 64)%Z -> (0 < n)%Z -> (0 < k)%Z -> (p + n <= q \/ q + k <= p)%Z.
Proof.
  intros C A m md p q n k CK HW Lp Lq NE Hp Hq Hn Hk.
  destruct (live_apart C A m md _ _ n k CK HW Lp Lq (zbv_ne p q Hp Hq NE) ltac:(lia) ltac:(lia)) as [X | X];
    rewrite !u_Z2bv in X by lia; lia.
Qed.

Lemma kr2_livk : forall A (m M : word -> option byte) (p k a : Z) (n : nat), LIVK A m M -> live A (Z_to_bv 64 p) = Some k ->
  (0 <= p)%Z -> (p + k < 2 ^ 64)%Z -> (p <= a)%Z -> (a + Z.of_nat n <= p + k)%Z ->
  rdn SEGS M (Z_to_bv 64 a) n = rdn SEGS m (Z_to_bv 64 a) n.
Proof.
  intros A m M p k a n L Lp Hp Hpk Ha Han. apply rdn_ext.
  - rewrite u_Z2bv by lia. lia.
  - intros x Hx. rewrite u_Z2bv in Hx by lia. apply (LIVK_at A m M p k x L Lp Hp ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma ki_rows : forall (k : nat) (i : Z) fr cs regs r M C A A1 m md vm1 (s : Z) (ret : word) r0 kels arrs rowss keld arrd rowsd (sy sx cyd cxd : Z) (S : TSet),
  Cok C -> (64 <= s)%Z -> (s <= c_top C)%Z -> (c_top C - LSTK <= s - 64)%Z ->
  (1 <= sx < 2 ^ 28)%Z -> (1 <= sy < 2 ^ 28)%Z -> (0 <= i < sy)%Z -> Z.of_nat k = (sy - i)%Z ->
  KG C A A1 kels arrs rowss keld arrd rowsd sy sx ->
  W C A1 M (with_vmmaps vm1 md) -> POSTM C A s m M -> cellsZ M (framek7 s ret r0) -> KI M kels arrs rowss keld arrd rowsd sy sx cyd cxd ->
  KV m M rowss rowsd sy sx i ->
  getr r 2 = Z_to_bv 64 (s - 64) -> getr r 10 = Z_to_bv 64 keld -> getr r 8 = Z_to_bv 64 kels -> getr r 9 = Z_to_bv 64 sx ->
  getr r 11 = Z_to_bv 64 (sy - 1) -> getr r 12 = Z_to_bv 64 (sx - 1) -> getr r 13 = Z_to_bv 64 i -> getr r 14 = Z_to_bv 64 (4 * sx) ->
  getr r 15 = Z_to_bv 64 sy -> getr r 16 = Z_to_bv 64 2147483647 ->
  regs_agree (fun x => In x KREGS) regs r ->
  (forall fr' M' r', W C A1 M' (with_vmmaps vm1 md) -> POSTM C A s m M' -> cellsZ M' (framek7 s ret r0) -> KI M' kels arrs rowss keld arrd rowsd sy sx cyd cxd ->
     KV m M' rowss rowsd sy sx sy -> f15_only fr fr' ->
     getr r' 2 = Z_to_bv 64 (s - 64) -> getr r' 10 = Z_to_bv 64 keld -> regs_agree (fun x => In x KREGS) regs r' ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs) r' (0x39084 : word) M' al_rom) (with_vmmaps vm1 md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) r (0x38f00 : word) M al_rom) (with_vmmaps vm1 md)) S.
Proof.
  induction k as [| k IH]; intros i fr cs regs r M C A A1 m md vm1 s ret r0 kels arrs rowss keld arrd rowsd sy sx cyd cxd S
    CK Hs Hsc Hlo Hsx Hsy Hi Hk KGi HWM PM CF KIM KVM E2 E10 E8 E9 E11 E12 E13 E14 E15 E16 AGr POST; [lia |].
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg]. pose proof LSTK_val as LS.
  assert (IMG : (0 <= alloc_top (c_vm C))%Z) by (pose proof Cimg as X; cbn in X; lia).
  assert (GTOP : (alloc_top (c_vm C) + 8192 <= s - 64)%Z) by lia.
  pose proof KGi as (Gk1 & Gk2 & LAk & Ga1 & Ga2 & LAa & ALa & GR & Gd1 & Gd2 & LA1d & LAd & Gad1 & Gad2 & LA1ad & LAad & ALad & GRD & GDD & SL).
  pose proof KIM as (Rsa & Rsr & Rdef & Rda & Rdr & Rsy & Rsx & Ko).
  pose proof HWM as [_ WPM _ _ _ _ _ _ _ _ _]. pose proof WPM as [MHM MLM _].
  set (j0 := (sy - 1 - i)%Z).
  destruct (GR j0 ltac:(unfold j0; lia)) as (Gr1 & Gr2 & LAr & ALr).
  destruct (GRD i Hi) as (Gq1 & Gq2 & LA1q & LAq & L0q & NEqa & NEqk & ALq).
  assert (NEsr : rowss j0 <> rowsd i) by (intros E; rewrite E in LAr; congruence).
  assert (NEks : kels <> rowsd i) by (intros E; rewrite E in LAk; congruence).
  assert (NEas : arrs <> rowsd i) by (intros E; rewrite E in LAa; congruence).
  pose proof (SL _ _ LAr) as LA1r. pose proof (SL _ _ LAk) as LA1k. pose proof (SL _ _ LAa) as LA1a.
  pose proof (kr2_apart C A1 M _ (rowss j0) (rowsd i) (4 * sx) (4 * sx) CK HWM LA1r LA1q NEsr ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as DSR.
  pose proof (kr2_apart C A1 M _ kels (rowsd i) 24 (4 * sx) CK HWM LA1k LA1q NEks ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as DKR.
  pose proof (kr2_apart C A1 M _ arrs (rowsd i) (8 * sy) (4 * sx) CK HWM LA1a LA1q NEas ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as DAR.
  pose proof (kr2_apart C A1 M _ keld (rowsd i) 24 (4 * sx) CK HWM LA1d LA1q (not_eq_sym NEqk) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as DDR.
  pose proof (kr2_apart C A1 M _ arrd (rowsd i) (8 * sy) (4 * sx) CK HWM LA1ad LA1q (not_eq_sym NEqa) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as DBR.
  destruct (ki_OH al_rom (mkFP fr cs) r M kels sy sx i arrs ltac:(lia) Hi ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALa Rsa E9 E8 E11 E13)
    as (R1 & M1 & G17 & G6 & G5 & G7 & AG1).
  eapply rz_msteps; [exact MHM | exact MLM | exact M1 |].
  assert (SOKd : store_ok SEGS M (Z_to_bv 64 (rowsd i)) (Z.to_nat (4 * sx)) = true).
  { apply (kt_sok_blk C A1 M (with_vmmaps vm1 md) (Z_to_bv 64 (rowsd i)) (4 * sx)); [exact CK | exact HWM | exact LA1q | | |];
      rewrite ?u_Z2bv, ?Z2Nat.id by lia; lia. }
  destruct (ki_col (Z.to_nat sx) fr cs R1 M sx 0 (arrs + 8 * j0) (rowss j0) keld arrd i (rowsd i)
              ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALr
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALad ltac:(lia) ltac:(lia) ALq
              ltac:(lia) ltac:(unfold j0 in *; lia) ltac:(lia) ltac:(lia)
              (Rsr j0 ltac:(unfold j0; lia)) Rda (Rdr i Hi) (fun a Ha => Rdef j0 a ltac:(unfold j0; lia) Ha) SOKd
              ltac:(ktk AG1; exact E10) ltac:(ktk AG1; exact E12) ltac:(ktk AG1; exact E14) ltac:(unfold j0; exact G17)
              G6 ltac:(rewrite G5; reflexivity) G7)
    as (fr' & R2 & M' & M2 & WI & F15a & VAL & AG2).
  eapply rz_msteps; [exact MHM | exact MLM | exact M2 |].
  destruct (winside_WP C A A1 m M M' (with_vmmaps vm1 md) (Z_to_bv 64 (rowsd i)) (4 * sx) (rowsd i) (rowsd i + 4 * sx) s CK (conj HWM PM)
              LA1q LAq L0q SL ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia) WI) as (HWM' & PM').
  assert (OUT : forall x : word, ~ (rowsd i <= u x < rowsd i + 4 * sx)%Z -> M' x = M x)
    by (intros x Hx; apply (winside_out _ _ _ _ x WI); [lia | exact Hx]).
  assert (CF' : cellsZ M' (framek7 s ret r0)).
  { apply (cellsZ_out M M' (rowsd i) (rowsd i + 4 * sx)); [exact OUT | | exact CF].
    unfold framek7. repeat (apply Forall_cons; [cbn [fst snd]; lia |]). apply Forall_nil. }
  assert (KI' : KI M' kels arrs rowss keld arrd rowsd sy sx cyd cxd).
  { apply (KI_out M M' kels arrs rowss keld arrd rowsd sy sx cyd cxd (rowsd i) (rowsd i + 4 * sx) (alloc_top (c_vm C)) KIM OUT (winside_grows _ _ _ _ WI));
      lia. }
  assert (KV' : KV m M' rowss rowsd sy sx (i + 1)).
  { intros i' q bs Hi' Hq R.
    destruct (Z.eq_dec i' i) as [-> | Ni].
    - apply (VAL q bs ltac:(lia)).
      rewrite (kr2_livk A m M (rowss j0) (4 * sx) (rowss j0 + 4 * (sx - 1 - q)) 4 (proj2 PM) LAr) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      exact R.
    - destruct (GRD i' ltac:(lia)) as (Gp1 & Gp2 & LA1p & _).
      pose proof (kr2_apart C A1 M _ (rowsd i') (rowsd i) (4 * sx) (4 * sx) CK HWM LA1p LA1q (GDD i' i ltac:(lia) Hi Ni)
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as DPP.
      apply (winside_rdn SEGS (rowsd i) (rowsd i + 4 * sx) M M' (rowsd i' + 4 * q) 4 _ WI); [lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                                                                                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      exact (KVM i' q bs ltac:(lia) Hq R). }
  assert (E13' : getr R2 13 = Z_to_bv 64 i) by (ktk AG2; ktk AG1; exact E13).
  assert (E15' : getr R2 15 = Z_to_bv 64 sy) by (ktk AG2; ktk AG1; exact E15).
  assert (E16' : getr R2 16 = Z_to_bv 64 2147483647) by (ktk AG2; ktk AG1; exact E16).
  pose proof HWM' as [_ WPM' _ _ _ _ _ _ _ _ _]. pose proof WPM' as [MHM' MLM' _].
  destruct (Z.eq_dec (i + 1) sy) as [Last | NotLast].
  - destruct (ki_ON al_rom (mkFP fr' cs) true R2 M' i sy Hi ltac:(lia) Last E13' E15' E16') as (R3 & M3 & G313 & AG3).
    eapply rz_msteps; [exact MHM' | exact MLM' | exact M3 |].
    apply (POST fr' M' R3 HWM' PM' CF' KI' ltac:(replace (i + 1)%Z with sy in KV' by lia; exact KV') F15a).
    + ktk AG3; ktk AG2; ktk AG1; exact E2.
    + ktk AG3; ktk AG2; ktk AG1; exact E10.
    + unfold KREGS in AGr |- *. ra_chain.
  - destruct (ki_ON al_rom (mkFP fr' cs) false R2 M' i sy Hi ltac:(lia) ltac:(cbv iota; lia) E13' E15' E16') as (R3 & M3 & G313 & AG3).
    eapply rz_msteps; [exact MHM' | exact MLM' | exact M3 |].
    apply (IH (i + 1)%Z fr' cs regs R3 M' C A A1 m md vm1 s ret r0 kels arrs rowss keld arrd rowsd sy sx cyd cxd S
             CK Hs Hsc Hlo Hsx Hsy ltac:(lia) ltac:(lia) KGi HWM' PM' CF' KI' KV');
      try (ktk AG3; ktk AG2; ktk AG1; assumption).
    + exact G313.
    + unfold KREGS in AGr |- *. ra_chain.
    + intros fr'' M'' r'' W'' PM'' CF'' KI'' KV'' F15b S2'' S10'' AGr''.
      exact (POST fr'' M'' r'' W'' PM'' CF'' KI'' KV'' (f15_only_trans _ _ _ F15a F15b) S2'' S10'' AGr'').
Qed.

(* [comment removed for export] *)
Theorem kernelInvert_W : kernelInvert_contract.
Proof.
  intros fr cs C A m md regs s kels arrs rowss ret S CK HW Hz H2 Hs16 Hstk Hsc H1 Hret H4 H10 KO KOR kR bR AR HkR HbR POST.
  replace (Z_to_bv 64 PC_kernelInvert) with (0x38e54 : word) by (apply bv_eq; reflexivity).
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg]. pose proof LSTK_val as LS. unfold KER_STACK, LSF in Hstk.
  assert (IMG : (0 <= alloc_top (c_vm C))%Z) by (pose proof Cimg as X; cbn in X; lia).
  assert (GTOP : (alloc_top (c_vm C) + 8192 <= s - 64)%Z) by lia.
  pose proof HW as [WI WP _ _ _ _ _ _ _ _ _]. pose proof WP as [MH ML _].
  pose proof KO as (Ks1 & Ks2 & LAks & L0ks & Rsy & Rsx & Rsa & Ka1 & Ka2 & Kne & LAa & L0a & KROWS & KDIST).
  pose proof KOR as (Rcy & Rcx).
  pose proof (blk_range C A m md (Z_to_bv 64 kels) 24 CK HW LAks ltac:(lia)) as BRk. rewrite u_Z2bv in BRk by lia.
  pose proof (blk_range C A m md (Z_to_bv 64 arrs) (8 * 41) CK HW LAa ltac:(lia)) as BRa. rewrite u_Z2bv in BRa by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) LAks) as (_ & ALks & _). rewrite u_Z2bv in ALks by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) LAa) as (_ & ALa & _). rewrite u_Z2bv in ALa by lia.
  assert (SOKf : store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true) by (apply (W_sok_win C A m md); [exact CK | exact HW | lia | cbn; lia]).
  destruct (ki_A al_rom (mkFP fr cs) regs m s kels 41%Z 41%Z 20%Z 20%Z ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (kt_mod8 _ ALks)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (conj Rsy (conj Rsx (conj Rcy Rcx))) SOKf H2 H1 H10)
    as (R1 & M1 & S1 & G1a & G110 & G111 & G18 & G118 & G119 & G19 & G120 & G121 & AG1).
  set (m1 := FRK7 m s ret regs) in *.
  assert (W1 : W C A m1 md) by (unfold m1, FRK7; ktwsw CK; exact HW).
  assert (PM1 : POSTM C A s m m1).
  { apply (POSTM_range C A m md m1 (s - 56) s s CK HW); [ | lia | lia | lia].
    intros a Ha. unfold m1. apply FRK7_out; lia. }
  assert (CF1 : cellsZ m1 (framek7 s ret regs)) by (unfold m1; apply framek7_init; lia).
  assert (KO1 : kobj C A m1 kels arrs 41 41 rowss) by (exact (kobj_keep C A A A m m1 s kels arrs 41 41 rowss KO ltac:(lia) (fun q _ => eq_refl) PM1 LAks LAa)).
  eapply rz_msteps; [exact MH | exact ML | exact M1 |].
  apply (kernelCreate_S1_W (fx := mkFP fr cs) C A m1 md R1 (s - 64)%Z 41%Z 41%Z (Z_to_bv 64 0x38ea4) S kR bR CK W1 S1
           ltac:(rewrite Zminus_mod, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) G1a ltac:(red; apply bv_eq; reflexivity)
           ltac:(ktk AG1; exact H4) G110 G111 ltac:(lia) ltac:(lia) ltac:(lia) AR HkR HbR).
  intros A1 m2 vm1 R2 W2 CK2 PM2 (keld & arrd & rowsd & G2k & KN) AR1.
  replace (Z_to_bv 64 0x38ea4) with (0x38ea4 : word) by (apply bv_eq; reflexivity).
  pose proof KN as (Kk1 & Kk2 & Kk16 & LA1k & LAk & L0k & Rh & Rw & Ra & Kda1 & Kda2 & Kda16 & Kne' & LA1a & LAa' & L0a' & KROWSd & KDISTd & KFR).
  pose proof W2 as [_ WP2 _ _ _ _ _ _ _ _ _]. pose proof WP2 as [MH2 ML2 _].
  assert (SLA : sub_live A A1) by (exact (kern_sub_live _ _ _ _ _ _ _ _ _ KN)).
  assert (KO2 : kobj C A1 m2 kels arrs 41 41 rowss)
    by (exact (kobj_keep C A A1 A m1 m2 (s - 64) kels arrs 41 41 rowss KO1 ltac:(lia) (kobj_blk_sub C A A1 m1 kels arrs 41 41 rowss KO1 SLA) PM2 LAks LAa)).
  pose proof (blk_range C A1 m2 _ (Z_to_bv 64 keld) 24 CK W2 LA1k ltac:(lia)) as BRkd. rewrite u_Z2bv in BRkd by lia.
  pose proof (blk_range C A1 m2 _ (Z_to_bv 64 arrd) (8 * 41) CK W2 LA1a ltac:(lia)) as BRad. rewrite u_Z2bv in BRad by lia.
  assert (SOKk : store_ok SEGS m2 (Z_to_bv 64 (keld + 8)) 8 = true).
  { apply (kt_sok_blk C A1 m2 (with_vmmaps vm1 md) (Z_to_bv 64 keld) 24); [exact CK | exact W2 | exact LA1k | | |]; rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  destruct (ki_B al_rom (mkFP fr cs) R2 m2 keld 41%Z 41%Z 20%Z 20%Z ltac:(lia) ltac:(lia) (kt_mod8 _ Kk16) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOKk G2k
              ltac:(rewrite (cs_kept_get _ _ 18%bv CK2) by ktcs; exact G118)
              ltac:(rewrite (cs_kept_get _ _ 9%bv CK2) by ktcs; exact G19)
              ltac:(rewrite (cs_kept_get _ _ 19%bv CK2) by ktcs; exact G119)
              ltac:(rewrite (cs_kept_get _ _ 20%bv CK2) by ktcs; exact G120)
              ltac:(rewrite (cs_kept_get _ _ 21%bv CK2) by ktcs; exact G121))
    as (R3 & M3 & G310 & G311 & G312 & G313 & G314 & G315 & G316 & G39 & G318 & AG3).
  set (m2b := wbytes m2 (Z_to_bv 64 (keld + 8)) (word_to_le_bytes 4 (Z_to_bv 64 (41 - 1 - 20)))) in *.
  set (m3 := wbytes m2b (Z_to_bv 64 (keld + 12)) (word_to_le_bytes 4 (Z_to_bv 64 (41 - 1 - 20)))) in *.
  assert (W2b : W C A1 m2b (with_vmmaps vm1 md)).
  { unfold m2b. apply (W_store_blk C A1 m2 _ (Z_to_bv 64 keld) _ 24); [exact CK | exact W2 | exact LA1k | exact L0k | rewrite !u_Z2bv by lia; lia | ktlen]. }
  assert (W3 : W C A1 m3 (with_vmmaps vm1 md)).
  { unfold m3. apply (W_store_blk C A1 m2b _ (Z_to_bv 64 keld) _ 24); [exact CK | exact W2b | exact LA1k | exact L0k | rewrite !u_Z2bv by lia; lia | ktlen]. }
  assert (PM3 : POSTM C A (s - 64) m2 m3).
  { eapply POSTM_trans.
    - unfold m2b. apply (POSTM_blk C A A1 m2 _ (Z_to_bv 64 keld) (Z_to_bv 64 (keld + 8)) 24 (word_to_le_bytes 4 (Z_to_bv 64 (41 - 1 - 20))) (s - 64) CK W2 LA1k LAk SLA);
        [rewrite !u_Z2bv by lia; lia | ktlen].
    - unfold m3. apply (POSTM_blk C A A1 m2b _ (Z_to_bv 64 keld) (Z_to_bv 64 (keld + 12)) 24 (word_to_le_bytes 4 (Z_to_bv 64 (41 - 1 - 20))) (s - 64) CK W2b LA1k LAk SLA);
        [rewrite !u_Z2bv by lia; lia | ktlen]. }
  assert (PMm3 : POSTM C A s m m3).
  { eapply POSTM_trans; [exact PM1 |]. eapply POSTM_trans; [apply (POSTM_mono C A (s - 64) s); [lia | exact PM2] |].
    apply (POSTM_mono C A (s - 64) s); [lia | exact PM3]. }
  assert (CF3 : cellsZ m3 (framek7 s ret regs)).
  { apply (cellsZ_frm C (s - 64) m1 m3); [exact CK | exact (FRM_trans _ _ _ _ _ (proj1 PM2) (proj1 PM3)) | lia | | exact CF1].
    eapply Forall_impl; [| apply framek7_bounds; lia]. intros av Hav. cbn beta in Hav |- *. lia. }
  assert (KO3 : kobj C A1 m3 kels arrs 41 41 rowss)
    by (exact (kobj_keep C A1 A1 A m2 m3 (s - 64) kels arrs 41 41 rowss KO2 ltac:(lia) (fun q _ => eq_refl) PM3 LAks LAa)).
  pose proof KO3 as (_ & _ & LA1ks & _ & _ & _ & Rsa3 & _ & _ & _ & LA1as & _ & KROWS3 & _).
  assert (DKA : (arrd + 328 <= keld \/ keld + 24 <= arrd)%Z).
  { destruct (live_apart C A1 m2 _ (Z_to_bv 64 arrd) (Z_to_bv 64 keld) (8 * 41) 24 CK W2 LA1a LA1k
                (zbv_ne arrd keld ltac:(lia) ltac:(lia) (fun E => Kne' (eq_sym E))) ltac:(lia) ltac:(lia)) as [X | X];
      rewrite !u_Z2bv in X by lia; lia. }
  assert (KI3 : KI m3 kels arrs rowss keld arrd rowsd 41 41 20 20).
  { unfold KI. refine (conj Rsa3 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
    - intros r Hr. destruct (KROWS3 r Hr) as (_ & _ & _ & _ & _ & _ & X). exact X.
    - intros r a Hr Ha. destruct (KROWS3 r Hr) as (X1 & X2 & _ & _ & X5 & _ & _).
      destruct (blk_byte C A1 m3 (with_vmmaps vm1 md) (Z_to_bv 64 (rowss r)) (4 * 41) (Z_to_bv 64 a) CK W3 X5 ltac:(rewrite !u_Z2bv by lia; lia)) as (_ & D & _).
      exact D.
    - unfold m3, m2b. rewrite !rdn_wbytes_out_Z by ktlen. exact Ra.
    - intros i Hi. destruct (KROWSd i Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & X).
      unfold m3, m2b. rewrite !rdn_wbytes_out_Z by ktlen. exact X.
    - unfold m3, m2b. rewrite !rdn_wbytes_out_Z by ktlen. exact Rh.
    - unfold m3, m2b. rewrite !rdn_wbytes_out_Z by ktlen. exact Rw.
    - split.
      + unfold m3, m2b. rewrite rdn_wbytes_out_Z by ktlen. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia.
      + unfold m3. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  assert (KG3 : KG C A A1 kels arrs rowss keld arrd rowsd 41 41).
  { unfold KG.
    split; [lia |]. split; [exact Ks2 |]. split; [exact LAks |].
    split; [lia |]. split; [exact Ka2 |]. split; [exact LAa |]. split; [exact (kt_mod8 _ ALa) |].
    split.
    { intros r Hr. destruct (KROWS r Hr) as (X1 & X2 & _ & _ & X5 & _ & _).
      pose proof (blk_range C A m md (Z_to_bv 64 (rowss r)) (4 * 41) CK HW X5 ltac:(lia)) as BR. rewrite u_Z2bv in BR by lia.
      pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) X5) as (_ & ALr & _). rewrite u_Z2bv in ALr by lia.
      split; [lia |]. split; [exact X2 |]. split; [exact X5 | exact (kt_mod4 _ ALr)]. }
    split; [lia |]. split; [exact Kk2 |]. split; [exact LA1k |]. split; [exact LAk |].
    split; [lia |]. split; [exact Kda2 |]. split; [exact LA1a |]. split; [exact LAa' |].
    split; [exact (kt_mod8 _ Kda16) |].
    split.
    { intros i Hi. destruct (KROWSd i Hi) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & _).
      pose proof (blk_range C A1 m2 _ (Z_to_bv 64 (rowsd i)) (4 * 41) CK W2 X6 ltac:(lia)) as BR. rewrite u_Z2bv in BR by lia.
      split; [lia |]. split; [exact X2 |]. split; [exact X6 |]. split; [exact X7 |]. split; [exact X8 |]. split; [exact X4 |].
      split; [exact X5 | exact (kt_mod4 _ X3)]. }
    split; [exact KDISTd | exact SLA]. }
  eapply rz_msteps; [exact MH2 | exact ML2 | exact M3 |].
  apply (ki_rows 41%nat 0%Z fr cs R3 R3 m3 C A A1 m md vm1 s ret regs kels arrs rowss keld arrd rowsd 41%Z 41%Z 20%Z 20%Z S
           CK ltac:(lia) Hsc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity)
           KG3 W3 PMm3 CF3 KI3 (KV_zero _ _ _ _ _ _)
           ltac:(ktk AG3; rewrite (cs_kept_get _ _ 2%bv CK2) by ktcs; exact S1) G310
           ltac:(ktk AG3; rewrite (cs_kept_get _ _ 8%bv CK2) by ktcs; exact G18) G39 G311 G312 G313 G314 G315 G316
           (regs_agree_refl _ _)).
  intros fr' M' r' W' PM' CF' KI' KV' F15 S2' S10' AGr.
  destruct (ki_E al_rom (mkFP fr' cs) r' regs M' s ret ltac:(lia) ltac:(lia) Hret CF' S2') as (RE & ME & SE2 & SE1 & KE & AGE).
  pose proof W' as [_ WP' _ _ _ _ _ _ _ _ _]. pose proof WP' as [MH' ML' _].
  eapply rz_msteps; [exact MH' | exact ML' | exact ME |].
  assert (KEEP : forall x : reg, ~ In x [1; 2; 8; 9; 10; 11; 18; 19; 20; 21]%list -> ~ In x [11; 12; 13; 14; 15; 16]%list ->
            ~ In x KREGS -> ~ In x [1; 2; 8; 9; 18; 19; 20; 21]%list -> AllocIface.callee_saved x -> getr RE x = getr regs x).
  { intros x N1 N2 N3 N4 CS. rewrite (AGE x N4), (AGr x N3), (AG3 x N2), (cs_kept_get _ _ x CK2 CS), (AG1 x N1). reflexivity. }
  apply (POST fr' cs A1 M' vm1 RE W' Hz).
  - apply cs_kept_intro; [rewrite SE2, H2; reflexivity | | | | | | | | | | | | | |];
      first [ apply KE; solve [ktin]
            | apply KEEP; [notin_list | notin_list | unfold KREGS; notin_list | notin_list | ktcs] ].
  - exact PM'.
  - exists keld, arrd, rowsd.
    pose proof KI' as (_ & _ & _ & Ra' & Rr' & Rh' & Rw' & Ko').
    split; [rewrite (AGE 10%bv) by notin_list; exact S10' |].
    split; [exact (kt_kern_mem C A A1 m2 M' keld arrd 41 41 rowsd KN Rh' Rw' Ra' Rr') |].
    split; [exact Ko' |].
    intros vs K. eapply kvals_ext; [| exact (KV_kvals m M' rowss rowsd 41 41 vs KV' K)].
    intros i j. cbn beta. f_equal; lia.
  - exact (f15_only_fs fr fr' F15).
  - exact AR1.
Qed.

End KinvW.
