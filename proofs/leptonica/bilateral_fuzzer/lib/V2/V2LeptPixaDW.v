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
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptRoom LeptSlots LeptExec LeptExecW LeptExecFP LeptExecX DitherLib DitherLoop LeptCmapArr LeptExecB LeptArithB LeptBracketB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptPixCopyST V2LeptPixaCreate V2LeptPixDestroyH V2LeptPixaDRun.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.
(* [comment removed for export] *)
#[local] Opaque RiscvSemantics.store_ok.

Section PixaDW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Definition BXD_WIN : Z := (96 + ALLOC_STACK)%Z.
Definition PAD_WIN : Z := (144 + ALLOC_STACK)%Z.
(* [comment removed for export] *)
Definition pd_rest : list (bv 5) := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition PA4 (pa parr ba barr : Z) : list word := map (Z_to_bv 64) [pa; parr; ba; barr].

(* [comment removed for export] *)
Definition pd_mem (C : lctx) (Ar A : AS) (m : word -> option byte) (parr w h i pix data : Z) : Prop :=
  (4096 <= pix)%Z /\ (pix + 64 <= alloc_top (c_vm C))%Z /\ (4096 <= data)%Z /\ (data + 4 * (wpl_of w 8 * h) <= alloc_top (c_vm C))%Z /\ pix <> data /\
  live Ar (Z_to_bv 64 pix) = None /\ live Ar (Z_to_bv 64 data) = None /\ live (c_A0 C) (Z_to_bv 64 pix) = None /\ live (c_A0 C) (Z_to_bv 64 data) = None /\
  live A (Z_to_bv 64 pix) = Some 64%Z /\ live A (Z_to_bv 64 data) = Some (4 * (wpl_of w 8 * h))%Z /\
  PIXat m pix (hdv w h 8 0 data) /\ rdn SEGS m (Z_to_bv 64 (parr + 8 * i)) 8 = Some (Z_to_le_bytes 8 pix).

(* [comment removed for export] *)
Definition pd_memq (pixes datad : Z -> Z) (lo hi : Z) (q : word) : Prop :=
  exists i, (lo <= i < hi)%Z /\ (q = Z_to_bv 64 (pixes i) \/ q = Z_to_bv 64 (datad i)).
(* [comment removed for export] *)
Definition pd_gone (pa parr ba barr : Z) (pixes datad : Z -> Z) (q : word) : Prop :=
  In q (PA4 pa parr ba barr) \/ pd_memq pixes datad 0 10 q.

(* [comment removed for export] *)
Lemma POSTD_of_rinv_slot : forall C A s pp (m m' : word -> option byte), rinv [(pp, 8%Z)] m m' -> POSTD C A s pp m m'.
Proof.
  intros C A s pp m m' [_ H]. split.
  - intros a _ _ _ _ _ Hs. apply H. intros r [<-|[]] Hi. apply Hs. exact Hi.
  - intros q k i _ _ Hs. apply H. intros r [<-|[]] Hi. apply Hs. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma sok_cell4 : forall C A m md (q : word) (n a : Z), Cok C -> W C A m md -> live A q = Some n ->
  (u q <= a)%Z -> (a + 4 <= u q + n)%Z -> store_ok SEGS m (Z_to_bv 64 a) 4 = true.
Proof.
  intros C A m md q n a CK HW Hl H1 H2.
  destruct (blk_range C A m md q n CK HW Hl ltac:(lia)) as [Hr1 Hr2].
  pose proof (alloc_top_lt_errno (c_vm C)) as Ht. unfold stack_max_size in Ht.
  apply (exW_sok_blk SEGS C A m md (u q) n a 4%nat p16_segs CK HW); [rewrite Z_to_bv_bv_unsigned; exact Hl | lia ..].
Qed.

Lemma bxw_POSTD_rinv : forall C A A' m md (M' : word -> option byte) (q : word) (n s pp lo len c k : Z), Cok C -> W C A m md ->
  live A q = Some n -> live A' q = None -> sub_live A' A ->
  rinv [(lo, len); (c, k)] m M' -> (c_top C - LSTK <= lo)%Z -> (lo + len <= s)%Z -> (s <= c_top C)%Z ->
  (u q <= c)%Z -> (c + k <= u q + n)%Z -> POSTD C A' s pp m M'.
Proof.
  intros C A A' m md M' q n s pp lo len c k CK HW Lq L'q SUB [_ RI] Hlo Hls Hs Hc1 Hc2.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  split.
  - intros a NH _ _ _ NS _. apply RI. intros r [<-|[<-|[]]]; unfold inreg; cbn [fst snd]; intro Hin.
    + apply NS. unfold scratch. lia.
    + apply NH. exact (proj1 (blk_byte C A m md q n a CK HW Lq ltac:(lia))).
  - intros q' k' i Lq' Hi _. apply RI.
    assert (LAq' : live A q' = Some k') by (apply SUB; exact Lq').
    assert (NE : q <> q') by (intros ->; rewrite Lq' in L'q; discriminate).
    pose proof (ai_live_hull A m (m_vmmaps md) q' k' (w_inv _ _ _ _ HW) LAq') as (Hk0 & _).
    pose proof (ai_live_hull A m (m_vmmaps md) q n (w_inv _ _ _ _ HW) Lq) as (Hn0 & _).
    destruct (blk_range C A m md q' k' CK HW LAq' ltac:(lia)) as [Bq1 Bq2].
    assert (Ux : u (at_ q' i) = (u q' + i)%Z) by (unfold at_; apply u_Z2bv; lia).
    pose proof (blk_byte C A m md q' k' (at_ q' i) CK HW LAq' ltac:(lia)) as (_ & _ & _ & NW & _).
    pose proof (ai_live_disjoint A m (m_vmmaps md) q n q' k' (w_inv _ _ _ _ HW) Lq LAq' NE) as DJ.
    assert (R1 : (n <= round16 n)%Z) by (apply round16_ge; lia).
    assert (R2 : (k' <= round16 k')%Z) by (apply round16_ge; lia).
    intros r [<-|[<-|[]]]; unfold inreg; cbn [fst snd]; intro Hin.
    + apply NW. unfold win. lia.
    + lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem boxaDestroy0_W : forall C A m md regs (s pp kb ba barr : Z) (pb : word) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BXD_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 -> (pp mod 8 = 0)%Z -> getr regs 10 = Z_to_bv 64 pp ->
  slotok C A s pp (Some (pb, kb)) ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 ba) ->
  (0 <= ba < 2 ^ 64)%Z -> (0 <= barr < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 ba) = Some 24%Z -> live (c_A0 C) (Z_to_bv 64 ba) = None ->
  live A (Z_to_bv 64 barr) = Some 80%Z -> live (c_A0 C) (Z_to_bv 64 barr) = None ->
  rdn SEGS m (Z_to_bv 64 ba) 4 = Some (Z_to_le_bytes 4 0) -> rdn SEGS m (Z_to_bv 64 (ba + 8)) 4 = Some (Z_to_le_bytes 4 1) ->
  rdn SEGS m (Z_to_bv 64 (ba + 16)) 8 = Some (Z_to_le_bytes 8 barr) ->
  pb <> Z_to_bv 64 ba -> pb <> Z_to_bv 64 barr ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 ba) = None -> live A' (Z_to_bv 64 barr) = None ->
     (forall q, q <> Z_to_bv 64 ba -> q <> Z_to_bv 64 barr -> live A' q = live A q) -> sub_live A' A ->
     POSTD C A' s pp m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 0x18fa0) m al_rom) md) S.
Proof.
  intros C A m md regs s pp kb ba barr pb ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 ALpp H10 SL Rpp Hba64 Hbarr64 Lba L0ba Lbarr L0barr
    Rn Rrc Rarr NEpa NEpb HK.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg]. pose proof LSTK_val as LS. cbv [ll_img LLU16 snd] in Cimg.
  unfold BXD_WIN, ALLOC_STACK in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (SLx := SL). unfold slotok in SLx. destruct SLx as (Lpb & L0pb & Hpb1 & Hpb2).
  destruct (blk_range C A m md pb kb CK HW Lpb ltac:(lia)) as [Bpb1 Bpb2].
  destruct (blk_range C A m md (Z_to_bv 64 ba) 24 CK HW Lba ltac:(lia)) as [Bba1 Bba2]. rewrite u_Z2bv in Bba1, Bba2 by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lba) as (_ & ALba & _). rewrite u_Z2bv in ALba by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lpb) as (Hkb0 & _).
  pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lpb Lba NEpa) as DJpb. rewrite u_Z2bv in DJpb by lia.
  assert (R16a : (kb <= round16 kb)%Z) by (apply round16_ge; lia).
  assert (R16b : (24 <= round16 24)%Z) by (apply round16_ge; lia).
  assert (HsR : (4096 + 96 <= s <= 2 ^ 47)%Z) by lia.
  assert (Hpp4k : (4096 <= pp)%Z) by lia.
  assert (DJ : (pp + 8 <= ba \/ ba + 24 <= pp)%Z) by lia.
  assert (NEab : Z_to_bv 64 ba <> Z_to_bv 64 barr) by (intros E; pose proof Lba as X; rewrite E in X; congruence).
  assert (M16 : ((s - 96) mod 16 = 0)%Z) by (rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) |
    exact (bd_A al_rom fx regs m s pp ba barr HsR Hpp4k ltac:(lia) Bba1 ltac:(lia) ALba ALpp Hbarr64 DJ Rpp Rn Rrc Rarr
             (W_sok_win C A m md (s - 96) 96 CK HW ltac:(lia) ltac:(cbn; lia))
             (sok_cell4 C A m md (Z_to_bv 64 ba) 24 (ba + 8) CK HW Lba ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia))
             H2 H10) |].
  intros fin (r1 & M1 & -> & RI1 & C8 & S1 & S8 & S9 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & G1 & G2 & G8 & G19 & G10 & AG1).
  assert (W1 : W C A M1 md).
  { apply (rinv_W C A m md M1 [((s - 96)%Z, 96%Z); ((ba + 8)%Z, 4%Z)] s CK HW Hhi RI1).
    unfold own_regions. apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil].
    right. exists (Z_to_bv 64 ba), 24%Z. cbn [fst snd]. rewrite u_Z2bv by lia. refine (conj Lba (conj L0ba (conj _ _))); lia. }
  unfold PC_FREE.
  apply (W_free16 C A M1 md r1 (Z_to_bv 64 barr) (getr r1 1) 80 (s - 96) S CK W1 G10 Lbarr L0barr eq_refl
           ltac:(rewrite G1; red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) G2 M16 ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m2 vm1 r2 W2 CS2 LB2 LEQ2 PM2 RT2.
  rewrite G1.
  eapply rz_reach; [exact (w_pure _ _ _ _ W2) | exact (bd_B al_rom fx r2 m2 s ba HsR Hba64 ltac:(csr; reflexivity) ltac:(csr; reflexivity)) |].
  intros fin (r3 & M3 & -> & -> & B1 & B2 & B10 & AG3).
  assert (LA1ba : live A1 (Z_to_bv 64 ba) = Some 24%Z) by (rewrite (LEQ2 _ NEab); exact Lba).
  unfold PC_FREE.
  apply (W_free16 C A1 m2 (with_vmmaps vm1 md) r3 (Z_to_bv 64 ba) (getr r3 1) 24 (s - 96) S CK W2 B10 LA1ba L0ba eq_refl
           ltac:(rewrite B1; red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) B2 M16 ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m3 vm2 r4 W3 CS4 LB4 LEQ4 PM4 RT4.
  rewrite with_vmmaps_twice in W3 |- *. rewrite B1.
  assert (NEbb : Z_to_bv 64 barr <> Z_to_bv 64 ba) by (intros E; apply NEab; symmetry; exact E).
  assert (LA2barr : live A2 (Z_to_bv 64 barr) = None) by (rewrite (LEQ4 _ NEbb); exact LB2).
  assert (EQ2 : forall q, q <> Z_to_bv 64 ba -> q <> Z_to_bv 64 barr -> live A2 q = live A q).
  { intros q N1 N2. rewrite (LEQ4 q N1). exact (LEQ2 q N2). }
  assert (SUB2 : sub_live A2 A).
  { intros q k Lq. assert (N1 : q <> Z_to_bv 64 ba) by (intros ->; rewrite Lq in LB4; discriminate).
    assert (N2 : q <> Z_to_bv 64 barr) by (intros ->; rewrite Lq in LA2barr; discriminate).
    rewrite <- (EQ2 q N1 N2). exact Lq. }
  assert (SUB21 : sub_live A2 A1).
  { intros q k Lq. assert (N1 : q <> Z_to_bv 64 ba) by (intros ->; rewrite Lq in LB4; discriminate).
    rewrite <- (LEQ4 q N1). exact Lq. }
  assert (Lpb2 : live A2 pb = Some kb) by (rewrite (EQ2 pb NEpa NEpb); exact Lpb).
  assert (SL2 : slotok C A2 s pp (Some (pb, kb))).
  { apply (slot_keep C A A2 s pp _ SL). intros p n E. injection E as <- <-. exact (EQ2 pb NEpa NEpb). }
  assert (RR : forall a : Z, (s - 96 <= a)%Z -> (a + 8 <= s)%Z -> rdn SEGS m3 (Z_to_bv 64 a) 8 = rdn SEGS M1 (Z_to_bv 64 a) 8).
  { intros a Ha1 Ha2.
    rewrite (FRM_rdn16 C (s - 96) m2 m3 a 8 CK (proj1 PM4)) by (cbn; lia).
    exact (FRM_rdn16 C (s - 96) M1 m2 a 8 CK (proj1 PM2) ltac:(lia) ltac:(cbn; lia) ltac:(lia)). }
  assert (SOKpp : store_ok SEGS m3 (Z_to_bv 64 pp) 8 = true).
  { rewrite <- p16_segs. exact (slot_sok C A2 m3 _ s pp _ CK W3 SL2 ltac:(lia)). }
  eapply rz_reach; [exact (w_pure _ _ _ _ W3) |
    exact (bd_C al_rom fx r4 m3 s pp ret (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
             (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
             HsR Hpp4k ltac:(lia) ltac:(lia) Hret H1 SOKpp
             ltac:(rewrite (RR (s - 8)%Z) by lia; exact S1) ltac:(rewrite (RR (s - 16)%Z) by lia; exact S8)
             ltac:(rewrite (RR (s - 24)%Z) by lia; exact S9) ltac:(rewrite (RR (s - 32)%Z) by lia; exact S18)
             ltac:(rewrite (RR (s - 40)%Z) by lia; exact S19) ltac:(rewrite (RR (s - 48)%Z) by lia; exact S20)
             ltac:(rewrite (RR (s - 56)%Z) by lia; exact S21) ltac:(rewrite (RR (s - 64)%Z) by lia; exact S22)
             ltac:(rewrite (RR (s - 72)%Z) by lia; exact S23) ltac:(rewrite (RR (s - 80)%Z) by lia; exact S24)
             ltac:(rewrite (RR (s - 88)%Z) by lia; exact S25) ltac:(rewrite (RR (s - 96)%Z) by lia; exact S26)
             ltac:(csr; reflexivity) ltac:(csr; reflexivity)) |].
  intros fin (r5 & M5 & -> & RI5 & R0 & F2 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & AG5).
  apply (HK A2 M5 vm2 r5).
  - apply (rinv_W C A2 m3 (with_vmmaps vm2 md) M5 [(pp, 8%Z)] s CK W3 Hhi RI5).
    unfold own_regions. apply Forall_cons; [|apply Forall_nil]. right. exists pb, kb. cbn [fst snd].
    refine (conj Lpb2 (conj L0pb (conj _ _))); lia.
  - apply cs_kept_of_rest; [rewrite F2, H2; reflexivity | exact F8 | exact F9 |].
    intros r Hr. cbn [In cs_rest] in Hr. repeat (destruct Hr as [<-|Hr]; [csr; reflexivity|]). destruct Hr.
  - exact LB4.
  - exact LA2barr.
  - exact EQ2.
  - exact SUB2.
  - assert (PD0 : POSTD C A2 s pp m M1).
    { apply (bxw_POSTD_rinv C A A2 m md M1 (Z_to_bv 64 ba) 24 s pp (s - 96) 96 (ba + 8) 4 CK HW Lba LB4 SUB2 RI1);
        rewrite ?u_Z2bv by lia; lia. }
    assert (PD1 : POSTD C A2 s pp M1 m2).
    { apply (POSTD_of_POSTM C A1 A2 s pp M1 m2); [| exact SUB21]. eapply POSTM_mono; [|exact PM2]. lia. }
    assert (PD2 : POSTD C A2 s pp m2 m3).
    { apply (POSTD_of_POSTM C A2 A2 s pp m2 m3); [| apply sub_live_refl]. eapply POSTM_mono; [|exact PM4]. lia. }
    eapply POSTD_trans; [exact PD0|]. eapply POSTD_trans; [exact PD1|]. eapply POSTD_trans; [exact PD2|].
    exact (POSTD_of_rinv_slot C A2 s pp m3 M5 RI5).
  - exact R0.
  - rewrite with_vmmaps_vmmaps in RT4. exact (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT2 RT4 ltac:(lia) ltac:(lia)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma POSTD_rdn_blk : forall C A s pp (m m' : word -> option byte) (q : word) (k a : Z) (n : nat), POSTD C A s pp m m' -> live A q = Some k ->
  (u q <= a)%Z -> (a + Z.of_nat n <= u q + k)%Z -> (u q + k <= 2 ^ 64)%Z -> (pp + 8 <= a \/ a + Z.of_nat n <= pp)%Z ->
  rdn SEGS m' (Z_to_bv 64 a) n = rdn SEGS m (Z_to_bv 64 a) n.
Proof.
  intros C A s pp m m' q k a n HP Hl H1 H2 H3 H4.
  assert (Hq : (0 <= u q < 2 ^ 64)%Z) by (pose proof (bv_unsigned_in_range 64 q) as H; unfold bv_modulus in H; exact H).
  assert (Ha : (0 <= u (Z_to_bv 64 a) < 2 ^ 64)%Z) by (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a)) as H; unfold bv_modulus in H; exact H).
  destruct (Nat.eq_dec n 0) as [->|Hn].
  { apply rdn_ext; [lia | intros x Hx; lia]. }
  apply rdn_ext; [rewrite u_small by lia; lia | ].
  intros x Hx. rewrite u_small in Hx by lia.
  apply (POSTD_blk_byte C A s pp m m' q k x HP Hl); [lia | unfold inslot; lia].
Qed.

(* [comment removed for export] *)
Definition pd_invM (C : lctx) (Ar Ae A : AS) (m0 m : word -> option byte) (regs0 : bvmap 5 word) (s pp kb : Z) (pb : word) (pa parr ba barr w h i : Z) (pixes datad : Z -> Z) : Prop :=
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs0 1)) /\ rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs0 8)) /\
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs0 9)) /\ rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs0 18)) /\
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs0 19)) /\
  slotok C A s pp (Some (pb, kb)) /\ sub_live Ar A /\
  live A (Z_to_bv 64 pa) = Some 32%Z /\ live A (Z_to_bv 64 parr) = Some 80%Z /\ live A (Z_to_bv 64 ba) = Some 24%Z /\ live A (Z_to_bv 64 barr) = Some 80%Z /\
  rdn SEGS m (Z_to_bv 64 pa) 4 = Some (Z_to_le_bytes 4 10) /\ rdn SEGS m (Z_to_bv 64 (pa + 16)) 8 = Some (Z_to_le_bytes 8 parr) /\ rdn SEGS m (Z_to_bv 64 (pa + 24)) 8 = Some (Z_to_le_bytes 8 ba) /\
  rdn SEGS m (Z_to_bv 64 ba) 4 = Some (Z_to_le_bytes 4 0) /\ rdn SEGS m (Z_to_bv 64 (ba + 8)) 4 = Some (Z_to_le_bytes 4 1) /\ rdn SEGS m (Z_to_bv 64 (ba + 16)) 8 = Some (Z_to_le_bytes 8 barr) /\
  (forall j, (i <= j < 10)%Z -> pd_mem C Ar A m parr w h j (pixes j) (datad j)) /\
  (forall j, (0 <= j < i)%Z -> live A (Z_to_bv 64 (pixes j)) = None /\ live A (Z_to_bv 64 (datad j)) = None) /\
  (forall q, ~ pd_memq pixes datad 0 i q -> live A q = live Ae q) /\
  (forall Az, sub_live Az A -> live Az (Z_to_bv 64 pa) = None -> live Az (Z_to_bv 64 parr) = None -> POSTD C Az s pp m0 m).

(* [comment removed for export] *)
Definition pd_static (C : lctx) (Ar : AS) (pb : word) (pa parr ba barr w h : Z) (pixes datad : Z -> Z) : Prop :=
  (0 <= pa < 2 ^ 64)%Z /\ (0 <= parr < 2 ^ 64)%Z /\ (0 <= ba < 2 ^ 64)%Z /\ (0 <= barr < 2 ^ 64)%Z /\
  live (c_A0 C) (Z_to_bv 64 pa) = None /\ live (c_A0 C) (Z_to_bv 64 parr) = None /\ live (c_A0 C) (Z_to_bv 64 ba) = None /\ live (c_A0 C) (Z_to_bv 64 barr) = None /\
  live Ar (Z_to_bv 64 pa) = None /\ live Ar (Z_to_bv 64 parr) = None /\ live Ar (Z_to_bv 64 ba) = None /\ live Ar (Z_to_bv 64 barr) = None /\
  live Ar pb = None /\ live (c_A0 C) pb = None /\ parr <> barr /\ (1 <= w)%Z /\ (1 <= h)%Z /\
  (forall j k, (0 <= j < k)%Z -> (k < 10)%Z -> datad j <> datad k /\ pixes j <> pixes k /\ pixes j <> datad k /\ datad j <> pixes k) /\
  (forall j, (0 <= j < 10)%Z -> ~ In (Z_to_bv 64 (pixes j)) (PA4 pa parr ba barr) /\ ~ In (Z_to_bv 64 (datad j)) (PA4 pa parr ba barr)) /\
  (forall j, (0 <= j < 10)%Z -> pb <> Z_to_bv 64 (pixes j) /\ pb <> Z_to_bv 64 (datad j)) /\
  ~ In pb (PA4 pa parr ba barr).

Lemma notin_PA4 : forall (q : word) pa parr ba barr, ~ In q (PA4 pa parr ba barr) ->
  q <> Z_to_bv 64 pa /\ q <> Z_to_bv 64 parr /\ q <> Z_to_bv 64 ba /\ q <> Z_to_bv 64 barr.
Proof.
  intros q pa parr ba barr H. unfold PA4 in H. cbn [map In] in H.
  split; [intros ->; apply H; left; reflexivity|].
  split; [intros ->; apply H; right; left; reflexivity|].
  split; intros ->; apply H; right; right; [left|right; left]; reflexivity.
Qed.

Lemma pdl_disj : forall A m vm (p q : word) (n k : Z), ainv A m vm -> live A p = Some n -> live A q = Some k -> n <> k ->
  (u p + n <= u q \/ u q + k <= u p)%Z.
Proof.
  intros A m vm p q n k HI Lp Lq NE.
  assert (NEpq : p <> q) by (intros ->; rewrite Lp in Lq; injection Lq as E; exact (NE E)).
  pose proof (ai_live_disjoint A m vm p n q k HI Lp Lq NEpq) as D.
  pose proof (ai_live_hull A m vm p n HI Lp) as (Hn & _).
  pose proof (ai_live_hull A m vm q k HI Lq) as (Hk & _).
  unfold round16 in D.
  pose proof (Z.div_mod (n + 15) 16 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound (n + 15) 16 ltac:(lia)) as E2.
  pose proof (Z.div_mod (k + 15) 16 ltac:(lia)) as E3. pose proof (Z.mod_pos_bound (k + 15) 16 ltac:(lia)) as E4.
  lia.
Qed.

(* [comment removed for export] *)
Lemma pda_loop_W : forall (n : nat) C Ar Ae A (m0 m : word -> option byte) md vme regs regs0 (s pp kb pa parr ba barr w h i : Z) (pb : word) (pixes datad : Z -> Z) (S : TSet),
  Z.of_nat n = (10 - i)%Z -> (0 <= i < 10)%Z -> Cok C -> W C A m md ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + PAD_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 4 = Z_to_bv 64 0x56270 -> getr regs 8 = Z_to_bv 64 pa -> getr regs 9 = Z_to_bv 64 pp ->
  getr regs 18 = Z_to_bv 64 (8 * i) -> getr regs 19 = Z_to_bv 64 i -> (forall r, In r pd_rest -> getr regs r = getr regs0 r) ->
  pd_static C Ar pb pa parr ba barr w h pixes datad ->
  pd_invM C Ar Ae A m0 m regs0 s pp kb pb pa parr ba barr w h i pixes datad ->
  roomtr Ae vme A (m_vmmaps md) 0 0 ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) ->
     getr regs' 2 = Z_to_bv 64 (s - 48) -> getr regs' 4 = Z_to_bv 64 0x56270 -> getr regs' 8 = Z_to_bv 64 pa -> getr regs' 9 = Z_to_bv 64 pp ->
     (forall r, In r pd_rest -> getr regs' r = getr regs0 r) ->
     pd_invM C Ar Ae A' m0 m' regs0 s pp kb pb pa parr ba barr w h 10 pixes datad ->
     roomtr Ae vme A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' (Z_to_bv 64 0x183cc) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 0x1839c) m al_rom) md) S.
Proof.
  intros n. induction n as [|n IH];
    intros C Ar Ae A m0 m md vme regs regs0 s pp kb pa parr ba barr w h i pb pixes datad S
      Hn Hi CK HW Hs16 Hlo Hhi R2 R4 R8 R9 R18 R19 RREST ST INV RT K; [lia|].
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val as HLS. unfold PAD_WIN, ALLOC_STACK in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof ST as (Rpa & Rparr & Rba & Rbarr & A0pa & A0parr & A0ba & A0barr & Arpa & Arparr & Arba & Arbarr & Arpb & A0pb & NEpb & Hw & Hh & DIST & NPA & NPB & NPBA).
  destruct INV as (F8 & F16 & F24 & F32 & F40 & SL & SUBr & Lpa & Lparr & Lba & Lbarr & Hn10 & Hparr & Hba & B0 & B1 & Bbarr & MEM & GONE & EQe & PD).
  destruct (blk_range C A m md (Z_to_bv 64 pa) 32 CK HW Lpa ltac:(lia)) as [Gpa TOPpa]. rewrite u_Z2bv in Gpa, TOPpa by lia.
  destruct (blk_range C A m md (Z_to_bv 64 parr) 80 CK HW Lparr ltac:(lia)) as [Gparr TOPparr]. rewrite u_Z2bv in Gparr, TOPparr by lia.
  destruct (blk_range C A m md (Z_to_bv 64 ba) 24 CK HW Lba ltac:(lia)) as [Gba TOPba]. rewrite u_Z2bv in Gba, TOPba by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lparr) as (_ & ALparr & _). rewrite u_Z2bv in ALparr by lia.
  pose proof (pdl_disj A m (m_vmmaps md) _ _ 32 80 (w_inv _ _ _ _ HW) Lpa Lparr ltac:(lia)) as D1. rewrite !u_Z2bv in D1 by lia.
  pose proof (pdl_disj A m (m_vmmaps md) _ _ 24 80 (w_inv _ _ _ _ HW) Lba Lparr ltac:(lia)) as D2. rewrite !u_Z2bv in D2 by lia.
  assert (RPOS : (0 < wpl_of w 8 * h)%Z).
  { apply Z.mul_pos_pos; [|lia]. unfold wpl_of. apply Z.div_str_pos. lia. }
  pose proof (MEM i ltac:(lia)) as (Hp4k & Hptop & Hd4k & Hdtop & NEpd & Arp & Ard & A0p & A0d & Lp & Ld & PX & Rslot).
  destruct (notin_PA4 _ _ _ _ _ (proj1 (NPA i ltac:(lia)))) as (Pa1 & Pa2 & Pa3 & Pa4).
  destruct (notin_PA4 _ _ _ _ _ (proj2 (NPA i ltac:(lia)))) as (Da1 & Da2 & Da3 & Da4).
  assert (ALs : ((parr + 8 * i) mod 8 = 0)%Z).
  { apply mod16_plus_mod8; [exact ALparr|]. rewrite Z.mul_comm. apply Z.mod_mul. lia. }
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) | exact (pd_L al_rom fx regs m s pa parr i ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hparr R2 R8 R18) |].
  intros fin (rL & ML & -> & -> & L1 & L2 & L10 & AGL).
  replace (Z_to_bv 64 PC_pixDestroy) with (0x1982c : word) by (apply bv_eq; reflexivity).
  apply (pixDestroy_free_W C A m md rL (s - 48) (parr + 8 * i) (pixes i) (4 * (wpl_of w 8 * h)) (hdv w h 8 0 (datad i))
           (Some (Z_to_bv 64 parr, 80%Z)) (getr rL 1) S CK HW L2).
  - rewrite <- Zminus_mod_idemp_l, Hs16. reflexivity.
  - unfold ALLOC_STACK. lia.
  - lia.
  - reflexivity.
  - rewrite L1. red. apply bv_eq. reflexivity.
  - csr. reflexivity.
  - exact ALs.
  - exact L10.
  - unfold slotok. cbv beta iota. rewrite u_Z2bv by lia. split; [exact Lparr|]. split; [exact A0parr|]. lia.
  - exact Rslot.
  - exact PX.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact Lp.
  - exact A0p.
  - exact Ld.
  - exact A0d.
  - lia.
  - exact (not_eq_sym NEpd).
  - intros p k E. injection E as <- <-. change (p_data (hdv w h 8 0 (datad i))) with (datad i).
    split; apply not_eq_sym; assumption.
  - intros A1 m1 vm1 r1 HW1 CS1 Lp1 Ld1 LEQ SUB1 PD1 RS1 RT1.
    change (p_data (hdv w h 8 0 (datad i))) with (datad i) in Ld1, LEQ.
    rewrite L1.
    assert (NONE1 : forall q, live A q = None -> live A1 q = None).
    { intros q Lq. destruct (live A1 q) as [k|] eqn:E; [|reflexivity]. rewrite (SUB1 q k E) in Lq. discriminate. }
    assert (Lpa1 : live A1 (Z_to_bv 64 pa) = Some 32%Z) by (rewrite LEQ by (apply not_eq_sym; assumption); exact Lpa).
    assert (Lparr1 : live A1 (Z_to_bv 64 parr) = Some 80%Z) by (rewrite LEQ by (apply not_eq_sym; assumption); exact Lparr).
    assert (Lba1 : live A1 (Z_to_bv 64 ba) = Some 24%Z) by (rewrite LEQ by (apply not_eq_sym; assumption); exact Lba).
    assert (Lbarr1 : live A1 (Z_to_bv 64 barr) = Some 80%Z) by (rewrite LEQ by (apply not_eq_sym; assumption); exact Lbarr).
    assert (RA : forall a : Z, (s - 48 <= a)%Z -> (a + 8 <= s)%Z -> rdn SEGS m1 (Z_to_bv 64 a) 8 = rdn SEGS m (Z_to_bv 64 a) 8).
    { intros a Ha1 Ha2. rewrite <- p16_segs. apply (POSTD_rdn_above C A1 (s - 48) (parr + 8 * i) m m1 a 8 CK PD1); lia. }
    assert (RB : forall (q k a : Z) (n0 : nat), live A1 (Z_to_bv 64 q) = Some k -> (0 <= q < 2 ^ 64)%Z -> (q <= a)%Z ->
                 (a + Z.of_nat n0 <= q + k)%Z -> (q + k <= 2 ^ 64)%Z -> (parr + 8 * i + 8 <= a \/ a + Z.of_nat n0 <= parr + 8 * i)%Z ->
                 rdn SEGS m1 (Z_to_bv 64 a) n0 = rdn SEGS m (Z_to_bv 64 a) n0).
    { intros q k a n0 Lq Hq H1 H2 H3 H4.
      apply (POSTD_rdn_blk C A1 (s - 48) (parr + 8 * i) m m1 (Z_to_bv 64 q) k a n0 PD1 Lq); rewrite ?u_Z2bv by lia; lia. }
    assert (INV1 : pd_invM C Ar Ae A1 m0 m1 regs0 s pp kb pb pa parr ba barr w h (i + 1) pixes datad).
    { unfold pd_invM. repeat (lazymatch goal with |- _ /\ _ => split end).
      - rewrite (RA (s - 8)%Z) by lia. exact F8.
      - rewrite (RA (s - 16)%Z) by lia. exact F16.
      - rewrite (RA (s - 24)%Z) by lia. exact F24.
      - rewrite (RA (s - 32)%Z) by lia. exact F32.
      - rewrite (RA (s - 40)%Z) by lia. exact F40.
      - apply (slot_keep C A A1 s pp _ SL). intros p k E. injection E as <- <-.
        destruct (NPB i ltac:(lia)) as [N1 N2]. exact (LEQ pb N1 N2).
      - intros q k Lq. rewrite LEQ; [exact (SUBr q k Lq) | intros ->; congruence | intros ->; congruence].
      - exact Lpa1.
      - exact Lparr1.
      - exact Lba1.
      - exact Lbarr1.
      - rewrite (RB pa 32%Z pa 4%nat Lpa1) by lia. exact Hn10.
      - rewrite (RB pa 32%Z (pa + 16)%Z 8%nat Lpa1) by lia. exact Hparr.
      - rewrite (RB pa 32%Z (pa + 24)%Z 8%nat Lpa1) by lia. exact Hba.
      - rewrite (RB ba 24%Z ba 4%nat Lba1) by lia. exact B0.
      - rewrite (RB ba 24%Z (ba + 8)%Z 4%nat Lba1) by lia. exact B1.
      - rewrite (RB ba 24%Z (ba + 16)%Z 8%nat Lba1) by lia. exact Bbarr.
      - intros j Hj.
        destruct (MEM j ltac:(lia)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
        destruct (DIST i j ltac:(lia) ltac:(lia)) as (Dd & Dp & Dpd & Ddp).
        pose proof (pdl_disj A m (m_vmmaps md) _ _ 64 80 (w_inv _ _ _ _ HW) Q10 Lparr ltac:(lia)) as D3. rewrite !u_Z2bv in D3 by lia.
        assert (Lpj : live A1 (Z_to_bv 64 (pixes j)) = Some 64%Z).
        { rewrite LEQ; [exact Q10 | apply zneq_w; lia | apply zneq_w; lia]. }
        assert (Ldj : live A1 (Z_to_bv 64 (datad j)) = Some (4 * (wpl_of w 8 * h))%Z).
        { rewrite LEQ; [exact Q11 | apply zneq_w; lia | apply zneq_w; lia]. }
        unfold pd_mem. repeat (lazymatch goal with |- _ /\ _ => split end); try assumption.
        + apply (PIXat_frame m); [exact Q12|]. intros x Hx.
          apply (POSTD_blk_byte C A1 (s - 48) (parr + 8 * i) m m1 (Z_to_bv 64 (pixes j)) 64 x PD1 Lpj); rewrite ?u_Z2bv by lia; [lia|].
          unfold inslot. lia.
        + rewrite (RB parr 80%Z (parr + 8 * j)%Z 8%nat Lparr1) by lia. exact Q13.
      - intros j Hj. destruct (Z.eq_dec j i) as [-> | Nji]; [split; assumption|].
        destruct (GONE j ltac:(lia)) as [G1 G2]. split; [apply NONE1; exact G1 | apply NONE1; exact G2].
      - intros q NQ. rewrite LEQ.
        + apply EQe. intros (j & Hj & Hq). apply NQ. red. exists j. split; [lia | exact Hq].
        + intros ->. apply NQ. red. exists i. split; [lia | left; reflexivity].
        + intros ->. apply NQ. red. exists i. split; [lia | right; reflexivity].
      - intros Az SUBaz Lzpa Lzparr.
        assert (SUBzA : sub_live Az A) by (intros q k Lq; exact (SUB1 q k (SUBaz q k Lq))).
        eapply POSTD_trans; [exact (PD Az SUBzA Lzpa Lzparr) |].
        apply (POSTD_mono C Az (s - 48) s); [lia|].
        apply (POSTD_of_POSTM C Az Az (s - 48) pp m m1); [| apply sub_live_refl].
        apply (POSTD_POSTM_blk C Az A1 m1 (with_vmmaps vm1 md) (Z_to_bv 64 parr) 80 (s - 48) (parr + 8 * i) m m1 CK HW1 Lparr1);
          [rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; lia | exact Lzparr | exact SUBaz
          | exact (POSTD_sub C A1 Az (s - 48) (parr + 8 * i) m m1 SUBaz PD1)]. }
    assert (RT2 : roomtr Ae vme A1 vm1 0 0) by (exact (roomtr_trans _ _ _ _ _ _ _ _ _ _ RT RT1 ltac:(lia) ltac:(lia))).
    assert (E2 : getr r1 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (E8 : getr r1 8 = Z_to_bv 64 pa) by (csr; reflexivity).
    assert (E18 : getr r1 18 = Z_to_bv 64 (8 * i)) by (csr; reflexivity).
    assert (E19 : getr r1 19 = Z_to_bv 64 i) by (csr; reflexivity).
    assert (ER : forall r, In r pd_rest -> getr r1 r = getr regs0 r).
    { intros r Hr. pose proof (RREST r Hr) as Er. unfold pd_rest in Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr];
        [rewrite (cs_rest_of_kept rL r1 CS1) by in_lit; rewrite (AGL _) by notin_lit; exact Er |]).
      destruct Hr. }
    assert (RN1 : rdn SEGS m1 (Z_to_bv 64 pa) 4 = Some (Z_to_le_bytes 4 10)) by (rewrite (RB pa 32%Z pa 4%nat Lpa1) by lia; exact Hn10).
    destruct (Z.eq_dec i 9) as [E9 | N9].
    + subst i.
      eapply rz_reach; [exact (w_pure _ _ _ _ HW1) | exact (pd_Ml al_rom fx r1 m1 s pa ltac:(lia) ltac:(lia) ltac:(lia) RN1 E2 E8 E18 E19) |].
      intros fin (r2 & M2 & -> & -> & S2 & S8 & AG2).
      apply (K A1 m1 vm1 r2 HW1 S2); [csr; reflexivity | exact S8 | csr; reflexivity | | exact INV1 | exact RT2].
      intros r Hr. pose proof (ER r Hr) as Er. unfold pd_rest in Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr]; [rewrite (AG2 _) by notin_lit; exact Er |]).
      destruct Hr.
    + eapply rz_reach; [exact (w_pure _ _ _ _ HW1) | exact (pd_Mm al_rom fx r1 m1 s pa i ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RN1 E2 E8 E18 E19) |].
      intros fin (r2 & M2 & -> & -> & S2 & S8 & S18 & S19 & AG2).
      apply (IH C Ar Ae A1 m0 m1 (with_vmmaps vm1 md) vme r2 regs0 s pp kb pa parr ba barr w h (i + 1)%Z pb pixes datad S);
        [lia | lia | exact CK | exact HW1 | exact Hs16 | unfold PAD_WIN, ALLOC_STACK; lia | exact Hhi | exact S2 | csr; reflexivity
        | exact S8 | csr; reflexivity | exact S18 | exact S19 | | exact ST | exact INV1 | rewrite with_vmmaps_vmmaps; exact RT2 | ].
      * intros r Hr. pose proof (ER r Hr) as Er. unfold pd_rest in Hr. cbn [In] in Hr.
        repeat (destruct Hr as [<- | Hr]; [rewrite (AG2 _) by notin_lit; exact Er |]).
        destruct Hr.
      * intros A' m' vm' regs' HW'. rewrite with_vmmaps_twice in HW' |- *. exact (K A' m' vm' regs' HW').
Qed.

Lemma pdw_apart : forall C A m md (p q : word) (n k : Z), W C A m md ->
  live A p = Some n -> live A q = Some k -> p <> q -> (0 <= n)%Z -> (0 <= k)%Z ->
  (u p + n <= u q \/ u q + k <= u p)%Z.
Proof.
  intros C A m md p q n k HW Lp Lq NE Hn Hk.
  destruct (ai_live_disjoint A m (m_vmmaps md) p n q k (w_inv _ _ _ _ HW) Lp Lq NE) as [X|X];
    [left; pose proof (round16_ge n Hn); lia | right; pose proof (round16_ge k Hk); lia].
Qed.
Lemma pdw_neq_size : forall (A : AS) (p q : word) (n k : Z), live A p = Some n -> live A q = Some k -> n <> k -> p <> q.
Proof. intros A p q n k Lp Lq NE E. subst q. rewrite Lp in Lq. injection Lq as E. exact (NE E). Qed.
Lemma pdw_sub_free : forall (A A' : AS) (p : word), live A' p = None -> (forall q, q <> p -> live A' q = live A q) -> sub_live A' A.
Proof.
  intros A A' p N K q k Lq. assert (Nq : q <> p) by (intros ->; rewrite N in Lq; discriminate).
  rewrite <- (K q Nq). exact Lq.
Qed.
Lemma pdw_ag_keep : forall (L : list reg) regs regs' (r : reg) (v : word),
  regs_agree (fun x => In x L) regs regs' -> existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = false ->
  getr regs r = v -> getr regs' r = v.
Proof.
  intros L regs regs' r v AG E H. rewrite AG; [exact H|]. intros Hin.
  assert (T : existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = true).
  { apply existsb_exists. exists r. split; [exact Hin | apply Z.eqb_refl]. }
  congruence.
Qed.
Ltac pak AG := apply (pdw_ag_keep _ _ _ _ _ AG); [vm_compute; reflexivity |].
Lemma pdw_rest_ag : forall (L : list reg) regs regs', regs_agree (fun x => In x L) regs regs' ->
  forallb (fun x => negb (existsb (fun y => Z.eqb (bv_unsigned y) (bv_unsigned x)) L)) pd_rest = true ->
  forall r, In r pd_rest -> getr regs' r = getr regs r.
Proof.
  intros L regs regs' AG B r Hr. rewrite AG; [reflexivity|]. intros Hin.
  rewrite forallb_forall in B. specialize (B r Hr). apply negb_true_iff in B.
  assert (T : existsb (fun y => Z.eqb (bv_unsigned y) (bv_unsigned r)) L = true).
  { apply existsb_exists. exists r. split; [exact Hin | apply Z.eqb_refl]. }
  congruence.
Qed.
Lemma pdw_rest_cs : forall R R', cs_kept R R' -> forall r, In r pd_rest -> getr R' r = getr R r.
Proof.
  intros R R' K r Hr. apply (cs_rest_of_kept R R' K r). unfold pd_rest in Hr. unfold cs_rest. cbn [In] in Hr |- *. tauto.
Qed.
Lemma pdw_rinv_out : forall (R : list (Z * Z)) (m M' : word -> option byte) (a : word), rinv R m M' ->
  (forall r, In r R -> ~ (fst r <= u a < fst r + snd r)%Z) -> M' a = m a.
Proof. intros R m M' a [_ H] D. apply H. intros r Hr. unfold inreg. exact (D r Hr). Qed.
Lemma pdw_rdn_keep : forall (m M' : word -> option byte) (q : word) (k a : Z) (n : nat),
  (forall x : word, (u q <= u x < u q + k)%Z -> M' x = m x) -> (u q <= a)%Z -> (a + Z.of_nat n <= u q + k)%Z -> (u q + k < 2 ^ 64)%Z ->
  rdn SEGS M' (Z_to_bv 64 a) n = rdn SEGS m (Z_to_bv 64 a) n.
Proof.
  intros m M' q k a n K H1 H2 H3. pose proof (u64_range q).
  apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply K; lia.
Qed.
Ltac pdz := cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Ltac rdisj := let r := fresh "r" in let Hr := fresh "Hr" in
  first [ pdz | intros r Hr; cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try contradiction; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Theorem pixaDestroy10_W : forall C Ar A m md regs (s pp kb pa parr ba barr w h : Z) (pb : word) (pixes datad : Z -> Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PAD_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 -> (pp mod 8 = 0)%Z -> getr regs 10 = Z_to_bv 64 pp ->
  slotok C A s pp (Some (pb, kb)) -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pa) ->
  sub_live Ar A -> pixa_cells m pa parr ba barr 10 ->
  live A (Z_to_bv 64 pa) = Some 32%Z -> live A (Z_to_bv 64 parr) = Some 80%Z -> live A (Z_to_bv 64 ba) = Some 24%Z -> live A (Z_to_bv 64 barr) = Some 80%Z ->
  pd_static C Ar pb pa parr ba barr w h pixes datad ->
  (forall j, (0 <= j < 10)%Z -> pd_mem C Ar A m parr w h j (pixes j) (datad j)) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     (forall q, pd_gone pa parr ba barr pixes datad q -> live A' q = None) ->
     (forall q, ~ pd_gone pa parr ba barr pixes datad q -> live A' q = live A q) -> sub_live Ar A' ->
     POSTD C A' s pp m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 0x18340) m al_rom) md) S.
Proof.
  intros C Ar A m md regs s pp kb pa parr ba barr w h pb pixes datad ret S CK HW H2 Hs16 Hstk Hsc H1 Hret H4 ALpp H10 SL Rpp SLA PC Lpa Lparr Lba Lbarr PS PMj POST.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. pose proof LSTK_val as LS. unfold PAD_WIN, ALLOC_STACK in Hstk.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PC as (Cn & Cna & Crc & Cparr & Cba & Cbn & Cbna & Cbrc & Cbarr). rewrite Z.add_0_r in Cn, Cbn.
  pose proof PS as (Rpa & Rparr & Rba & Rbarr & L0pa & L0parr & L0ba & L0barr & LRpa & LRparr & LRba & LRbarr & LRpb & L0pb & NEpr & Hw1 & Hh1 & DIST & NPA & NPB & NPB4).
  destruct (blk_range C A m md (Z_to_bv 64 pa) 32 CK HW Lpa ltac:(lia)) as [Gpa Tpa]. rewrite u_Z2bv in Gpa, Tpa by lia.
  destruct (blk_range C A m md (Z_to_bv 64 parr) 80 CK HW Lparr ltac:(lia)) as [Gparr Tparr]. rewrite u_Z2bv in Gparr, Tparr by lia.
  destruct (blk_range C A m md (Z_to_bv 64 ba) 24 CK HW Lba ltac:(lia)) as [Gba Tba]. rewrite u_Z2bv in Gba, Tba by lia.
  destruct (blk_range C A m md (Z_to_bv 64 barr) 80 CK HW Lbarr ltac:(lia)) as [Gbarr Tbarr]. rewrite u_Z2bv in Gbarr, Tbarr by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lpa) as (_ & ALpa & _). rewrite u_Z2bv in ALpa by lia.
  assert (ALpa8 : ((pa + 24) mod 8 = 0)%Z) by (apply mod16_plus_mod8; [exact ALpa | reflexivity]).
  assert (NEpa_parr : Z_to_bv 64 pa <> Z_to_bv 64 parr) by (apply (pdw_neq_size A _ _ 32 80 Lpa Lparr); lia).
  assert (NEpa_ba : Z_to_bv 64 pa <> Z_to_bv 64 ba) by (apply (pdw_neq_size A _ _ 32 24 Lpa Lba); lia).
  assert (NEpa_barr : Z_to_bv 64 pa <> Z_to_bv 64 barr) by (apply (pdw_neq_size A _ _ 32 80 Lpa Lbarr); lia).
  assert (NEparr_ba : Z_to_bv 64 parr <> Z_to_bv 64 ba) by (apply (pdw_neq_size A _ _ 80 24 Lparr Lba); lia).
  assert (NEparr_barr : Z_to_bv 64 parr <> Z_to_bv 64 barr) by (apply zneq_w; lia).
  assert (NEba_barr : Z_to_bv 64 ba <> Z_to_bv 64 barr) by (apply (pdw_neq_size A _ _ 24 80 Lba Lbarr); lia).
  pose proof SL as SL0. cbn [slotok] in SL0. destruct SL0 as (Lpb & L0pb' & Hpb1 & Hpb2).
  destruct (notin_PA4 pb pa parr ba barr NPB4) as (NBpa & NBparr & NBba & NBbarr).
  destruct (slot_range C A m md s pp _ CK HW SL ltac:(lia)) as [Hpp4k Hpptop].
  assert (DJs : (pp + 8 <= s - 48 \/ s <= pp)%Z).
  { destruct (slot_where C A m md s pp _ CK HW SL ltac:(lia)) as [[X _] | (_ & X & Y)]; lia. }
  assert (DJp : (pp + 8 <= pa \/ pa + 32 <= pp)%Z).
  { destruct (pdw_apart C A m md pb (Z_to_bv 64 pa) kb 32 HW Lpb Lpa NBpa ltac:(lia) ltac:(lia)) as [X | X]; rewrite u_Z2bv in X by lia; lia. }
  assert (SOKf : store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true) by (apply (W_sok_win C A m md); [exact CK | exact HW | lia | cbn; lia]).
  assert (SOKrc : store_ok SEGS m (Z_to_bv 64 (pa + 8)) 4 = true).
  { apply (sok_cell4 C A m md (Z_to_bv 64 pa) 32); [exact CK | exact HW | exact Lpa | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; lia]. }
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) | apply (pd_A al_rom fx regs m s pp pa ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALpa ALpp DJs DJp Rpp Cn Crc SOKf SOKrc H2 H10) |].
  intros fin (r1 & M1 & -> & RI1 & Rrc1 & F8 & F16 & F24 & F32 & F40 & E2 & E8 & E9 & E18 & E19 & AG1).
  assert (LR1 : forall Az, sub_live Az A -> live Az (Z_to_bv 64 pa) = None -> local_regions C A Az s [((s - 40)%Z, 40%Z); ((pa + 8)%Z, 4%Z)]).
  { intros Az SAz Naz. unfold local_regions. constructor; [left; cbn [fst snd]; lia |]. constructor; [| constructor].
    right. exists (Z_to_bv 64 pa), 32%Z. rewrite u_Z2bv by lia. cbn [fst snd].
    split; [exact Lpa|]. split; [exact Naz|]. split; [exact L0pa | lia]. }
  destruct (rinv_WP2 C Ar A m md M1 _ s CK HW SLA Hsc RI1 (LR1 Ar SLA LRpa)) as (W1 & _).
  assert (KEEPb : forall (q : word) k, live A q = Some k -> q <> Z_to_bv 64 pa -> forall x : word, (u q <= u x < u q + k)%Z -> M1 x = m x).
  { intros q k Lq Nq x Hx. destruct (Z_lt_le_dec 0 k) as [Kp | Kn]; [| exfalso; lia].
    destruct (blk_range C A m md q k CK HW Lq Kp) as [Gq Tq].
    destruct (pdw_apart C A m md q (Z_to_bv 64 pa) k 32 HW Lq Lpa Nq ltac:(lia) ltac:(lia)) as [X | X]; rewrite u_Z2bv in X by lia;
      apply (pdw_rinv_out _ m M1 x RI1); intros r Hr; cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [fst snd]; lia. }
  assert (PM1 : forall j, (0 <= j < 10)%Z -> pd_mem C Ar A M1 parr w h j (pixes j) (datad j)).
  { intros j Hj. destruct (PMj j Hj) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & PXj & Rj).
    destruct (NPA j Hj) as [NA1 NA2]. destruct (notin_PA4 _ _ _ _ _ NA1) as (Np1 & _).
    unfold pd_mem. do 11 (split; [assumption|]). split.
    - apply (PIXat_frame m M1 (pixes j) _ PXj). intros x Hx. apply (KEEPb (Z_to_bv 64 (pixes j)) 64%Z G10 Np1 x). rewrite u_Z2bv by lia. exact Hx.
    - rewrite (pdw_rdn_keep m M1 (Z_to_bv 64 parr) 80 (parr + 8 * j) 8 (KEEPb _ _ Lparr (not_eq_sym NEpa_parr))) by (rewrite u_Z2bv by lia; pdz). exact Rj. }
  assert (INV0 : pd_invM C Ar A A m M1 regs s pp kb pb pa parr ba barr w h 0 pixes datad).
  { unfold pd_invM.
    split; [exact F8|]. split; [exact F16|]. split; [exact F24|]. split; [exact F32|]. split; [exact F40|].
    split; [exact SL|]. split; [exact SLA|].
    split; [exact Lpa|]. split; [exact Lparr|]. split; [exact Lba|]. split; [exact Lbarr|].
    split; [rewrite (rinv_rdn SEGS _ m M1 pa 4 RI1) by rdisj; exact Cn|].
    split; [rewrite (rinv_rdn SEGS _ m M1 (pa + 16) 8 RI1) by rdisj; exact Cparr|].
    split; [rewrite (rinv_rdn SEGS _ m M1 (pa + 24) 8 RI1) by rdisj; exact Cba|].
    split; [rewrite (pdw_rdn_keep m M1 (Z_to_bv 64 ba) 24 ba 4 (KEEPb _ _ Lba (not_eq_sym NEpa_ba))) by (rewrite u_Z2bv by lia; pdz); exact Cbn|].
    split; [rewrite (pdw_rdn_keep m M1 (Z_to_bv 64 ba) 24 (ba + 8) 4 (KEEPb _ _ Lba (not_eq_sym NEpa_ba))) by (rewrite u_Z2bv by lia; pdz); exact Cbrc|].
    split; [rewrite (pdw_rdn_keep m M1 (Z_to_bv 64 ba) 24 (ba + 16) 8 (KEEPb _ _ Lba (not_eq_sym NEpa_ba))) by (rewrite u_Z2bv by lia; pdz); exact Cbarr|].
    split; [intros j Hj; apply PM1; lia|].
    split; [intros j Hj; exfalso; lia|].
    split; [intros q _; reflexivity|].
    intros Az SAz Npa Nparr. destruct (rinv_WP2 C Az A m md M1 _ s CK HW SAz Hsc RI1 (LR1 Az SAz Npa)) as (_ & PMz).
    exact (POSTD_of_POSTM C Az Az s pp m M1 PMz (fun q k X => X)). }
  apply (pda_loop_W 10 C Ar A A m M1 md (m_vmmaps md) r1 regs s pp kb pa parr ba barr w h 0 pb pixes datad S
           ltac:(reflexivity) ltac:(lia) CK W1 Hs16 ltac:(unfold PAD_WIN, ALLOC_STACK; lia) Hsc E2
           ltac:(pak AG1; exact H4) E8 E9 E18 E19 (pdw_rest_ag _ regs r1 AG1 ltac:(vm_compute; reflexivity)) PS INV0 (roomtr_refl A (m_vmmaps md) 0 0 ltac:(lia) ltac:(lia))).
  intros A' m' vm' rL W' L2 L4 L8 L9 LR INV RT'.
  destruct INV as (G8 & G16 & G24 & G32 & G40 & SL' & SLA' & Lpa' & Lparr' & Lba' & Lbarr' & Rn' & Rparr' & Rba' & Rbn' & Rbrc' & Rbarr' & PMe & DEADj & LEQ' & PDz).
  eapply rz_reach; [exact (w_pure _ _ _ _ W') | apply (pd_B al_rom fx rL m' s pa parr ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Rparr' L2 L8) |].
  intros fin (rB & MB & -> & -> & B1 & B2 & B8 & B10 & AGB).
  apply (W_free16 C A' m' (with_vmmaps vm' md) rB (Z_to_bv 64 parr) (Z_to_bv 64 0x183d4) 80 (s - 48) S CK W' B10 Lparr' L0parr B1
           ltac:(red; apply bv_eq; reflexivity) ltac:(pak AGB; exact L4) B2 ltac:(rewrite Zminus_mod, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r1' W1' CK1 N1 K1 PM1' RT1.
  rewrite with_vmmaps_twice in W1' |- *. rewrite with_vmmaps_vmmaps in RT1.
  assert (C2 : getr r1' 2 = Z_to_bv 64 (s - 48)) by (rewrite (cs_kept_get _ _ 2%bv CK1) by (left; reflexivity); exact B2).
  assert (C8 : getr r1' 8 = Z_to_bv 64 pa) by (rewrite (cs_kept_get _ _ 8%bv CK1) by (right; right; right; left; reflexivity); exact B8).
  assert (Lpa1 : live A1 (Z_to_bv 64 pa) = Some 32%Z) by (rewrite (K1 _ NEpa_parr); exact Lpa').
  assert (Lba1 : live A1 (Z_to_bv 64 ba) = Some 24%Z) by (rewrite (K1 _ (not_eq_sym NEparr_ba)); exact Lba').
  assert (Lbarr1 : live A1 (Z_to_bv 64 barr) = Some 80%Z) by (rewrite (K1 _ (not_eq_sym NEparr_barr)); exact Lbarr').
  assert (KPa : forall x : word, (u (Z_to_bv 64 pa) <= u x < u (Z_to_bv 64 pa) + 32)%Z -> m1 x = m' x).
  { intros x Hx. exact (LIVK_byte A1 m' m1 _ 32 x (proj2 PM1') Lpa1 Hx). }
  assert (KBa : forall x : word, (u (Z_to_bv 64 ba) <= u x < u (Z_to_bv 64 ba) + 24)%Z -> m1 x = m' x).
  { intros x Hx. exact (LIVK_byte A1 m' m1 _ 24 x (proj2 PM1') Lba1 Hx). }
  assert (RBa1 : rdn SEGS m1 (Z_to_bv 64 (pa + 24)) 8 = Some (Z_to_le_bytes 8 ba)).
  { rewrite (pdw_rdn_keep m' m1 _ 32 (pa + 24) 8 KPa) by (rewrite u_Z2bv by lia; pdz). exact Rba'. }
  assert (Rbn1 : rdn SEGS m1 (Z_to_bv 64 ba) 4 = Some (Z_to_le_bytes 4 0)).
  { rewrite (pdw_rdn_keep m' m1 _ 24 ba 4 KBa) by (rewrite u_Z2bv by lia; pdz). exact Rbn'. }
  assert (Rbrc1 : rdn SEGS m1 (Z_to_bv 64 (ba + 8)) 4 = Some (Z_to_le_bytes 4 1)).
  { rewrite (pdw_rdn_keep m' m1 _ 24 (ba + 8) 4 KBa) by (rewrite u_Z2bv by lia; pdz). exact Rbrc'. }
  assert (Rbarr1 : rdn SEGS m1 (Z_to_bv 64 (ba + 16)) 8 = Some (Z_to_le_bytes 8 barr)).
  { rewrite (pdw_rdn_keep m' m1 _ 24 (ba + 16) 8 KBa) by (rewrite u_Z2bv by lia; pdz). exact Rbarr'. }
  eapply rz_reach; [exact (w_pure _ _ _ _ W1') | apply (pd_C al_rom fx r1' m1 s pa ltac:(lia) ltac:(lia) ltac:(lia) C2 C8) |].
  intros fin (rC & MC & -> & -> & Cr1 & Cr2 & Cr8 & Cr10 & AGC).
  apply (boxaDestroy0_W C A1 m1 (with_vmmaps vm1 md) rC (s - 48) (pa + 24) 32 ba barr (Z_to_bv 64 pa) (Z_to_bv 64 0x183dc) S
           CK W1' Cr2 ltac:(rewrite Zminus_mod, Hs16; reflexivity) ltac:(unfold BXD_WIN, ALLOC_STACK; lia) ltac:(lia) Cr1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(pak AGC; rewrite (cs_kept_get _ _ 4%bv CK1) by (right; right; left; reflexivity); pak AGB; exact L4)
           ALpa8 Cr10
           ltac:(cbn [slotok]; rewrite u_Z2bv by lia; split; [exact Lpa1 |]; split; [exact L0pa | lia])
           RBa1 Rba Rbarr Lba1 L0ba Lbarr1 L0barr Rbn1 Rbrc1 Rbarr1 NEpa_ba NEpa_barr).
  intros A2 m2 vm2 r2 W2 CK2 N2a N2b K2 SUB21 PD2 Rpp2 RT2.
  rewrite with_vmmaps_twice in W2 |- *. rewrite with_vmmaps_vmmaps in RT2.
  assert (D2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (rewrite (cs_kept_get _ _ 2%bv CK2) by (left; reflexivity); exact Cr2).
  assert (D8 : getr r2 8 = Z_to_bv 64 pa) by (rewrite (cs_kept_get _ _ 8%bv CK2) by (right; right; right; left; reflexivity); pak AGC; exact C8).
  assert (Lpa2 : live A2 (Z_to_bv 64 pa) = Some 32%Z) by (rewrite (K2 _ NEpa_ba NEpa_barr); exact Lpa1).
  eapply rz_reach; [exact (w_pure _ _ _ _ W2) | apply (pd_D al_rom fx r2 m2 s pa ltac:(lia) ltac:(lia) ltac:(lia) D2 D8) |].
  intros fin (rD & MD & -> & -> & Dr1 & Dr2 & Dr10 & AGD).
  apply (W_free16 C A2 m2 (with_vmmaps vm2 md) rD (Z_to_bv 64 pa) (Z_to_bv 64 0x183e4) 32 (s - 48) S CK W2 Dr10 Lpa2 L0pa Dr1
           ltac:(red; apply bv_eq; reflexivity)
           ltac:(pak AGD; rewrite (cs_kept_get _ _ 4%bv CK2) by (right; right; left; reflexivity); pak AGC;
                 rewrite (cs_kept_get _ _ 4%bv CK1) by (right; right; left; reflexivity); pak AGB; exact L4)
           Dr2 ltac:(rewrite Zminus_mod, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A3 m3 vm3 r3 W3 CK3 N3 K3 PM3 RT3.
  rewrite with_vmmaps_twice in W3 |- *. rewrite with_vmmaps_vmmaps in RT3.
  assert (SUB1 : sub_live A1 A') by (exact (pdw_sub_free A' A1 _ N1 K1)).
  assert (SUB32 : sub_live A3 A2) by (exact (pdw_sub_free A2 A3 _ N3 K3)).
  assert (SUB31 : sub_live A3 A1) by (exact (sub_live_trans _ _ _ SUB32 SUB21)).
  assert (SUB3' : sub_live A3 A') by (exact (sub_live_trans _ _ _ SUB31 SUB1)).
  assert (N3parr : live A3 (Z_to_bv 64 parr) = None).
  { rewrite (K3 _ (not_eq_sym NEpa_parr)), (K2 _ NEparr_ba NEparr_barr). exact N1. }
  assert (N3ba : live A3 (Z_to_bv 64 ba) = None) by (rewrite (K3 _ (not_eq_sym NEpa_ba)); exact N2a).
  assert (N3barr : live A3 (Z_to_bv 64 barr) = None) by (rewrite (K3 _ (not_eq_sym NEpa_barr)); exact N2b).
  assert (KK : forall q, q <> Z_to_bv 64 pa -> q <> Z_to_bv 64 parr -> q <> Z_to_bv 64 ba -> q <> Z_to_bv 64 barr -> live A3 q = live A' q).
  { intros q X1 X2 X3 X4. rewrite (K3 _ X1), (K2 _ X3 X4), (K1 _ X2). reflexivity. }
  assert (SL3 : slotok C A3 s pp (Some (pb, kb))).
  { apply (slot_keep C A' A3 s pp _ SL'). intros p n E. injection E as <- <-. exact (KK pb NBpa NBparr NBba NBbarr). }
  assert (Lpb3 : live A3 pb = Some kb) by (pose proof SL3 as X; cbn [slotok] in X; exact (proj1 X)).
  assert (G2 : getr r3 2 = Z_to_bv 64 (s - 48)) by (rewrite (cs_kept_get _ _ 2%bv CK3) by (left; reflexivity); exact Dr2).
  assert (G9 : getr r3 9 = Z_to_bv 64 pp).
  { rewrite (cs_kept_get _ _ 9%bv CK3) by (right; right; right; right; left; reflexivity). pak AGD.
    rewrite (cs_kept_get _ _ 9%bv CK2) by (right; right; right; right; left; reflexivity). pak AGC.
    rewrite (cs_kept_get _ _ 9%bv CK1) by (right; right; right; right; left; reflexivity). pak AGB. exact L9. }
  assert (FR : forall a, (s - 48 <= a)%Z -> (a + 8 <= s)%Z -> rdn SEGS m3 (Z_to_bv 64 a) 8 = rdn SEGS m' (Z_to_bv 64 a) 8).
  { intros a Ha1 Ha2.
    rewrite (FRM_rdn16 C (s - 48) m2 m3 a 8 CK (proj1 PM3)) by pdz.
    pose proof (POSTD_rdn_above C A2 (s - 48) (pa + 24) m1 m2 a 8 CK PD2 ltac:(lia) ltac:(pdz) ltac:(lia) ltac:(pdz)) as X.
    rewrite p16_segs in X. rewrite X.
    exact (FRM_rdn16 C (s - 48) m' m1 a 8 CK (proj1 PM1') ltac:(lia) ltac:(pdz) ltac:(lia)). }
  eapply rz_reach; [exact (w_pure _ _ _ _ W3) |
    apply (pd_E al_rom fx r3 m3 s pp ret (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
             ltac:(lia) ltac:(lia) ltac:(lia) DJs Hret H1
             ltac:(rewrite <- p16_segs; exact (slot_sok C A3 m3 _ s pp _ CK W3 SL3 ltac:(lia)))
             ltac:(rewrite FR by lia; exact G8) ltac:(rewrite FR by lia; exact G16) ltac:(rewrite FR by lia; exact G24)
             ltac:(rewrite FR by lia; exact G32) ltac:(rewrite FR by lia; exact G40) G2 G9) |].
  intros fin (rE & ME & -> & RIE & RppE & E2' & E8' & E9' & E18' & E19' & AGE).
  assert (SLA3 : sub_live Ar A3).
  { intros q k Lq. pose proof (SLA' q k Lq) as Lq'.
    assert (X1 : q <> Z_to_bv 64 pa) by (intros ->; rewrite LRpa in Lq; discriminate).
    assert (X2 : q <> Z_to_bv 64 parr) by (intros ->; rewrite LRparr in Lq; discriminate).
    assert (X3 : q <> Z_to_bv 64 ba) by (intros ->; rewrite LRba in Lq; discriminate).
    assert (X4 : q <> Z_to_bv 64 barr) by (intros ->; rewrite LRbarr in Lq; discriminate).
    rewrite (KK q X1 X2 X3 X4). exact Lq'. }
  assert (LRpp : local_regions C A3 Ar s [(pp, 8%Z)]).
  { unfold local_regions. constructor; [| constructor]. right. exists pb, kb. cbn [fst snd].
    split; [exact Lpb3|]. split; [exact LRpb|]. split; [exact L0pb | lia]. }
  destruct (rinv_WP2 C Ar A3 m3 (with_vmmaps vm3 md) ME _ s CK W3 SLA3 Hsc RIE LRpp) as (WE & _).
  assert (REST : forall r, In r pd_rest -> getr rE r = getr regs r).
  { intros r Hr.
    rewrite (pdw_rest_ag _ _ _ AGE ltac:(vm_compute; reflexivity) r Hr), (pdw_rest_cs _ _ CK3 r Hr),
      (pdw_rest_ag _ _ _ AGD ltac:(vm_compute; reflexivity) r Hr), (pdw_rest_cs _ _ CK2 r Hr),
      (pdw_rest_ag _ _ _ AGC ltac:(vm_compute; reflexivity) r Hr), (pdw_rest_cs _ _ CK1 r Hr),
      (pdw_rest_ag _ _ _ AGB ltac:(vm_compute; reflexivity) r Hr).
    exact (LR r Hr). }
  assert (CKF : cs_kept regs rE).
  { apply cs_kept_of_rest; [rewrite E2', H2; reflexivity | exact E8' | exact E9' |].
    intros r Hr. unfold cs_rest in Hr. cbn [In] in Hr.
    repeat destruct Hr as [<- | Hr];
      first [ exact E18' | exact E19' | contradiction | apply REST; unfold pd_rest; cbn [In]; repeat (first [left; reflexivity | right]) ]. }
  assert (PDF : POSTD C A3 s pp m ME).
  { assert (P1 : POSTD C A3 s pp m m') by (exact (PDz A3 SUB3' N3 N3parr)).
    assert (P2 : POSTD C A3 s pp m' m1).
    { apply (POSTD_of_POSTM C A1 A3 s pp m' m1); [| exact SUB31]. apply (POSTM_mono C A1 (s - 48) s); [lia | exact PM1']. }
    assert (P3 : POSTD C A3 s pp m1 m2).
    { pose proof (POSTD_sub C A2 A3 (s - 48) (pa + 24) m1 m2 SUB32 PD2) as X.
      pose proof (POSTD_POSTM_blk C A3 A1 m1 (with_vmmaps vm1 md) (Z_to_bv 64 pa) 32 (s - 48) (pa + 24) m1 m2 CK W1' Lpa1
                    ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia) N3 SUB31 X) as Y.
      apply (POSTD_of_POSTM C A3 A3 s pp m1 m2); [| exact (fun q k Z => Z)]. apply (POSTM_mono C A3 (s - 48) s); [lia | exact Y]. }
    assert (P4 : POSTD C A3 s pp m2 m3).
    { apply (POSTD_of_POSTM C A3 A3 s pp m2 m3); [| exact (fun q k Z => Z)]. apply (POSTM_mono C A3 (s - 48) s); [lia | exact PM3]. }
    assert (P5 : POSTD C A3 s pp m3 ME) by (exact (POSTD_of_rinv_slot C A3 s pp m3 ME RIE)).
    eapply POSTD_trans; [exact P1|]. eapply POSTD_trans; [exact P2|]. eapply POSTD_trans; [exact P3|].
    eapply POSTD_trans; [exact P4|]. exact P5. }
  assert (RTF : roomtr A (m_vmmaps md) A3 vm3 0 0).
  { exact (roomtr_trans _ _ _ _ _ _ _ _ _ _ (roomtr_trans _ _ _ _ _ _ _ _ _ _ (roomtr_trans _ _ _ _ _ _ _ _ _ _ RT' RT1 ltac:(lia) ltac:(lia)) RT2 ltac:(lia) ltac:(lia)) RT3 ltac:(lia) ltac:(lia)). }
  apply (POST A3 ME vm3 rE WE CKF).
  - intros q [Hq | (j & Hj & Hq)].
    + unfold PA4 in Hq. cbn [map In] in Hq. destruct Hq as [<- | [<- | [<- | [<- | []]]]]; assumption.
    + destruct (NPA j Hj) as [NA1 NA2]. destruct (DEADj j ltac:(lia)) as [Dp Dd].
      destruct Hq as [-> | ->].
      * destruct (notin_PA4 _ _ _ _ _ NA1) as (X1 & X2 & X3 & X4). rewrite (KK _ X1 X2 X3 X4). exact Dp.
      * destruct (notin_PA4 _ _ _ _ _ NA2) as (X1 & X2 & X3 & X4). rewrite (KK _ X1 X2 X3 X4). exact Dd.
  - intros q NG. assert (NI : ~ In q (PA4 pa parr ba barr)) by (intro X; apply NG; left; exact X).
    assert (NM : ~ pd_memq pixes datad 0 10 q) by (intro X; apply NG; right; exact X).
    destruct (notin_PA4 _ _ _ _ _ NI) as (X1 & X2 & X3 & X4).
    rewrite (KK q X1 X2 X3 X4). exact (LEQ' q NM).
  - exact SLA3.
  - exact PDF.
  - exact RppE.
  - exact RTF.
Qed.

End PixaDW.
