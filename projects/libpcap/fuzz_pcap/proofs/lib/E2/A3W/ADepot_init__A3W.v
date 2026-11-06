(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepotKit__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHandoffDefs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface.
From stdpp Require gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_iface AFake_init.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module ADepot_init.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepotKit__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.ADepotKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ADepot_tabscan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma tab_image : forall i, TAB <= i < NUNIQ ->
  seg_rom asegs (wa i) = Some (Z_to_bv 8 0) /\ forall m, m (wa i) = None -> wview asegs m (wa i) <> None.
Proof.
  intros i Hi. unfold TAB, NUNIQ in Hi.
  assert (U : bv_unsigned (wa i) = i) by (apply wa_unsigned; lia).
  assert (FS : find_segment asegs i 1 = Some Asan_segment_003).
  { rewrite a_find_segment_1 by lia.
    destruct (Z.leb_spec0 0x10000 i); destruct (Z.leb_spec0 (i + 1) 0x32000); cbn [andb]; try lia.
    destruct (Z.leb_spec0 0x32000 i); destruct (Z.leb_spec0 (i + 1) 0xa4000); cbn [andb]; try lia.
    destruct (Z.leb_spec0 0xa4000 i); destruct (Z.leb_spec0 (i + 1) 0xa7000); cbn [andb]; try lia.
    destruct (Z.leb_spec0 0xa7000 i); destruct (Z.leb_spec0 (i + 1) 0x603000); cbn [andb]; try lia. reflexivity. }
  assert (OFF : Z.to_N (i - Z.of_N (seg_base Asan_segment_003)) = (0xe94d8 + Z.to_N (i - 0x1904d8))%N).
  { replace (Z.of_N (seg_base Asan_segment_003)) with 0xa7000 by (vm_compute; reflexivity). lia. }
  pose proof (tab_byte_at (0xe94d8 + Z.to_N (i - 0x1904d8))%N ltac:(lia)) as B.
  split.
  - unfold seg_rom, memory_read. rewrite U. change (Z.of_N 1) with 1. rewrite FS.
    replace (seg_readable Asan_segment_003) with true by (vm_compute; reflexivity).
    rewrite OFF. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
    rewrite B. reflexivity.
  - intros m Hm. unfold wview. rewrite Hm, U, FS.
    replace (seg_writable Asan_segment_003) with true by (vm_compute; reflexivity).
    rewrite OFF, B. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tab_cell0 : forall m b, 0 <= b < 1048576 ->
  (forall i, TAB + 4 * b <= i < TAB + 4 * b + 4 -> m (wa i) = None) ->
  rw_cells asegs m (TAB + 4 * b) [C4 (Z_to_bv 64 0)].
Proof.
  intros m b Hb Hnone. unfold TAB, NUNIQ in *.
  split; [split|].
  - cbn. split; [reflexivity| exact I].
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    assert (R : TAB <= 1639640 + 4 * b + Z.of_nat i < NUNIQ) by (unfold TAB, NUNIQ; lia).
    destruct (tab_image _ R) as [SR _].
    unfold mrd. rewrite Hnone by lia. rewrite SR.
    destruct i as [|[|[|[|i]]]]; try reflexivity. lia.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    assert (R : TAB <= 1639640 + 4 * b + i < NUNIQ) by (unfold TAB, NUNIQ; lia).
    destruct (tab_image _ R) as [_ WV]. apply WV. apply Hnone. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dp_pfact_eqb (f g : pfact) : bool :=
  match f, g with
  | PVar n lo hi, PVar n' lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
  | PRange e lo hi, PRange e' lo' hi' => zexp_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | PDisj a1 n1 a2 n2, PDisj a1' n1' a2' n2' => zexp_eqb a1 a1' && Z.eqb n1 n1' && zexp_eqb a2 a2' && Z.eqb n2 n2'
  | _, _ => false
  end.
#[using="Type"] Lemma dp_pfact_eqb_eq : forall f g, dp_pfact_eqb f g = true -> f = g.
Proof.
  intros f g H. destruct f, g; cbn in H; try discriminate;
    repeat (apply andb_prop in H as [H ?X]);
    repeat match goal with
    | K : zexp_eqb _ _ = true |- _ => apply zexp_eqb_eq in K
    | K : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in K
    | K : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in K
    end; subst; reflexivity.
Qed.
#[using="Type"] Lemma dp_pfact_find : forall V (l : list pfact) f,
  Forall (pfact_ok V) l -> existsb (dp_pfact_eqb f) l = true -> pfact_ok V f.
Proof.
  intros V l f HF HE. apply existsb_exists in HE as (g & Hin & Hg). apply dp_pfact_eqb_eq in Hg. subst g.
  exact (proj1 (Forall_forall _ _) HF f Hin).
Qed.

End CANSEC1.
Local Ltac mf V m HM f H := pose proof (mfact_find asegs V m _ f HM ltac:(vm_compute; reflexivity)) as H; cbn [mfact_ok zv cellw] in H.
Local Ltac pf V HP f H := pose proof (dp_pfact_find V _ f HP ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok zv] in H.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma stk_of_zero : forall m a n, 0 <= a ->
  (forall i, 0 <= i < n -> m (wa (a + i)) = Some (Z_to_bv 8 0)) -> wr_at asegs m a n -> stk asegs m a (a + n).
Proof.
  intros m a n Ha Z0 (W1 & W2 & W3). split; [lia|]. split; [lia|]. intros x Hx.
  replace x with (a + (x - a)) by lia. split; [apply W3; lia|].
  exists (Z_to_bv 8 0). unfold mrd. rewrite Z0 by lia. reflexivity.
Qed.

#[using="Type"] Lemma wr_at_sub' : forall m a n a' n', wr_at asegs m a n -> 0 <= a' -> a <= a' -> a' + n' <= a + n -> wr_at asegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H0 H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma BUD_le : forall U hs n, Forall (fun u => (length u <= 254)%nat) U -> BUD U hs n <= 255 * Z.of_nat (length U).
Proof.
  induction U as [|u U IH]; intros hs n F; cbn [BUD length]; [lia|].
  inversion F; subst. specialize (IH hs n ltac:(assumption)). unfold ucost. destruct (has_hash hs n (hashU u)); lia.
Qed.
#[using="Type"] Lemma CNT_le : forall U hs n, CNT U hs n <= Z.of_nat (length U).
Proof.
  induction U as [|u U IH]; intros hs n; cbn [CNT length]; [lia|].
  specialize (IH hs n). destruct (has_hash hs n (hashU u)); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hw0 (w : bool) : Z := if w then 4663259168155682864 else 5539319482190822624.
Definition bw0 (w : bool) : Z := if w then 51248 else 163040.
Definition tf0 (w : bool) : Z := if w then 2 else 3.
Definition D0 (w : bool) : dstate :=
  mkD 1 (fun b => if b =? bw0 w then 1 else 0) (fun _ => hw0 w) (fun _ => 0) (fun _ => 1) (tf0 w).

#[using="Type"] Lemma bw0_bkt : forall w, bkt (hw0 w) = bw0 w.
Proof. intros [|]; reflexivity. Qed.

#[using="Type"] Lemma D0_wf : forall w U, (length U <= 4096)%nat -> Forall (fun u => (length u <= 254)%nat) U -> dwf U (D0 w).
Proof.
  intros w U LU FU. pose proof (BUD_le U (fun _ => hw0 w) 1 FU) as B1. pose proof (CNT_le U (fun _ => hw0 w) 1) as C1.
  assert (HW : 0 <= hw0 w < 2^64) by (destruct w; cbn; lia).
  assert (TF : 0 <= tf0 w <= 3) by (destruct w; cbn; lia).
  unfold dwf, D0; cbn [dN dhd dhs dlk dsid dtf].
  split; [lia|]. split. { intros i Hi. lia. }
  split. { intros b Hb. destruct (Z.eqb_spec b (bw0 w)); [| lia]. split; [lia|]. intros _. rewrite bw0_bkt. lia. }
  split. { intros i Hi. split; [exact HW|]. split; [lia|]. intros C. exfalso. exact (C eq_refl). }
  split. { intros i Hi. rewrite bw0_bkt, Z.eqb_refl. assert (i = 1) by lia. subst i. cbn. left. reflexivity. }
  change (Z.to_nat 1) with 1%nat. lia.
Qed.

#[using="Type"] Theorem adepot_init : forall (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem),
  Forall (mfact_ok asegs V m) asan_mem_facts ->
  Forall (mfact_ok asegs V m) (asan_mem_facts_w w) ->
  Forall (pfact_ok V) asan_pure_facts ->
  (length U <= 4096)%nat -> Forall (fun u => (length u <= 254)%nat) U ->
  32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP ->      (* [comment removed for export] *)
  ADEPOTi (mkALayout (LV V) w U) m.
Proof.
  intros V w U m HM HMW HP LU FU HAT.
  set (L := mkALayout (LV V) w U).
  assert (EN : al_nodes L = 4096 * V 469%nat) by reflexivity.
  assert (ES : al_store L = 4096 * V 470%nat) by reflexivity.
  assert (EU : al_U L = U) by reflexivity.
  exists (D0 w). split; [rewrite EU; apply D0_wf; assumption|].
  (* [comment removed for export] *)
  pf V HP (PVar 469 1 34359736064) P469. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 469)) 1048576 (ZLit 65536) 6238208) DIh469. pf V HP (PVar 470 1 34359734272) P470. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 470)) 8388608 (ZLit 65536) 6238208) DIh470.
  pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 469)) 1048576 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW469.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 470)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW470.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 469)) 1048576 (ZMul (ZLit 4096) (ZV 470)) 8388608) D56.
  split.
  2:{ unfold dlayout. rewrite EN, ES. unfold ABase.AIMG_HI. repeat split; try (clear - P469 P470 P0 P6 P10 DW469 DW470 D56 DIh469 DIh470 HAT; lia).
      all: rewrite Z.mul_comm; apply Z_mod_mult. }
  clear DW469 DW470.
  (* [comment removed for export] *)
  mf V m HM (MCell (ZLit 0x1804d8) 8 (ZMul (ZLit 4096) (ZV 470))) CPTR.
  mf V m HM (MCell (ZLit 0x5904d8) 4 (ZLit 1)) CNU.
  mf V m HM (MCell (ZLit 0x5904e8) 8 (ZMul (ZLit 4096) (ZV 469))) CMAP.
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 469)) (ZLit 24)) 4 (ZLit 0)) CN24.
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 469)) (ZLit 28)) 4 (ZLit 1)) CN28.
  mf V m HM (MZero (ZAdd (ZMul (ZLit 4096) (ZV 469)) (ZLit 32)) 1048544) ZN.
  mf V m HM (MWr (ZMul (ZLit 4096) (ZV 469)) 1048576) WN.
  mf V m HM (MWr (ZMul (ZLit 4096) (ZV 470)) 8388608) WS.
  mf8o V m HM (ZMul (ZLit 4096) (ZV 470)) 8 266380 CS8.      (* [comment removed for export] *)
  mf V m HM (MZero (ZAdd (ZMul (ZLit 4096) (ZV 470)) (ZLit 4096)) 8384512) ZS4096.      (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (WF : rw_cells asegs m 1574088 [C8 (Z_to_bv 64 (tf0 w))]
            /\ rw_cells asegs m 1574112 [C4 (Z_to_bv 64 (tf0 w))]
            /\ rw_cells asegs m (1639640 + 4 * bw0 w) [C4 (Z_to_bv 64 1)]
            /\ (forall i, 1574120 <= i < 1639640 + 4 * bw0 w -> m (wa i) = None)
            /\ (forall i, 1639640 + 4 * bw0 w + 4 <= i < 5833944 -> m (wa i) = None)
            /\ rw_cells asegs m (4096 * V 469%nat + 16) [C8 (Z_to_bv 64 (hw0 w))]
            /\ rw_cells asegs m (4096 * V 470%nat) [C8 (Z_to_bv 64 (if w then 1 else 2))]
            /\ stk asegs m (4096 * V 470%nat + 16) (4096 * V 470%nat + 8388608)).
  { destruct w; cbn [tf0 bw0 hw0] in *; unfold asan_mem_facts_w in HMW.
    - (* [comment removed for export] *)
      mf V m HMW (MCell (ZLit 1574088) 8 (ZLit 2)) F1. mf V m HMW (MCell (ZLit 1574112) 4 (ZLit 2)) F2.
      mf V m HMW (MCell (ZLit 1844632) 4 (ZLit 1)) F3. mf V m HMW (MImg 1574120 1844632) F4. mf V m HMW (MImg 1844636 5833944) F5.
      mf V m HMW (MCell (ZAdd (ZMul (ZLit 4096) (ZV 469)) (ZLit 16)) 8 (ZLit 4663259168155682864)) F6.
      mf V m HMW (MCell (ZMul (ZLit 4096) (ZV 470)) 8 (ZLit 1)) F7.
      mf V m HMW (MZero (ZAdd (ZMul (ZLit 4096) (ZV 470)) (ZLit 16)) 4080) F9.
      refine (conj F1 (conj F2 (conj F3 (conj F4 (conj F5 (conj F6 (conj F7 _))))))).
      replace (4096 * V 470%nat + 8388608) with (4096 * V 470%nat + 16 + 8388592) by lia.
      apply stk_of_zero; [lia | | eapply wr_at_sub'; [exact WS | lia | lia | lia]].
      intros i Hi. destruct (Z.lt_ge_cases i 4080) as [LT|GE]; [apply F9; lia|].
      replace (4096 * V 470%nat + 16 + i) with (4096 * V 470%nat + 4096 + (i - 4080)) by lia. apply ZS4096. lia.
    - (* [comment removed for export] *)
      mf V m HMW (MCell (ZLit 1574088) 8 (ZLit 3)) F1. mf V m HMW (MCell (ZLit 1574112) 4 (ZLit 3)) F2.
      mf V m HMW (MCell (ZLit 2291800) 4 (ZLit 1)) F3. mf V m HMW (MImg 1574120 2291800) F4. mf V m HMW (MImg 2291804 5833944) F5.
      mf V m HMW (MCell (ZAdd (ZMul (ZLit 4096) (ZV 469)) (ZLit 16)) 8 (ZLit 5539319482190822624)) F6.
      mf V m HMW (MCell (ZMul (ZLit 4096) (ZV 470)) 8 (ZLit 2)) F7.
      mf8o V m HMW (ZMul (ZLit 4096) (ZV 470)) 16 271324 F8.
      mf V m HMW (MZero (ZAdd (ZMul (ZLit 4096) (ZV 470)) (ZLit 24)) 4072) F9.
      refine (conj F1 (conj F2 (conj F3 (conj F4 (conj F5 (conj F6 (conj F7 _))))))).
      apply (stk_merge asegs m _ (4096 * V 470%nat + 24)); [| | lia].
      + pose proof (stk_of_rw_cells asegs m _ _ F8) as K. cbn [cells_size csize Nat.add] in K.
        replace (4096 * V 470%nat + 16 + Z.of_nat 8) with (4096 * V 470%nat + 24) in K by lia. exact K.
      + replace (4096 * V 470%nat + 8388608) with (4096 * V 470%nat + 24 + 8388584) by lia.
        apply stk_of_zero; [lia | | eapply wr_at_sub'; [exact WS | lia | lia | lia]].
        intros i Hi. destruct (Z.lt_ge_cases i 4072) as [LT|GE]; [apply F9; lia|].
        replace (4096 * V 470%nat + 24 + i) with (4096 * V 470%nat + 4096 + (i - 4072)) by lia. apply ZS4096. lia. }
  (nd_pre WF 8%nat; intros CTF CST CBK IM1 IM2 CN16 CS0 SKS16; nd_post).
  unfold dcells, D0; cbn [dN dhd dhs dlk dsid dtf]. rewrite EN, ES. unfold SSTF, SSPTR, SSST, NUNIQ, MAP1.
  split; [exact CTF|]. split; [exact CPTR|]. split; [exact CST|]. split; [exact CNU|]. split; [exact CMAP|].
  split.
  { intros b Hb. destruct (Z.eqb_spec b (bw0 w)) as [->|NE]; [exact CBK|].
    apply tab_cell0; [exact Hb|]. unfold TAB. intros i Hi.
    assert (BW : 0 <= bw0 w < 1048576) by (destruct w; cbn; lia).
    destruct (Z.lt_ge_cases b (bw0 w)); [apply IM1; lia | apply IM2; lia]. }
  split.
  { intros i Hi. assert (i = 1) by lia. subst i.
    apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact CN16|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m _ [_] [_])). cbn [cells_size csize Nat.add]. split.
    - replace (4096 * V 469%nat + 16 * 1 + Z.of_nat 8) with (4096 * V 469%nat + 24) by lia. exact CN24.
    - replace (4096 * V 469%nat + 16 * 1 + Z.of_nat 8 + Z.of_nat 4) with (4096 * V 469%nat + 28) by lia. exact CN28. }
  split.
  { replace (4096 * V 469%nat + 1048576) with (4096 * V 469%nat + 32 + 1048544) by lia.
    replace (4096 * V 469%nat + 16 * (1 + 1)) with (4096 * V 469%nat + 32) by lia.
    apply stk_of_zero; [lia | exact ZN |]. eapply wr_at_sub'; [exact WN | lia | lia | lia]. }
  apply (stk_merge asegs m _ (4096 * V 470%nat + 8)); [| | lia].
  { pose proof (stk_of_rw_cells asegs m _ _ CS0) as K. cbn [cells_size csize Nat.add] in K.
    replace (4096 * V 470%nat + Z.of_nat 8) with (4096 * V 470%nat + 8) in K by lia. exact K. }
  apply (stk_merge asegs m _ (4096 * V 470%nat + 16)); [| exact SKS16 | lia].
  pose proof (stk_of_rw_cells asegs m _ _ CS8) as K. cbn [cells_size csize Nat.add] in K.
  replace (4096 * V 470%nat + 8 + Z.of_nat 8) with (4096 * V 470%nat + 16) in K by lia. exact K.
Qed.
End CANSEC2.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.ADepotKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ADepot_tabscan.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB.   (* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma tab_image : forall i, TAB <= i < NUNIQ ->
  seg_rom asegs (wa i) = Some (Z_to_bv 8 0) /\ forall m, m (wa i) = None -> wview asegs m (wa i) <> None.
Proof.
  intros i Hi. unfold TAB, NUNIQ in Hi.
  assert (U : bv_unsigned (wa i) = i) by (apply wa_unsigned; lia).
  assert (FS : find_segment asegs i 1 = Some AsanUbsan_segment_003).
  { rewrite a_find_segment_1 by lia.
    destruct (Z.leb_spec0 0x10000 i); destruct (Z.leb_spec0 (i + 1) 0x32000); cbn [andb]; try lia.
    destruct (Z.leb_spec0 0x32000 i); destruct (Z.leb_spec0 (i + 1) 0xa5000); cbn [andb]; try lia.
    destruct (Z.leb_spec0 0xa5000 i); destruct (Z.leb_spec0 (i + 1) 0xa7000); cbn [andb]; try lia.
    destruct (Z.leb_spec0 0xa7000 i); destruct (Z.leb_spec0 (i + 1) 0x604000); cbn [andb]; try lia. reflexivity. }
  assert (OFF : Z.to_N (i - Z.of_N (seg_base AsanUbsan_segment_003)) = (0xe98d8 + Z.to_N (i - 0x1908d8))%N).
  { replace (Z.of_N (seg_base AsanUbsan_segment_003)) with 0xa7000 by (vm_compute; reflexivity). lia. }
  pose proof (tab_byte_at (0xe98d8 + Z.to_N (i - 0x1908d8))%N ltac:(lia)) as B.
  split.
  - unfold seg_rom, memory_read. rewrite U. change (Z.of_N 1) with 1. rewrite FS.
    replace (seg_readable AsanUbsan_segment_003) with true by (vm_compute; reflexivity).
    rewrite OFF. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
    rewrite B. reflexivity.
  - intros m Hm. unfold wview. rewrite Hm, U, FS.
    replace (seg_writable AsanUbsan_segment_003) with true by (vm_compute; reflexivity).
    rewrite OFF, B. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tab_cell0 : forall m b, 0 <= b < 1048576 ->
  (forall i, TAB + 4 * b <= i < TAB + 4 * b + 4 -> m (wa i) = None) ->
  rw_cells asegs m (TAB + 4 * b) [C4 (Z_to_bv 64 0)].
Proof.
  intros m b Hb Hnone. unfold TAB, NUNIQ in *.
  split; [split|].
  - cbn. split; [reflexivity| exact I].
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    assert (R : TAB <= 1640664 + 4 * b + Z.of_nat i < NUNIQ) by (unfold TAB, NUNIQ; lia).
    destruct (tab_image _ R) as [SR _].
    unfold mrd. rewrite Hnone by lia. rewrite SR.
    destruct i as [|[|[|[|i]]]]; try reflexivity. lia.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    assert (R : TAB <= 1640664 + 4 * b + i < NUNIQ) by (unfold TAB, NUNIQ; lia).
    destruct (tab_image _ R) as [_ WV]. apply WV. apply Hnone. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dp_pfact_eqb (f g : pfact) : bool :=
  match f, g with
  | PVar n lo hi, PVar n' lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
  | PRange e lo hi, PRange e' lo' hi' => zexp_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | PDisj a1 n1 a2 n2, PDisj a1' n1' a2' n2' => zexp_eqb a1 a1' && Z.eqb n1 n1' && zexp_eqb a2 a2' && Z.eqb n2 n2'
  | _, _ => false
  end.
#[using="Type"] Lemma dp_pfact_eqb_eq : forall f g, dp_pfact_eqb f g = true -> f = g.
Proof.
  intros f g H. destruct f, g; cbn in H; try discriminate;
    repeat (apply andb_prop in H as [H ?X]);
    repeat match goal with
    | K : zexp_eqb _ _ = true |- _ => apply zexp_eqb_eq in K
    | K : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in K
    | K : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in K
    end; subst; reflexivity.
Qed.
#[using="Type"] Lemma dp_pfact_find : forall V (l : list pfact) f,
  Forall (pfact_ok V) l -> existsb (dp_pfact_eqb f) l = true -> pfact_ok V f.
Proof.
  intros V l f HF HE. apply existsb_exists in HE as (g & Hin & Hg). apply dp_pfact_eqb_eq in Hg. subst g.
  exact (proj1 (Forall_forall _ _) HF f Hin).
Qed.

End CANSEC1.
Local Ltac mf V m HM f H := pose proof (mfact_find asegs V m _ f HM ltac:(vm_compute; reflexivity)) as H; cbn [mfact_ok zv cellw] in H.
Local Ltac pf V HP f H := pose proof (dp_pfact_find V _ f HP ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok zv] in H.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma stk_of_zero : forall m a n, 0 <= a ->
  (forall i, 0 <= i < n -> m (wa (a + i)) = Some (Z_to_bv 8 0)) -> wr_at asegs m a n -> stk asegs m a (a + n).
Proof.
  intros m a n Ha Z0 (W1 & W2 & W3). split; [lia|]. split; [lia|]. intros x Hx.
  replace x with (a + (x - a)) by lia. split; [apply W3; lia|].
  exists (Z_to_bv 8 0). unfold mrd. rewrite Z0 by lia. reflexivity.
Qed.

#[using="Type"] Lemma wr_at_sub' : forall m a n a' n', wr_at asegs m a n -> 0 <= a' -> a <= a' -> a' + n' <= a + n -> wr_at asegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H0 H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma BUD_le : forall U hs n, Forall (fun u => (length u <= 254)%nat) U -> BUD U hs n <= 255 * Z.of_nat (length U).
Proof.
  induction U as [|u U IH]; intros hs n F; cbn [BUD length]; [lia|].
  inversion F; subst. specialize (IH hs n ltac:(assumption)). unfold ucost. destruct (has_hash hs n (hashU u)); lia.
Qed.
#[using="Type"] Lemma CNT_le : forall U hs n, CNT U hs n <= Z.of_nat (length U).
Proof.
  induction U as [|u U IH]; intros hs n; cbn [CNT length]; [lia|].
  specialize (IH hs n). destruct (has_hash hs n (hashU u)); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hw0 (w : bool) : Z := if w then 16662922904711132905 else 16817842525396500458.
Definition bw0 (w : bool) : Z := if w then 456425 else 491498.
Definition tf0 (w : bool) : Z := if w then 2 else 3.
Definition D0 (w : bool) : dstate :=
  mkD 1 (fun b => if b =? bw0 w then 1 else 0) (fun _ => hw0 w) (fun _ => 0) (fun _ => 1) (tf0 w).

#[using="Type"] Lemma bw0_bkt : forall w, bkt (hw0 w) = bw0 w.
Proof. intros [|]; reflexivity. Qed.

#[using="Type"] Lemma D0_wf : forall w U, (length U <= 4096)%nat -> Forall (fun u => (length u <= 254)%nat) U -> dwf U (D0 w).
Proof.
  intros w U LU FU. pose proof (BUD_le U (fun _ => hw0 w) 1 FU) as B1. pose proof (CNT_le U (fun _ => hw0 w) 1) as C1.
  assert (HW : 0 <= hw0 w < 2^64) by (destruct w; cbn; lia).
  assert (TF : 0 <= tf0 w <= 3) by (destruct w; cbn; lia).
  unfold dwf, D0; cbn [dN dhd dhs dlk dsid dtf].
  split; [lia|]. split. { intros i Hi. lia. }
  split. { intros b Hb. destruct (Z.eqb_spec b (bw0 w)); [| lia]. split; [lia|]. intros _. rewrite bw0_bkt. lia. }
  split. { intros i Hi. split; [exact HW|]. split; [lia|]. intros C. exfalso. exact (C eq_refl). }
  split. { intros i Hi. rewrite bw0_bkt, Z.eqb_refl. assert (i = 1) by lia. subst i. cbn. left. reflexivity. }
  change (Z.to_nat 1) with 1%nat. lia.
Qed.

#[using="Type"] Theorem adepot_init : forall (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem),
  Forall (mfact_ok asegs V m) asan_mem_facts ->
  Forall (mfact_ok asegs V m) (asan_mem_facts_w w) ->
  Forall (pfact_ok V) asan_pure_facts ->
  (length U <= 4096)%nat -> Forall (fun u => (length u <= 254)%nat) U ->
  32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP ->      (* [comment removed for export] *)
  ADEPOTi (mkALayout (LV V) w U) m.
Proof.
  intros V w U m HM HMW HP LU FU HAT.
  set (L := mkALayout (LV V) w U).
  assert (EN : al_nodes L = 4096 * V 469%nat) by reflexivity.
  assert (ES : al_store L = 4096 * V 470%nat) by reflexivity.
  assert (EU : al_U L = U) by reflexivity.
  exists (D0 w). split; [rewrite EU; apply D0_wf; assumption|].
  (* [comment removed for export] *)
  pf V HP (PVar 469 1 34359736064) P469. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 469)) 1048576 (ZLit 65536) 6242304) DIh469. pf V HP (PVar 470 1 34359734272) P470. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 470)) 8388608 (ZLit 65536) 6242304) DIh470.
  pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 469)) 1048576 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW469.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 470)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW470.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 469)) 1048576 (ZMul (ZLit 4096) (ZV 470)) 8388608) D56.
  split.
  2:{ unfold dlayout. rewrite EN, ES. unfold A3W.ABase.TwB.AIMG_HI. repeat split; try (clear - P469 P470 P0 P6 P10 DW469 DW470 D56 DIh469 DIh470 HAT; lia).
      all: rewrite Z.mul_comm; apply Z_mod_mult. }
  clear DW469 DW470.
  (* [comment removed for export] *)
  mf V m HM (MCell (ZLit 0x1808d8) 8 (ZMul (ZLit 4096) (ZV 470))) CPTR.
  mf V m HM (MCell (ZLit 0x5908d8) 4 (ZLit 1)) CNU.
  mf V m HM (MCell (ZLit 0x5908e8) 8 (ZMul (ZLit 4096) (ZV 469))) CMAP.
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 469)) (ZLit 24)) 4 (ZLit 0)) CN24.
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 469)) (ZLit 28)) 4 (ZLit 1)) CN28.
  mf V m HM (MZero (ZAdd (ZMul (ZLit 4096) (ZV 469)) (ZLit 32)) 1048544) ZN.
  mf V m HM (MWr (ZMul (ZLit 4096) (ZV 469)) 1048576) WN.
  mf V m HM (MWr (ZMul (ZLit 4096) (ZV 470)) 8388608) WS.
  mf8o V m HM (ZMul (ZLit 4096) (ZV 470)) 8 266484 CS8.      (* [comment removed for export] *)
  mf V m HM (MZero (ZAdd (ZMul (ZLit 4096) (ZV 470)) (ZLit 4096)) 8384512) ZS4096.      (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (WF : rw_cells asegs m 1575112 [C8 (Z_to_bv 64 (tf0 w))]
            /\ rw_cells asegs m 1575136 [C4 (Z_to_bv 64 (tf0 w))]
            /\ rw_cells asegs m (1640664 + 4 * bw0 w) [C4 (Z_to_bv 64 1)]
            /\ (forall i, 1575144 <= i < 1640664 + 4 * bw0 w -> m (wa i) = None)
            /\ (forall i, 1640664 + 4 * bw0 w + 4 <= i < 5834968 -> m (wa i) = None)
            /\ rw_cells asegs m (4096 * V 469%nat + 16) [C8 (Z_to_bv 64 (hw0 w))]
            /\ rw_cells asegs m (4096 * V 470%nat) [C8 (Z_to_bv 64 (if w then 1 else 2))]
            /\ stk asegs m (4096 * V 470%nat + 16) (4096 * V 470%nat + 8388608)).
  { destruct w; cbn [tf0 bw0 hw0] in *; unfold asan_mem_facts_w in HMW.
    - (* [comment removed for export] *)
      mf V m HMW (MCell (ZLit 1575112) 8 (ZLit 2)) F1. mf V m HMW (MCell (ZLit 1575136) 4 (ZLit 2)) F2.
      mf V m HMW (MCell (ZLit 3466364) 4 (ZLit 1)) F3. mf V m HMW (MImg 1575144 3466364) F4. mf V m HMW (MImg 3466368 5834968) F5.
      mf V m HMW (MCell (ZAdd (ZMul (ZLit 4096) (ZV 469)) (ZLit 16)) 8 (ZLit 16662922904711132905)) F6.
      mf V m HMW (MCell (ZMul (ZLit 4096) (ZV 470)) 8 (ZLit 1)) F7.
      mf V m HMW (MZero (ZAdd (ZMul (ZLit 4096) (ZV 470)) (ZLit 16)) 4080) F9.
      refine (conj F1 (conj F2 (conj F3 (conj F4 (conj F5 (conj F6 (conj F7 _))))))).
      replace (4096 * V 470%nat + 8388608) with (4096 * V 470%nat + 16 + 8388592) by lia.
      apply stk_of_zero; [lia | | eapply wr_at_sub'; [exact WS | lia | lia | lia]].
      intros i Hi. destruct (Z.lt_ge_cases i 4080) as [LT|GE]; [apply F9; lia|].
      replace (4096 * V 470%nat + 16 + i) with (4096 * V 470%nat + 4096 + (i - 4080)) by lia. apply ZS4096. lia.
    - (* [comment removed for export] *)
      mf V m HMW (MCell (ZLit 1575112) 8 (ZLit 3)) F1. mf V m HMW (MCell (ZLit 1575136) 4 (ZLit 3)) F2.
      mf V m HMW (MCell (ZLit 3606656) 4 (ZLit 1)) F3. mf V m HMW (MImg 1575144 3606656) F4. mf V m HMW (MImg 3606660 5834968) F5.
      mf V m HMW (MCell (ZAdd (ZMul (ZLit 4096) (ZV 469)) (ZLit 16)) 8 (ZLit 16817842525396500458)) F6.
      mf V m HMW (MCell (ZMul (ZLit 4096) (ZV 470)) 8 (ZLit 2)) F7.
      mf8o V m HMW (ZMul (ZLit 4096) (ZV 470)) 16 271428 F8.
      mf V m HMW (MZero (ZAdd (ZMul (ZLit 4096) (ZV 470)) (ZLit 24)) 4072) F9.
      refine (conj F1 (conj F2 (conj F3 (conj F4 (conj F5 (conj F6 (conj F7 _))))))).
      apply (stk_merge asegs m _ (4096 * V 470%nat + 24)); [| | lia].
      + pose proof (stk_of_rw_cells asegs m _ _ F8) as K. cbn [cells_size csize Nat.add] in K.
        replace (4096 * V 470%nat + 16 + Z.of_nat 8) with (4096 * V 470%nat + 24) in K by lia. exact K.
      + replace (4096 * V 470%nat + 8388608) with (4096 * V 470%nat + 24 + 8388584) by lia.
        apply stk_of_zero; [lia | | eapply wr_at_sub'; [exact WS | lia | lia | lia]].
        intros i Hi. destruct (Z.lt_ge_cases i 4072) as [LT|GE]; [apply F9; lia|].
        replace (4096 * V 470%nat + 24 + i) with (4096 * V 470%nat + 4096 + (i - 4072)) by lia. apply ZS4096. lia. }
  (nd_pre WF 8%nat; intros CTF CST CBK IM1 IM2 CN16 CS0 SKS16; nd_post).
  unfold dcells, D0; cbn [dN dhd dhs dlk dsid dtf]. rewrite EN, ES. unfold SSTF, SSPTR, SSST, NUNIQ, MAP1.
  split; [exact CTF|]. split; [exact CPTR|]. split; [exact CST|]. split; [exact CNU|]. split; [exact CMAP|].
  split.
  { intros b Hb. destruct (Z.eqb_spec b (bw0 w)) as [->|NE]; [exact CBK|].
    apply tab_cell0; [exact Hb|]. unfold TAB. intros i Hi.
    assert (BW : 0 <= bw0 w < 1048576) by (destruct w; cbn; lia).
    destruct (Z.lt_ge_cases b (bw0 w)); [apply IM1; lia | apply IM2; lia]. }
  split.
  { intros i Hi. assert (i = 1) by lia. subst i.
    apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact CN16|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m _ [_] [_])). cbn [cells_size csize Nat.add]. split.
    - replace (4096 * V 469%nat + 16 * 1 + Z.of_nat 8) with (4096 * V 469%nat + 24) by lia. exact CN24.
    - replace (4096 * V 469%nat + 16 * 1 + Z.of_nat 8 + Z.of_nat 4) with (4096 * V 469%nat + 28) by lia. exact CN28. }
  split.
  { replace (4096 * V 469%nat + 1048576) with (4096 * V 469%nat + 32 + 1048544) by lia.
    replace (4096 * V 469%nat + 16 * (1 + 1)) with (4096 * V 469%nat + 32) by lia.
    apply stk_of_zero; [lia | exact ZN |]. eapply wr_at_sub'; [exact WN | lia | lia | lia]. }
  apply (stk_merge asegs m _ (4096 * V 470%nat + 8)); [| | lia].
  { pose proof (stk_of_rw_cells asegs m _ _ CS0) as K. cbn [cells_size csize Nat.add] in K.
    replace (4096 * V 470%nat + Z.of_nat 8) with (4096 * V 470%nat + 8) in K by lia. exact K. }
  apply (stk_merge asegs m _ (4096 * V 470%nat + 16)); [| exact SKS16 | lia].
  pose proof (stk_of_rw_cells asegs m _ _ CS8) as K. cbn [cells_size csize Nat.add] in K.
  replace (4096 * V 470%nat + 8 + Z.of_nat 8) with (4096 * V 470%nat + 16) in K by lia. exact K.
Qed.
End CANSEC2.
End TwB.
End ADepot_init.

(* [comment removed for export] *)
Module AResv.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import MState Mem Cells ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AHandoffDefs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require Import AsanPlan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma resv_named : forall V k n kd lo hi,
  In (LMap (ZMul (ZLit 4096) (ZV k)) n kd) asan_ledger ->
  0 <= V k <= 34359738368 -> 0 <= n < 2^62 ->
  4096 * V k <= lo -> hi <= 4096 * V k + n ->
  pcov (resv_of V) lo hi.
Proof.
  intros V k n kd lo hi HIN HV HN LO HI x Hx.
  exists (4096 * V k, 4096 * V k + n). split; [| cbn [fst snd]; lia].
  unfold resv_of, resv_entries. rewrite map_app. apply in_app_iff. left.
  apply in_map_iff. exists (wa (zv V (ZMul (ZLit 4096) (ZV k))), wa n). split.
  - unfold iv_of, wa. cbn [fst snd zv]. rewrite !unsigned_lit by lia. reflexivity.
  - apply in_flat_map. exists (LMap (ZMul (ZLit 4096) (ZV k)) n kd). split; [exact HIN| left; reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma resv_lit : forall V b n kd lo hi,
  In (LMap (ZLit b) n kd) asan_ledger ->
  0 <= b < 2^62 -> 0 <= n < 2^62 ->
  b <= lo -> hi <= b + n ->
  pcov (resv_of V) lo hi.
Proof.
  intros V b n kd lo hi HIN HB HN LO HI x Hx.
  exists (b, b + n). split; [| cbn [fst snd]; lia].
  unfold resv_of, resv_entries. rewrite map_app. apply in_app_iff. left.
  apply in_map_iff. exists (wa (zv V (ZLit b)), wa n). split.
  - unfold iv_of, wa. cbn [fst snd zv]. rewrite !unsigned_lit by lia. reflexivity.
  - apply in_flat_map. exists (LMap (ZLit b) n kd). split; [exact HIN| left; reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma resv_img : forall V, pcov (resv_of V) 0x10000 AIMG_HI.
Proof.
  intros V x Hx. unfold AIMG_HI in Hx.
  assert (SEG : forall b n, In (b, n) (map uns2 (segments_reserved asegs)) -> In (b, b + n) (resv_of V)).
  { intros b n Hin. apply in_map_iff in Hin. (nd_pre Hin 3%nat; intros [a m] E Hin; nd_post). unfold uns2 in E. cbn [fst snd] in E. injection E as <- <-.
    unfold resv_of, resv_entries. rewrite map_app. apply in_app_iff. right. apply in_map_iff. exists (a, m). split; [reflexivity| exact Hin]. }
  rewrite reserved_eval in SEG.
  destruct (Z_lt_le_dec x 204800); [| destruct (Z_lt_le_dec x 671744); [| destruct (Z_lt_le_dec x 684032)]].      (* [comment removed for export] *)
  - exists (65536, 65536 + 139264). split; [apply SEG; cbn; tauto| cbn [fst snd]; lia].
  - exists (204800, 204800 + 466944). split; [apply SEG; cbn; tauto| cbn [fst snd]; lia].
  - exists (671744, 671744 + 12288). split; [apply SEG; cbn; tauto| cbn [fst snd]; lia].
  - exists (684032, 684032 + 5619712). split; [apply SEG; cbn; tauto| cbn [fst snd]; lia].
Qed.

End CANSEC1.
Local Ltac inled := cbn; repeat (first [left; exact eq_refl | right]).
(* [comment removed for export] *)
Local Ltac pv PF k lo hi :=
  let H := fresh in pose proof (pfact_find _ (PVar k lo hi) PF ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok] in H.

Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Theorem aresv_ok_handoff : forall V (w : bool) (U : list (list Z)),
  Forall (pfact_ok V) asan_pure_facts ->
  aresv_ok (mkALayout (LV V) w U) (resv_of V).
Proof.
  intros V w U PF.
  pv PF 78%nat 1 34359736304. pv PF 207%nat 1 34359735410. pv PF 208%nat 4295491576 34326181871.
  pv PF 226%nat 1 34359734272. pv PF 227%nat 1 34359736319. pv PF 228%nat 1 34359736304.
  pv PF 245%nat 1 34359736319. pv PF 310%nat 1 34359736319. pv PF 393%nat 1 34359733495.
  pv PF 469%nat 1 34359736064. pv PF 470%nat 1 34359734272. pv PF 487%nat 1 34359736319. pv PF 568%nat 1 34359736319.
  unfold aresv_ok, al_space_beg, al_ptr_array, al_t, al_ctx, al_nodes, al_store, al_fake. lazy [al_V LV Nat.eqb].
  split; [apply resv_img|].
  split.
  { (* [comment removed for export] *)
    intros x Hx.
    destruct (Z_lt_le_dec x 0x8fff7000); [| destruct (Z_lt_le_dec x 0x2008fff7000)].
    - eapply (resv_lit V 2147446784 268435456 _); [inled| lia| lia| | | exact (conj (proj1 Hx) l)]; cbn; lia.
    - eapply (resv_lit V 2415882240 2199023255552 _); [inled| lia| lia| | | exact (conj l l0)]; cbn; lia.
    - eapply (resv_lit V 2201439137792 15392894357504 _); [inled| lia| lia| | | exact (conj l0 (proj2 Hx))]; cbn; lia. }
  split; [eapply (resv_named V 208 137439023104 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 226 8388608 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 227 4096 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 228 65536 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 469 1048576 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 470 8388608 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 393 11571200 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 310 4096 _); [inled| lia| lia| lia| cbn; lia]|].
  (* [comment removed for export] *)
  split; [eapply (resv_named V 78 65536 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 207 3727360 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 245 4096 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 487 4096 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 568 4096 _); [inled| lia| lia| lia| cbn; lia]|].
  (* [comment removed for export] *)
  intros x Hx. apply (resv_img V). pose proof ATPv_img as TI. unfold AIMG_HI. lia.
Qed.
End CANSEC2.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHandoffDefs.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma resv_named : forall V k n kd lo hi,
  In (LMap (ZMul (ZLit 4096) (ZV k)) n kd) asan_ledger ->
  0 <= V k <= 34359738368 -> 0 <= n < 2^62 ->
  4096 * V k <= lo -> hi <= 4096 * V k + n ->
  pcov (resv_of V) lo hi.
Proof.
  intros V k n kd lo hi HIN HV HN LO HI x Hx.
  exists (4096 * V k, 4096 * V k + n). split; [| cbn [fst snd]; lia].
  unfold resv_of, resv_entries. rewrite map_app. apply in_app_iff. left.
  apply in_map_iff. exists (wa (zv V (ZMul (ZLit 4096) (ZV k))), wa n). split.
  - unfold iv_of, wa. cbn [fst snd zv]. rewrite !unsigned_lit by lia. reflexivity.
  - apply in_flat_map. exists (LMap (ZMul (ZLit 4096) (ZV k)) n kd). split; [exact HIN| left; reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma resv_lit : forall V b n kd lo hi,
  In (LMap (ZLit b) n kd) asan_ledger ->
  0 <= b < 2^62 -> 0 <= n < 2^62 ->
  b <= lo -> hi <= b + n ->
  pcov (resv_of V) lo hi.
Proof.
  intros V b n kd lo hi HIN HB HN LO HI x Hx.
  exists (b, b + n). split; [| cbn [fst snd]; lia].
  unfold resv_of, resv_entries. rewrite map_app. apply in_app_iff. left.
  apply in_map_iff. exists (wa (zv V (ZLit b)), wa n). split.
  - unfold iv_of, wa. cbn [fst snd zv]. rewrite !unsigned_lit by lia. reflexivity.
  - apply in_flat_map. exists (LMap (ZLit b) n kd). split; [exact HIN| left; reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma resv_img : forall V, pcov (resv_of V) 0x10000 AIMG_HI.
Proof.
  intros V x Hx. unfold AIMG_HI in Hx.
  assert (SEG : forall b n, In (b, n) (map uns2 (segments_reserved asegs)) -> In (b, b + n) (resv_of V)).
  { intros b n Hin. apply in_map_iff in Hin. (nd_pre Hin 3%nat; intros [a m] E Hin; nd_post). unfold uns2 in E. cbn [fst snd] in E. injection E as <- <-.
    unfold resv_of, resv_entries. rewrite map_app. apply in_app_iff. right. apply in_map_iff. exists (a, m). split; [reflexivity| exact Hin]. }
  rewrite reserved_eval in SEG.
  destruct (Z_lt_le_dec x 204800); [| destruct (Z_lt_le_dec x 675840); [| destruct (Z_lt_le_dec x 684032)]].      (* [comment removed for export] *)
  - exists (65536, 65536 + 139264). split; [apply SEG; cbn; tauto| cbn [fst snd]; lia].
  - exists (204800, 204800 + 471040). split; [apply SEG; cbn; tauto| cbn [fst snd]; lia].
  - exists (675840, 675840 + 8192). split; [apply SEG; cbn; tauto| cbn [fst snd]; lia].
  - exists (684032, 684032 + 5623808). split; [apply SEG; cbn; tauto| cbn [fst snd]; lia].
Qed.

End CANSEC1.
Local Ltac inled := cbn; repeat (first [left; exact eq_refl | right]).
(* [comment removed for export] *)
Local Ltac pv PF k lo hi :=
  let H := fresh in pose proof (pfact_find _ (PVar k lo hi) PF ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok] in H.

Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Theorem aresv_ok_handoff : forall V (w : bool) (U : list (list Z)),
  Forall (pfact_ok V) asan_pure_facts ->
  aresv_ok (mkALayout (LV V) w U) (resv_of V).
Proof.
  intros V w U PF.
  pv PF 78%nat 1 34359736304. pv PF 207%nat 1 34359735410. pv PF 208%nat 4295491576 34326181871.
  pv PF 226%nat 1 34359734272. pv PF 227%nat 1 34359736319. pv PF 228%nat 1 34359736304.
  pv PF 245%nat 1 34359736319. pv PF 310%nat 1 34359736319. pv PF 393%nat 1 34359733495.
  pv PF 469%nat 1 34359736064. pv PF 470%nat 1 34359734272. pv PF 487%nat 1 34359736319. pv PF 568%nat 1 34359736319.
  unfold aresv_ok, al_space_beg, al_ptr_array, al_t, al_ctx, al_nodes, al_store, al_fake. lazy [al_V LV Nat.eqb].
  split; [apply resv_img|].
  split.
  { (* [comment removed for export] *)
    intros x Hx.
    destruct (Z_lt_le_dec x 0x8fff7000); [| destruct (Z_lt_le_dec x 0x2008fff7000)].
    - eapply (resv_lit V 2147446784 268435456 _); [inled| lia| lia| | | exact (conj (proj1 Hx) l)]; cbn; lia.
    - eapply (resv_lit V 2415882240 2199023255552 _); [inled| lia| lia| | | exact (conj l l0)]; cbn; lia.
    - eapply (resv_lit V 2201439137792 15392894357504 _); [inled| lia| lia| | | exact (conj l0 (proj2 Hx))]; cbn; lia. }
  split; [eapply (resv_named V 208 137439023104 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 226 8388608 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 227 4096 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 228 65536 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 469 1048576 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 470 8388608 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 393 11571200 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 310 4096 _); [inled| lia| lia| lia| cbn; lia]|].
  (* [comment removed for export] *)
  split; [eapply (resv_named V 78 65536 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 207 3727360 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 245 4096 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 487 4096 _); [inled| lia| lia| lia| cbn; lia]|].
  split; [eapply (resv_named V 568 4096 _); [inled| lia| lia| lia| cbn; lia]|].
  (* [comment removed for export] *)
  intros x Hx. apply (resv_img V). pose proof ATPv_img as TI. unfold AIMG_HI. lia.
Qed.
End CANSEC2.
End TwB.
End AResv.

(* [comment removed for export] *)
Module ARepInit.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AHandoffDefs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_iface AFake_init. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_init OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_init__A3W.ADepot_init OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_C OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_D OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_E.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Init.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.   (* [comment removed for export] *)
  Hypothesis HTLS : tls_at V.      (* [comment removed for export] *)
  Hypothesis SH0 : ashadow0 V m.
  Hypothesis SH1 : ashadow1 V m.      (* [comment removed for export] *)
  Let L := mkALayout (LV V) w U.
  (* [comment removed for export] *)
  Local Ltac ho := first [eassumption | exact (proj1 HTLS)].

  (* [comment removed for export] *)
  #[using="rc tlsI HM HP HU HAT HTLS"] Theorem AQUAR_init : AQUAR L (ST0 V) X0 m.
  Proof.
    exists qconc0. unfold AQUAR_at. cbn [q_loc q_glob q_ia qconc0 a_qloc a_qglob a_qloc_bytes a_qglob_bytes ST0 ainit].
    split; [(eapply aquar_glob_const_init; ho)|].
    split; [(eapply aqcache_loc_init; ho)|].
    split; [(eapply aqcache_glob_init; ho)|].
    split; [(eapply aintal_init; ho)|].
    split; [(eapply qcoupled_init; ho)| (eapply qnum_init; ho)].
  Qed.

  (* [comment removed for export] *)
  Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (DEP : alayout -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
  Hypothesis HQ : AQ L (ST0 V) X0 m.
  Hypothesis HS : ASEC L (ST0 V) X0 m.
  Hypothesis HD : DEP L m.
  Let H := mkAHoles AQ ASEC DEP AFK.

  #[using="HM HP HU HAT HTLS SH0 HQ HS HD"] Theorem AREP_init : AREP H L (ST0 V) X0 m.
  Proof.
    unfold AREP. cbn [ah_quar ah_sec ah_depot H].
    split; [(eapply awf_init; ho)|].
    split; [(eapply arep_rt_init; ho)|].
    split; [(eapply ainstance_init; ho)|].
    split; [(eapply athread_init; ho)|].
    split.
    { intros c Hc. split; [(eapply aregion_cells_init; ho)|]. split; [(eapply afreearray_init; ho)|].
      split; [(eapply aslots_init; ho)| (eapply aslot_shadow_init; ho)]. }
    split; [exact HQ|]. split; [exact HS|]. split; [exact HD|].
    split; [(eapply arelro_init; ho)|].
    split; [(eapply arep_rt2_init; ho)|].
    split; [intros c Hc; (eapply ashadow_avail_init; ho)|].
    (eapply arep_rt3_init; ho).
  Qed.

  (* [comment removed for export] *)
  Variables (lz : list (word * word)) (AL : word -> Prop).
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.
  (* [comment removed for export] *)
  Hypothesis ASH0 : forall p : word, bv_unsigned p mod 4096 = 0 ->
    shad (al_space_beg L) <= bv_unsigned p < shad (al_space_beg L) + 17179869184 -> AL p.
  Hypothesis HF : AFK L [] m.

  #[using="HM HP HU HAT HTLS SH0 HQ HS HD A0I ASH0 HF"] Theorem AHEAP_P_init : AHEAP_P H L (fp_ok lz AL) (ST0 V) [] m.
  Proof.
    split; [(eapply alayout_ok_init; ho)|].
    split; [(eapply arng_init; ho)|].
    split; [exists X0; split; [exact AREP_init| (eapply ablocks_init; ho)]|].
    exact HF.
  Qed.
End Init.

(* [comment removed for export] *)
#[using="Type"] Corollary AHEAP_P_init_fake :
  forall (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (DEP : alayout -> amem -> Prop)
         (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem) (lz : list (word * word)) (AL : word -> Prop),
    Forall (mfact_ok asegs V m) asan_mem_facts -> Forall (pfact_ok V) asan_pure_facts -> (length U <= Z.to_nat AUMAX)%nat ->
    32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP -> tls_at V -> ashadow0 V m -> ashadow1 V m ->
    AQ (mkALayout (LV V) w U) (ST0 V) X0 m -> ASEC (mkALayout (LV V) w U) (ST0 V) X0 m -> DEP (mkALayout (LV V) w U) m ->
    (forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p) ->
    (forall p : word, bv_unsigned p mod 4096 = 0 -> shad (al_space_beg (mkALayout (LV V) w U)) <= bv_unsigned p < shad (al_space_beg (mkALayout (LV V) w U)) + 17179869184 -> AL p) ->
    AHEAP_P (mkAHoles AQ ASEC DEP AFAKE) (mkALayout (LV V) w U) (fp_ok lz AL) (ST0 V) [] m.
Proof.
  intros AQ ASEC DEP V w U m lz AL HM HP HU HAT HTLS SH0 SH1 HQ HS HD A0I ASH0.
  apply AHEAP_P_init; try assumption. apply afake_init; first [assumption | exact (proj1 HTLS)].
Qed.

(* [comment removed for export] *)
#[using="Type"] Corollary AHEAP_P_init_quar_fake :
  forall (ASEC : alayout -> astate -> aconc -> amem -> Prop) (DEP : alayout -> amem -> Prop)
         (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem) (lz : list (word * word)) (AL : word -> Prop),
    Forall (mfact_ok asegs V m) asan_mem_facts -> Forall (pfact_ok V) asan_pure_facts -> (length U <= Z.to_nat AUMAX)%nat ->
    32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP -> tls_at V -> ashadow0 V m -> ashadow1 V m ->
    ASEC (mkALayout (LV V) w U) (ST0 V) X0 m -> DEP (mkALayout (LV V) w U) m ->
    (forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p) ->
    (forall p : word, bv_unsigned p mod 4096 = 0 -> shad (al_space_beg (mkALayout (LV V) w U)) <= bv_unsigned p < shad (al_space_beg (mkALayout (LV V) w U)) + 17179869184 -> AL p) ->
    AHEAP_P (mkAHoles AQUAR ASEC DEP AFAKE) (mkALayout (LV V) w U) (fp_ok lz AL) (ST0 V) [] m.
Proof.
  intros ASEC DEP V w U m lz AL HM HP HU HAT HTLS SH0 SH1 HS HD A0I ASH0.
  apply AHEAP_P_init_fake; try assumption. apply AQUAR_init; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Corollary AHEAP_P_init_qdf :
  forall (ASEC : alayout -> astate -> aconc -> amem -> Prop)
         (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem) (lz : list (word * word)) (AL : word -> Prop),
    Forall (mfact_ok asegs V m) asan_mem_facts -> Forall (mfact_ok asegs V m) (asan_mem_facts_w w) -> Forall (pfact_ok V) asan_pure_facts ->
    (length U <= 4096)%nat -> Forall (fun u => (length u <= 254)%nat) U ->
    32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP -> tls_at V -> ashadow0 V m -> ashadow1 V m ->
    ASEC (mkALayout (LV V) w U) (ST0 V) X0 m ->
    (forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p) ->
    (forall p : word, bv_unsigned p mod 4096 = 0 -> shad (al_space_beg (mkALayout (LV V) w U)) <= bv_unsigned p < shad (al_space_beg (mkALayout (LV V) w U)) + 17179869184 -> AL p) ->
    AHEAP_P (mkAHoles AQUAR ASEC (ADEPOT adepot_iface) AFAKE) (mkALayout (LV V) w U) (fp_ok lz AL) (ST0 V) [] m.
Proof.
  intros ASEC V w U m lz AL HM HMw HP HU HU' HAT HTLS SH0 SH1 HS A0I ASH0.
  apply AHEAP_P_init_quar_fake; try assumption. cbn [ADEPOT adepot_iface]. apply adepot_init; assumption.
Qed.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHandoffDefs.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_init.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_init__A3W.ADepot_init.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_C.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_D.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_E.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Init.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.   (* [comment removed for export] *)
  Hypothesis HTLS : tls_at V.      (* [comment removed for export] *)
  Hypothesis SH0 : ashadow0 V m.
  Hypothesis SH1 : ashadow1 V m.      (* [comment removed for export] *)
  Let L := mkALayout (LV V) w U.
  (* [comment removed for export] *)
  Local Ltac ho := first [eassumption | exact (proj1 HTLS)].

  (* [comment removed for export] *)
  #[using="rc tlsI HM HP HU HAT HTLS"] Theorem AQUAR_init : AQUAR L (ST0 V) X0 m.
  Proof.
    exists qconc0. unfold AQUAR_at. cbn [q_loc q_glob q_ia qconc0 a_qloc a_qglob a_qloc_bytes a_qglob_bytes ST0 ainit].
    split; [(eapply aquar_glob_const_init; ho)|].
    split; [(eapply aqcache_loc_init; ho)|].
    split; [(eapply aqcache_glob_init; ho)|].
    split; [(eapply aintal_init; ho)|].
    split; [(eapply qcoupled_init; ho)| (eapply qnum_init; ho)].
  Qed.

  (* [comment removed for export] *)
  Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (DEP : alayout -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
  Hypothesis HQ : AQ L (ST0 V) X0 m.
  Hypothesis HS : ASEC L (ST0 V) X0 m.
  Hypothesis HD : DEP L m.
  Let H := mkAHoles AQ ASEC DEP AFK.

  #[using="HM HP HU HAT HTLS SH0 HQ HS HD"] Theorem AREP_init : AREP H L (ST0 V) X0 m.
  Proof.
    unfold AREP. cbn [ah_quar ah_sec ah_depot H].
    split; [(eapply awf_init; ho)|].
    split; [(eapply arep_rt_init; ho)|].
    split; [(eapply ainstance_init; ho)|].
    split; [(eapply athread_init; ho)|].
    split.
    { intros c Hc. split; [(eapply aregion_cells_init; ho)|]. split; [(eapply afreearray_init; ho)|].
      split; [(eapply aslots_init; ho)| (eapply aslot_shadow_init; ho)]. }
    split; [exact HQ|]. split; [exact HS|]. split; [exact HD|].
    split; [(eapply arelro_init; ho)|].
    split; [(eapply arep_rt2_init; ho)|].
    split; [intros c Hc; (eapply ashadow_avail_init; ho)|].
    (eapply arep_rt3_init; ho).
  Qed.

  (* [comment removed for export] *)
  Variables (lz : list (word * word)) (AL : word -> Prop).
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.
  (* [comment removed for export] *)
  Hypothesis ASH0 : forall p : word, bv_unsigned p mod 4096 = 0 ->
    shad (al_space_beg L) <= bv_unsigned p < shad (al_space_beg L) + 17179869184 -> AL p.
  Hypothesis HF : AFK L [] m.

  #[using="HM HP HU HAT HTLS SH0 HQ HS HD A0I ASH0 HF"] Theorem AHEAP_P_init : AHEAP_P H L (fp_ok lz AL) (ST0 V) [] m.
  Proof.
    split; [(eapply alayout_ok_init; ho)|].
    split; [(eapply arng_init; ho)|].
    split; [exists X0; split; [exact AREP_init| (eapply ablocks_init; ho)]|].
    exact HF.
  Qed.
End Init.

(* [comment removed for export] *)
#[using="Type"] Corollary AHEAP_P_init_fake :
  forall (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (DEP : alayout -> amem -> Prop)
         (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem) (lz : list (word * word)) (AL : word -> Prop),
    Forall (mfact_ok asegs V m) asan_mem_facts -> Forall (pfact_ok V) asan_pure_facts -> (length U <= Z.to_nat AUMAX)%nat ->
    32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP -> tls_at V -> ashadow0 V m -> ashadow1 V m ->
    AQ (mkALayout (LV V) w U) (ST0 V) X0 m -> ASEC (mkALayout (LV V) w U) (ST0 V) X0 m -> DEP (mkALayout (LV V) w U) m ->
    (forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p) ->
    (forall p : word, bv_unsigned p mod 4096 = 0 -> shad (al_space_beg (mkALayout (LV V) w U)) <= bv_unsigned p < shad (al_space_beg (mkALayout (LV V) w U)) + 17179869184 -> AL p) ->
    AHEAP_P (mkAHoles AQ ASEC DEP AFAKE) (mkALayout (LV V) w U) (fp_ok lz AL) (ST0 V) [] m.
Proof.
  intros AQ ASEC DEP V w U m lz AL HM HP HU HAT HTLS SH0 SH1 HQ HS HD A0I ASH0.
  apply AHEAP_P_init; try assumption. apply afake_init; first [assumption | exact (proj1 HTLS)].
Qed.

(* [comment removed for export] *)
#[using="Type"] Corollary AHEAP_P_init_quar_fake :
  forall (ASEC : alayout -> astate -> aconc -> amem -> Prop) (DEP : alayout -> amem -> Prop)
         (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem) (lz : list (word * word)) (AL : word -> Prop),
    Forall (mfact_ok asegs V m) asan_mem_facts -> Forall (pfact_ok V) asan_pure_facts -> (length U <= Z.to_nat AUMAX)%nat ->
    32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP -> tls_at V -> ashadow0 V m -> ashadow1 V m ->
    ASEC (mkALayout (LV V) w U) (ST0 V) X0 m -> DEP (mkALayout (LV V) w U) m ->
    (forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p) ->
    (forall p : word, bv_unsigned p mod 4096 = 0 -> shad (al_space_beg (mkALayout (LV V) w U)) <= bv_unsigned p < shad (al_space_beg (mkALayout (LV V) w U)) + 17179869184 -> AL p) ->
    AHEAP_P (mkAHoles AQUAR ASEC DEP AFAKE) (mkALayout (LV V) w U) (fp_ok lz AL) (ST0 V) [] m.
Proof.
  intros ASEC DEP V w U m lz AL HM HP HU HAT HTLS SH0 SH1 HS HD A0I ASH0.
  apply AHEAP_P_init_fake; try assumption. apply AQUAR_init; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Corollary AHEAP_P_init_qdf :
  forall (ASEC : alayout -> astate -> aconc -> amem -> Prop)
         (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem) (lz : list (word * word)) (AL : word -> Prop),
    Forall (mfact_ok asegs V m) asan_mem_facts -> Forall (mfact_ok asegs V m) (asan_mem_facts_w w) -> Forall (pfact_ok V) asan_pure_facts ->
    (length U <= 4096)%nat -> Forall (fun u => (length u <= 254)%nat) U ->
    32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP -> tls_at V -> ashadow0 V m -> ashadow1 V m ->
    ASEC (mkALayout (LV V) w U) (ST0 V) X0 m ->
    (forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p) ->
    (forall p : word, bv_unsigned p mod 4096 = 0 -> shad (al_space_beg (mkALayout (LV V) w U)) <= bv_unsigned p < shad (al_space_beg (mkALayout (LV V) w U)) + 17179869184 -> AL p) ->
    AHEAP_P (mkAHoles AQUAR ASEC (ADEPOT adepot_iface) AFAKE) (mkALayout (LV V) w U) (fp_ok lz AL) (ST0 V) [] m.
Proof.
  intros ASEC V w U m lz AL HM HMw HP HU HU' HAT HTLS SH0 SH1 HS A0I ASH0.
  apply AHEAP_P_init_quar_fake; try assumption. cbn [ADEPOT adepot_iface]. apply adepot_init; assumption.
Qed.
End CANSEC1.
End TwB.
End ARepInit.
