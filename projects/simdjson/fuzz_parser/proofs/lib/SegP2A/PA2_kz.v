(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge Mem Cells Step Frame SysStep Bytes InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells ABase AMalloc_iface AU_iface AU_kit AU_fuzz_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Export APS2_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Local Notation M64 := 18446744073709551616.
Local Notation u := bv_unsigned.
Local Notation SH := 2147450880%Z (only parsing).

Notation ATOPM := 140737479966720%Z (only parsing).
(* [comment removed for export] *)
Definition DJ (a n b k : Z) : Prop := a + n <= b \/ b + k <= a.

Ltac clear_quant := repeat match goal with H : forall _ : Z, _ |- _ => clear H end.
Ltac zsolve := clear_quant; repeat (rewrite (Z.mod_small _ 18446744073709551616) by lia); lia.
Ltac djsolve :=
  clear_quant; repeat (rewrite (Z.mod_small _ 18446744073709551616) by lia);
  first [ left; lia | right; lia
        | match goal with H : DJ ?a ?n ?b ?k |- _ =>
            lazymatch goal with |- context [a] => lazymatch goal with |- context [b] =>
              unfold DJ in H; solve [destruct H as [h|h]; [left; lia | right; lia] | destruct H as [h|h]; [right; lia | left; lia]]
            end end end ].

(* [comment removed for export] *)
Ltac djsolve2 :=
  clear_quant; repeat (rewrite (Z.mod_small _ 18446744073709551616) by lia);
  first [ left; lia | right; lia
        | match goal with H : DJ _ _ _ _ |- _ =>
            unfold DJ in H; solve [destruct H as [h|h]; [left; lia | right; lia] | destruct H as [h|h]; [right; lia | left; lia]] end ].

Section CANSEC. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma shad_8 : forall X, 0 <= X -> shad (8 * X) = SH + X.
Proof. intros X H. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite Z.mul_comm, Z.div_mul by lia. lia. Qed.

(* [comment removed for export] *)
Lemma seg_rom_above : forall a, 0x665000 <= a < M64 -> seg_rom asegs (Z_to_bv 64 a) = None.
Proof. intros a H. apply ref_seg_rom_none. rewrite u_Z_to_bv, Z.mod_small by lia. lia. Qed.

Section K.
  Variable ZL : list Z.
  Variable m : word -> option byte.
  Local Notation E := (mkEZ ZL).
  Local Notation zv e := (zden ZL e mod M64).

  (* [comment removed for export] *)
  Lemma kz_shadow_blk : forall (AI : AMallocIface) L RNG st LB p n b cnt,
    AHEAP AI L RNG st LB m -> In (HB p (8 * zv b) n) LB -> (zok b && zok cnt)%bool = true ->
    8 * zv cnt <= n -> SH + zv b + zv cnt < M64 ->
    kentry_ok asegs E m (KZero (SA b SH) cnt).
  Proof.
    intros AI L RNG st LB p n b cnt AH HIN Hz Hc Hb.
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH HIN) as (_ & _ & _ & _ & BSH & _).
    pose proof (Z.mod_pos_bound (zden ZL b) M64 ltac:(lia)). pose proof (Z.mod_pos_bound (zden ZL cnt) M64 ltac:(lia)).
    apply (kz_zero asegs ZL m); [exact Hz | lia | lia | lia |]. intros i Hi.
    specialize (BSH i ltac:(lia) ltac:(lia)). rewrite shad_8 in BSH by lia.
    replace (8 * i + 8 <=? n) with true in BSH by (symmetry; apply Z.leb_le; lia). unfold wa in BSH.
    replace (zv b + SH + i) with (SH + zv b + i) by lia. exact BSH.
  Qed.

  (* [comment removed for export] *)
  Lemma kz_zero_cells : forall b k cnt A cs, (zok b && zok cnt)%bool = true -> rw_cells asegs m A cs ->
    0x665000 <= A -> A + Z.of_nat (cells_size cs) <= M64 ->
    A <= zv b + k -> zv b + k + zv cnt <= A + Z.of_nat (cells_size cs) -> zv b + k < M64 ->
    (forall i, 0 <= i < zv cnt -> nth_error (cells_bytes cs) (Z.to_nat (zv b + k - A + i)) = Some (Z_to_bv 8 0)) ->
    kentry_ok asegs E m (KZero (SA b k) cnt).
  Proof.
    intros b k cnt A cs Hz [[Hwf HB] _] H1 H2 H3 H4 H5 HZ.
    apply (kz_zero_bytes asegs ZL m b k cnt A (cells_bytes cs) Hz HB); [| lia | rewrite cells_bytes_length by exact Hwf; lia | lia | exact HZ].
    intros i Hi. rewrite cells_bytes_length in Hi by exact Hwf. apply seg_rom_above. lia.
  Qed.
End K.

(* [comment removed for export] *)
Lemma stk_wr_atA : forall m lo hi a n, stk asegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> wr_at asegs m a n.
Proof.
  intros m lo hi a n (S0 & S1 & S) H1 H2 H3. split; [lia|]. split; [lia|]. intros i Hi.
  exact (proj1 (S (a + i) ltac:(lia))).
Qed.

Lemma stk_unkA : forall ZL m lo hi b k n, stk asegs m lo hi -> (zok b && zok n)%bool = true ->
  0x665000 <= lo -> hi < M64 -> lo <= zden ZL b mod M64 + k -> zden ZL b mod M64 + k + zden ZL n mod M64 <= hi ->
  kentry_ok asegs (mkEZ ZL) m (KUnk (SA b k) n).
Proof.
  intros ZL m lo hi b k n (S0 & S1 & S) Hz Hlo Hhi H1 H2. pose proof (Z.mod_pos_bound (zden ZL n) M64 ltac:(lia)).
  apply (kz_unk asegs ZL m); [exact Hz | lia | lia | lia |]. intros i Hi.
  destruct (S (zden ZL b mod M64 + k + i) ltac:(lia)) as [_ (bt & Hb)].
  rewrite ref_mrd_overlay in Hb by (unfold wa; rewrite u_Z_to_bv, Z.mod_small by lia; lia). unfold wa in Hb. rewrite Hb. discriminate.
Qed.

Lemma seg_rom_blk : forall A n, 0x665000 <= A -> A + n <= M64 -> forall i, 0 <= i < n -> seg_rom asegs (Z_to_bv 64 (A + i)) = None.
Proof. intros A n H0 H1 i Hi. apply seg_rom_above. lia. Qed.

Lemma cb_bytesA : forall m A n j, rw_cells asegs m A [CB n j] -> bytes_at asegs m A j /\ Z.of_nat (length j) = Z.of_nat n.
Proof.
  intros m A n j H. pose proof (rw_cells_bytes_at _ _ _ _ H) as HB. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  split; [exact HB|]. destruct H as [[[Hw _] _] _]. cbn [cell_wf] in Hw. rewrite Hw. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma kz_unk_wr : forall ZL m b k n A L, (zok b && zok n)%bool = true -> wr_at asegs m A L -> 0x665000 <= A ->
  A <= zden ZL b mod M64 + k -> zden ZL b mod M64 + k + zden ZL n mod M64 <= A + L -> zden ZL b mod M64 + k < M64 ->
  kentry_ok asegs (mkEZ ZL) m (KUnk (SA b k) n).
Proof.
  intros ZL m b k n A L Hz (W0 & W1 & W) HA H1 H2 H3. pose proof (Z.mod_pos_bound (zden ZL n) M64 ltac:(lia)).
  apply (kz_unk asegs ZL m); [exact Hz | lia | lia | lia |]. intros i Hi.
  specialize (W (zden ZL b mod M64 + k - A + i) ltac:(lia)).
  rewrite ref_wview_overlay in W by (unfold wa; rewrite u_Z_to_bv, Z.mod_small by lia; lia).
  unfold wa in W. replace (A + (zden ZL b mod M64 + k - A + i)) with (zden ZL b mod M64 + k + i) in W by lia. exact W.
Qed.

(* [comment removed for export] *)
Lemma blk_bounds : forall (AI : AMallocIface) L RNG st LB m b, AHEAP AI L RNG st LB m -> In b LB ->
  0x665000 <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP.
Proof. intros AI L RNG st LB m b AH HIN. pose proof (AI_block_bounds AI _ _ _ _ _ _ AH HIN). unfold AIMG_HI in *. lia. Qed.

Lemma heap_blk_ablk : forall (AI : AMallocIface) L RNG st LB m p A n, AHEAP AI L RNG st LB m -> In (HB p A n) LB ->
  ((0x665000 <= A /\ A + n <= 0x7fff7000) \/ (0x10007fff8000 <= A /\ A + n <= ATOP)) /\ A mod 16 = 0 /\ 1 <= n.
Proof.
  intros AI L RNG st LB m p A n AH HIN. destruct (AI_block AI _ _ _ _ _ _ _ _ AH HIN) as (NR & (B1 & B2 & B3 & B4) & _).
  unfold ablk, AIMG_HI, KLS in B1. lia.
Qed.

(* [comment removed for export] *)
Lemma heap_blk_disj : forall (AI : AMallocIface) L RNG st LB m p A n q B k, AHEAP AI L RNG st LB m ->
  In (HB p A n) LB -> In (HB q B k) LB -> p <> q -> A + n <= B \/ B + k <= A.
Proof.
  intros AI L RNG st LB m p A n q B k AH H1 H2 Hpq.
  exact (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH H1 H2 ltac:(intros E; injection E; intros; subst; apply Hpq; reflexivity)).
Qed.

(* [comment removed for export] *)
Lemma heap_fake_disj : forall (AI : AMallocIface) L RNG st LB m p A n cls FA FN, AHEAP AI L RNG st LB m ->
  In (HB p A n) LB -> In (mkABlock (ABFake cls) FA FN) LB -> A + n <= FA \/ FA + FN <= A.
Proof.
  intros AI L RNG st LB m p A n cls FA FN AH H1 H2.
  exact (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH H1 H2 ltac:(intros E; discriminate E)).
Qed.

(* [comment removed for export] *)
Lemma got_nothrow_cell : forall (AI : AMallocIface) L RNG st LB m, AHEAP AI L RNG st LB m -> mem_inv asegs m ->
  rw_cells asegs m 0x107fa0 [C8 (Z_to_bv 64 0x2cb90)].
Proof.
  intros AI L RNG st LB m AH MI. pose proof (AI_relro AI L RNG st LB m AH) as R. unfold ARELRO_LO, ARELRO_HI in R.
  eapply rw_cells_recast; [apply (rw_cells_image0 asegs _ 0x107fa0 (le8 (Z_to_bv 64 0x2cb90)));
    [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
    | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma tab_sh_pts : forall m lo hi, tab_sh m (lo, hi) -> 0x665000 <= shad lo -> shad lo + (hi - lo) / 8 < M64 -> 0 <= (hi - lo) / 8 ->
  forall i, 0 <= i < (hi - lo) / 8 -> m (Z_to_bv 64 (shad lo + i)) = Some (Z_to_bv 8 0).
Proof.
  intros m lo hi HT H1 H2 H3 i Hi. unfold tab_sh in HT. cbn [fst snd] in HT.
  pose proof (rw_cells_bytes_at _ _ _ _ HT) as (_ & _ & HB). cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  rewrite repeat_length in HB. specialize (HB (Z.to_nat i) ltac:(lia)).
  rewrite nth_error_repeat in HB by lia. rewrite Z2Nat.id in HB by lia.
  rewrite ref_mrd_overlay in HB by (unfold wa; rewrite u_Z_to_bv, Z.mod_small by lia; lia). exact HB.
Qed.

Lemma img_sh_pts : forall m, img_sh m ->
  forall a n i, In (a, n) A2_IMGSH -> 0 <= i < n -> m (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).
Proof.
  intros m HI a n i Ha Hi.
  assert (KEY : forall lo hi, In (lo, hi) IMG_TABS -> a = shad lo -> n = (hi - lo) / 8 -> m (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0)).
  { intros lo hi Hin -> ->. pose proof (proj1 (Forall_forall _ _) HI _ Hin) as HT. pose proof (img_tabs_bounds lo hi Hin) as B.
    eapply tab_sh_pts; [exact HT | rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia
                       | rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | exact Hi]. }
  cbn [A2_IMGSH In] in Ha.
  destruct Ha as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; injection E as <- <-;
    [ apply (KEY 0x23500 0x23600) | apply (KEY 0x23640 0x24418) | apply (KEY 0x24780 0x24838) | apply (KEY 0x24860 0x27110)
    | apply (KEY 0x28280 0x28380) | apply (KEY 0x283c0 0x2ad20) | apply (KEY 0x2ad40 0x2afc0) ];
    first [ (cbn [IMG_TABS In]; tauto) | (vm_compute; reflexivity) ].
Qed.

(* [comment removed for export] *)
Lemma img_sh_pres : forall (AI : AMallocIface) LB SP m m', (forall iv, In iv client_ranges -> In iv (aci AI)) ->
  img_sh m -> aheap_pres (aci AI) LB SP m m' -> img_sh m'.
Proof.
  intros AI LB SP m m' HCI HI HP. unfold img_sh in *. apply Forall_forall. intros [lo hi] Hin.
  pose proof (proj1 (Forall_forall _ _) HI _ Hin) as HT. pose proof (img_tabs_bounds lo hi Hin) as B.
  unfold tab_sh in *. cbn [fst snd] in *.
  eapply aheap_pres_rw_cells; [exact HP | exact HT |]. right; right. right; left.
  exists (lo, hi). split; [apply HCI; unfold client_ranges; apply in_or_app; right; exact Hin|].
  cbn [fst snd cells_size csize]. rewrite ?Nat.add_0_r. rewrite shad_div. unfold ASHOFF. rewrite Z2Nat.id by (Z.div_mod_to_equations; lia).
  Z.div_mod_to_equations. lia.
Qed.

End CANSEC.
