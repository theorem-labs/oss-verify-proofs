(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v; 64 of its 422 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/TxGlue.v, with its module paths and module names changed; 647 of its 739 lines of code are new or changed and 330 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/WriterRet.v, with its module paths changed; 199 of its 247 lines of code are new or changed and 691 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/WriterCall.v, with its module paths and module names changed; 105 of its 137 lines of code are new or changed and 215 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/SlotStepB.v, with its addresses changed; 196 of its 247 lines of code are new or changed and 86 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/SlotStepC.v, with its addresses changed; 303 of its 367 lines of code are new or changed and 183 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract Img0 FrameAPI AllocSlots AllocRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem Frame Cells Step Exec.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger GIInit KindBGlue SlotInv SlotDefs
  SlotStep SlotStepA SlotStepB SlotStepC WriterSpec HState HStateRoom preset_base64_decode_c fuzz_alloc_peak_c
  check_bounded_alloc_c SlotRunB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require HsKindB WriterSpecFacts.
Import ListNotations.
Local Open Scope Z_scope.

(* From the decoder call to the check_2 call: the decoder (its contract), then segment sD (fuzz_alloc_peak and
   check_1 inside). The state after the decoder (pd) carries the decoder's answer (dec_ans). *)

Lemma six_len : forall six, Z.of_nat (length (six_bytes six)) <= Z.of_nat (length six) / 4 * 3 + 2.
Proof.
  fix IH 1. intros [|a [|b [|c [|d r]]]]; cbn [six_bytes length]; try (Z.div_mod_to_equations; lia).
  specialize (IH r). Z.div_mod_to_equations. lia.
Qed.

Lemma dec_len : forall tb bs, b64_dec tb = Some bs -> Z.of_nat (length bs) <= Z.of_nat (length tb) / 4 * 3 + 2.
Proof.
  intros tb bs H. unfold b64_dec in H.
  destruct (b64_scan 0 [] tb) as [[six pad]|] eqn:E; [|discriminate].
  destruct ((pad <=? 2) && six_tail_ok six); [|discriminate]. injection H as <-.
  destruct (WriterSpecFacts.scan_inv tb 0 [] six pad E) as [H1 _]. cbn [length] in H1.
  pose proof (six_len six). Z.div_mod_to_equations. lia.
Qed.

Lemma map_zs : forall l, map (Z_to_bv 8) (zs l) = l.
Proof.
  intros l. unfold zs. rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext. intros x.
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma zs_ok : forall l, bytes_ok (zs l).
Proof.
  intros l. unfold bytes_ok, zs. apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (x & <- & _).
  pose proof (bv_unsigned_in_range 8 x) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma zs_nz : forall l, ~ In (Z_to_bv 8 0) l -> no_zero (zs l).
Proof.
  intros l H. unfold no_zero, zs. apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (x & <- & Hx).
  intros E. apply H. replace (Z_to_bv 8 0) with x; [exact Hx|]. apply bv_eq. rewrite E. reflexivity.
Qed.

Lemma hi_writable : forall m a, 0x55000 <= a < 2 ^ 64 -> mbyte rsegs m a <> None -> writable_at rsegs m a.
Proof.
  intros m a Ha H. unfold writable_at, wview. unfold mbyte in H.
  destruct (m (Z_to_bv 64 a)) as [x|] eqn:E; [discriminate|].
  exfalso. apply H. unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
  rewrite MState.unsigned_lit by lia.
  rewrite (HsKindB.find_segment_above rsegs 0x55000 a 1 HsKindB.rsegs_top) by lia. reflexivity.
Qed.

Lemma wr_of_bytes : forall m a l, 0x55000 <= a -> Mem.bytes_at rsegs m a l -> Mem.wr_at rsegs m a (Z.of_nat (length l)).
Proof.
  intros m a l Ha (H1 & H2 & H3). split; [lia|]. split; [lia|]. intros i Hi.
  apply (hi_writable m (a + i)); [lia|].
  replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia.
  change (mbyte rsegs m (a + Z.of_nat (Z.to_nat i))) with (Mem.mrd rsegs m (Mem.wa (a + Z.of_nat (Z.to_nat i)))).
  rewrite (H3 (Z.to_nat i) ltac:(lia)). apply nth_error_Some. lia.
Qed.

Lemma bytes_keep : forall segs m m' a l, Mem.bytes_at segs m a l ->
  (forall i, 0 <= i < Z.of_nat (length l) -> mbyte segs m' (a + i) = mbyte segs m (a + i)) ->
  Mem.bytes_at segs m' a l.
Proof.
  intros segs m m' a l (H1 & H2 & H3) K. split; [exact H1|]. split; [exact H2|]. intros i Hi.
  change (mbyte segs m' (a + Z.of_nat i) = nth_error l i). rewrite K by lia. exact (H3 i Hi).
Qed.

Lemma bytes_present : forall segs m a k, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> present m (a + i)) -> exists l, length l = k /\ Mem.bytes_at segs m a l.
Proof.
  intros segs m a k. revert a. induction k as [|k IH]; intros a Ha Hk HP.
  - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (HP 0 ltac:(lia)) as (x & Hx). rewrite Z.add_0_r in Hx.
    destruct (IH (a + 1)) as (l & Hl & Hb); [lia | lia | |].
    { intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply HP. lia. }
    exists (x :: l). split; [cbn; lia|]. split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i].
    + cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. unfold Mem.mrd, Mem.wa. rewrite Hx. reflexivity.
    + cbn [nth_error]. destruct Hb as (_ & _ & Hb). cbn [length] in Hi. rewrite <- (Hb i ltac:(lia)).
      f_equal. f_equal. lia.
Qed.

Section D.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Lemma slack_of : block_slack_present B API -> forall L A mem md p n, MR L A mem md -> In (p, n) (blocks L A) ->
  0 <= n -> exists slack, Mem.bytes_at (ms_segs B) mem (p + n) slack /\ Z.of_nat (length slack) = (- (p + n)) mod 8.
Proof.
  intros BS L A mem md p n HM Hin Hn.
  destruct (HsKindB.in_blocks L A p n Hin) as (q & Hq & ->).
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q n HM Hq) as [R1 R2].
  pose proof alloc_ceiling_lt as Hc.
  destruct (bytes_present (ms_segs B) mem (ptr_addr L q + n) (Z.to_nat ((- (ptr_addr L q + n)) mod 8)))
    as (l & Hl & Hb).
  - lia.
  - pose proof (Z.mod_pos_bound (- (ptr_addr L q + n)) 8 ltac:(lia)). lia.
  - intros i Hi. apply (BS L A mem md (ptr_addr L q) n); [exact HM | exact Hin |].
    rewrite Z2Nat.id in Hi by (apply Z.mod_pos_bound; lia). Z.div_mod_to_equations. lia.
  - exists l. split; [exact Hb|]. rewrite Hl. rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). reflexivity.
Qed.

(* mid_call for a callee that may also write the frame's first cell (the decoder writes the length there). *)
Lemma mid_call_c : slot_env B API ->
  forall regs0 L0 A0 mem0 md0 cnt0 L A regs mem md lenw Lam peak cnt bnd Kc E L' A' regs' mem' md'
    lenw' Lam' peak' cnt' bnd',
  slot_mid B API regs0 L0 A0 mem0 md0 cnt0 L A regs mem md lenw Lam peak cnt bnd ->
  call_post_k B MR Kc L A regs mem md E L' A' regs' mem' md' ->
  0 <= Kc <= SLOT_STACK - 48 ->
  (forall a, E a -> in_globals omx_G a \/ (a < alloc_ceiling /\ ~ in_img B a) \/
     (spZ regs0 - 48 <= a < spZ regs0 - 40)) ->
  (forall q k, In (q, k) (user_blocks A0) -> In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) ->
  (st_init_done A = true -> st_init_done A' = true) ->
  Mem.bytes_at (ms_segs B) mem' (spZ regs0 - 48) (Mem.le8 lenw') ->
  ledger B L' A' mem' Lam' peak' cnt' (2 ^ 64 - 1) -> cnt0 <= cnt' <= cnt0 + 100 ->
  res_ok_slots A' bnd' -> ro_agree (ms_segs B) mem' ->
  slot_mid B API regs0 L0 A0 mem0 md0 cnt0 L' A' regs' mem' md' lenw' Lam' peak' cnt' bnd'.
Proof.
  intros ENV regs0 L0 A0 mem0 md0 cnt0 L A regs mem md lenw Lam peak cnt bnd Kc E L' A' regs' mem' md'
    lenw' Lam' peak' cnt' bnd' (SP & REL & R2 & RS & FR & _ & _ & _ & _ & FZ) CP HK HE HU HI HL LG HC RES RA.
  pose proof ENV as (SEG & _ & _ & ERR & AX & _ & GF & _).
  pose proof (slot_img_low B API ENV) as IL. pose proof IL as [ILi _].
  pose proof (mid_spZ B regs0 regs SP R2) as Hsp. pose proof SP as (H16 & Hlo & Hhi & Htp).
  pose proof alloc_ceiling_val. pose proof alloc_ceiling_lt. unfold SLOT_STACK in *.
  pose proof CP as (HM' & _ & _ & _ & _ & RP & _ & HF & _).
  pose proof REL as (HM & _).
  assert (Elow : forall a, E a -> a < alloc_ceiling \/ spZ regs0 - 48 <= a < spZ regs0 - 40).
  { intros a Ha. destruct (HE a Ha) as [Hg|[Hl|Hc]]; [left | left; tauto | right; exact Hc].
    destruct (GF a Hg) as (_ & Hr & _). lia. }
  assert (HLw : forall i, 0 <= i < 8 -> writable_at (ms_segs B) mem' (spZ regs0 - 48 + i)).
  { intros i Hi. rewrite SEG. apply hi_writable; [lia|]. destruct HL as (_ & _ & HL3).
    pose proof (HL3 (Z.to_nat i) ltac:(rewrite Mem.length_le8; lia)) as Hb.
    replace (spZ regs0 - 48 + i) with (spZ regs0 - 48 + Z.of_nat (Z.to_nat i)) by lia.
    rewrite <- SEG.
    change (mbyte (ms_segs B) mem' (spZ regs0 - 48 + Z.of_nat (Z.to_nat i)))
      with (Mem.mrd (ms_segs B) mem' (Mem.wa (spZ regs0 - 48 + Z.of_nat (Z.to_nat i)))).
    rewrite Hb. apply nth_error_Some. rewrite Mem.length_le8. lia. }
  split; [exact SP|].
  split.
  { apply (slot_rel_call B API AX IL omx_G SLOT_STACK (spZ regs0) L0 A0 mem0 md0 L A mem md Kc regs E L' A' regs' mem' md'
      REL CP); unfold SLOT_STACK; try lia.
    - intros a Ha Hs He. destruct (Elow a He); lia.
    - intros a Hi _ _ _ Hg He. destruct (HE a He) as [Hg'|[(_ & Hn)|Hc]];
        [exact (Hg Hg') | exact (Hn Hi) | pose proof (ILi a Hi); lia].
    - intros a Ha Hn.
      destruct (Z_le_gt_dec (spZ regs0 - 48) a) as [Hx1|Hx1]; [destruct (Z_lt_ge_dec a (spZ regs0 - 40)) as [Hx2|Hx2]|].
      + left. replace a with (spZ regs0 - 48 + (a - (spZ regs0 - 48))) by lia. apply HLw. lia.
      + right. intros He. destruct (Elow a He); lia.
      + right. intros He. destruct (Elow a He); lia.
    - exact HU.
    - exact HI. }
  split; [exact (eq_trans (RP 2 ltac:(unfold callee_saved; lia)) R2)|].
  split; [intros k Hk; exact (eq_trans (RP k ltac:(unfold callee_saved; lia)) (RS k Hk))|].
  split.
  { destruct FR as ((WF0 & BY0) & _).
    cbn [slot_cells Cells.cells_bytes Cells.cbytes] in BY0.
    apply Mem.bytes_at_app in BY0 as (_ & BY1). rewrite Mem.length_le8 in BY1.
    assert (KEEP : forall i, 0 <= i < 40 ->
              mbyte rsegs mem' (spZ regs0 - 48 + Z.of_nat 8 + i) = mbyte rsegs mem (spZ regs0 - 48 + Z.of_nat 8 + i)).
    { intros i Hi. rewrite <- SEG. eapply proj1. apply HF.
      - left. lia.
      - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho). lia.
      - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM' Ho). lia.
      - unfold scratch_k. rewrite Hsp. lia.
      - intros He. destruct (Elow _ He); lia. }
    assert (BYN : Mem.bytes_at rsegs mem' (spZ regs0 - 48) (Cells.cells_bytes (slot_cells regs0 lenw'))).
    { cbn [slot_cells Cells.cells_bytes Cells.cbytes]. apply Mem.bytes_at_app. split.
      - rewrite <- SEG. exact HL.
      - rewrite Mem.length_le8. apply (bytes_keep rsegs mem mem' _ _ BY1). intros i Hi.
        apply KEEP. cbn [length app] in Hi. rewrite !length_app, !Mem.length_le8 in Hi. cbn in Hi. lia. }
    split; [split; [exact WF0 | exact BYN]|].
    pose proof (wr_of_bytes mem' (spZ regs0 - 48) _ ltac:(lia) BYN) as WR.
    cbn [slot_cells Cells.cells_bytes Cells.cbytes] in WR. rewrite !length_app, !Mem.length_le8 in WR.
    cbn [slot_cells Cells.cells_size Cells.csize Nat.add]. cbn [length Nat.add] in WR. exact WR. }
  split; [exact LG|]. split; [exact HC|]. split; [exact RES|]. split; [exact RA | exact FZ].
Qed.

Definition dec_ans (L0 : layout) (A0 : astate) (mem : word -> option byte) (pl : list byte) (text bd : Z)
    (lenw : word) (Lam : list (Z * Z)) (b bnd : sbound) : Prop :=
  (b64_dec (zs (slot_db pl)) = None /\ bd = 0 /\ lenw = Z_to_bv 64 (2 ^ 64 - 1) /\ Lam = [] /\
   bnd = sb_malloc b (slot_nn pl + 1)) \/
  (exists bs, b64_dec (zs (slot_db pl)) = Some bs /\ bd <> 0 /\ lenw = Z_to_bv 64 (Z.of_nat (length bs)) /\
   Mem.bytes_at (ms_segs B) mem bd (bz bs) /\ Lam = [(bd, dec_size (zs (slot_db pl)))] /\
   bnd = sb_malloc (sb_malloc b (slot_nn pl + 1)) (dec_size (zs (slot_db pl)) + 16) /\
   (text, slot_nn pl + 1) <> (bd - 16, dec_size (zs (slot_db pl)) + 16) /\
   (forall q k, In (q, k) (user_blocks A0) -> (ptr_addr L0 q, k) <> (bd - 16, dec_size (zs (slot_db pl)) + 16))).

Definition pd (regs0 : bvmap 5 word) (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model)
    (pl : list byte) (cnt0 : Z) (b : sbound)
    (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (lenw : word) (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound) (bd : Z) (pt : sptr) (text : Z) : Prop :=
  slot_mid B API regs0 L0 A0 mem0 md0 cnt0 L A regs mem md lenw Lam peak cnt bnd /\
  In (pt, slot_nn pl + 1) (user_blocks A) /\ ptr_addr L pt = text /\ text mod 16 = 0 /\
  (forall q k, In (q, k) (user_blocks A0) -> 0 < k -> ptr_addr L0 q <> text) /\
  Mem.bytes_at (ms_segs B) mem text (slot_db pl ++ [Z_to_bv 8 0]) /\
  dec_ans L0 A0 mem pl text bd lenw Lam b bnd /\ slot_nn pl <= 0x300000.

Definition at_c2 (regs0 : bvmap 5 word) (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model)
    (pl : list byte) (cnt0 : Z) (b : sbound)
    (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  exists lenw Lam peak cnt bnd bd pt text,
  pd regs0 L0 A0 mem0 md0 pl cnt0 b L A regs mem md lenw Lam peak cnt bnd bd pt text /\ cnt <= cnt0 + 4 /\
  getr regs 1 = Z_to_bv 64 0x133d4 /\ getr regs 8 = Z_to_bv 64 text /\ getr regs 9 = Z_to_bv 64 (slot_nn pl) /\
  getr regs 10 = Z_to_bv 64 text /\ getr regs 11 = Z_to_bv 64 bd /\ getr regs 12 = lenw /\
  getr regs 18 = Z_to_bv 64 bd /\ getr regs 19 = Z_to_bv 64 0.

Lemma step_dec : slot_env B API -> preset_base64_decode_contract B API sb_form -> fuzz_alloc_peak_contract ->
  check_bounded_alloc_contract ->
  forall regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L A regs mem md (P : config -> Prop),
  slot_start B API regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j -> slot_bnd b ->
  at_dec B API regs0 L0 A0 mem0 md0 p0 pl cnt0 b L A regs mem md ->
  (forall L' A' regs' mem' md', at_c2 regs0 L0 A0 mem0 md0 pl cnt0 b L' A' regs' mem' md' ->
     SR (ms_segs B) (mkCfg (mkst regs' (Z_to_bv 64 0x135ec) mem' (seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 0x14e90) mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros ENV DEC FAP CBA regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L A regs mem md P HS HB
    (cnt & pt & text & MID & Hcn & Hpt & Ept & H16 & FA0 & BYT & R1 & R8 & R9 & R10 & R11 & R18 & R19 & Hnn) KC.
  pose proof ENV as (SEG & MAL & FRE & ERR & AX & BS & GF & SNK).
  pose proof HS as (SP & _ & _ & _ & _ & _ & _ & _ & _ & Hp & Hpe & _ & _ & _ & _ & _ & _ & _ & HCN & HJ).
  pose proof MID as (_ & REL & R2 & RS & FR & LG & HC & RES & RA & FZ).
  pose proof (mid_spZ B regs0 regs SP R2) as Hsp.
  pose proof SP as (Hs16 & Hlo & Hhi & Htp).
  pose proof alloc_ceiling_val as Hac. pose proof alloc_ceiling_lt as Hacl.
  pose proof (slot_nn_range pl) as Hnr. pose proof (slot_db_length pl) as Hdl.
  pose proof REL as (HM & _).
  pose proof HB as (HBl & HBb & HBc).
  assert (Hj : Z.of_nat j <= 3) by lia. assert (Hcnt : cnt0 <= 3 * 2 ^ 60) by nia.
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ pt _ HM Hpt) as [Ht1 Ht2]. rewrite Ept in Ht1, Ht2.
  assert (HinT : In (text, slot_nn pl + 1) (blocks L A)).
  { rewrite <- Ept. unfold blocks. apply in_map_iff. exists (pt, slot_nn pl + 1). split; [reflexivity | exact Hpt]. }
  destruct (slack_of BS L A mem md text (slot_nn pl + 1) HM HinT ltac:(lia)) as (slack & BS1 & Hsl).
  unfold SLOT_STACK in *.
  assert (Htb : Z.of_nat (length (zs (slot_db pl))) = slot_nn pl) by (unfold zs; rewrite length_map; exact Hdl).
  assert (Hds : dec_size (zs (slot_db pl)) = slot_nn pl / 4 * 3 + 3) by (unfold dec_size; rewrite Htb; reflexivity).
  destruct FR as ((WF0 & BY0) & WR0).
  eapply SR_bind.
  { apply (DEC L A regs mem md text (spZ regs0 - 48) (zs (slot_db pl)) slack (sb_malloc b (slot_nn pl + 1)) [] 0 cnt
      (2 ^ 64 - 1)).
    - exact SEG.
    - exact ERR.
    - exact RA.
    - eapply mid_pre; [exact MID | unfold DEC_STACK, ALLOC_STACK, SLOT_STACK; lia |]. rewrite R1. apply ret_lit; lia.
    - exact R10.
    - exact R11.
    - apply zs_nz, slot_db_nozero.
    - apply zs_ok.
    - lia.
    - rewrite map_app, map_zs. cbn [map]. apply Mem.bytes_at_app. split; [exact BYT|].
      replace (text + Z.of_nat (length (slot_db pl ++ [Z_to_bv 8 0]))) with (text + (slot_nn pl + 1))
        by (rewrite length_app, Nat2Z.inj_add, Hdl; cbn [length Z.of_nat]; lia).
      exact BS1.
    - rewrite Htb, Hsl. replace (- (text + slot_nn pl + 1)) with (- (text + (slot_nn pl + 1))) by lia. lia.
    - right. right. right. exists text, (slot_nn pl + 1). rewrite Htb. split; [exact HinT | lia].
    - rewrite Hsp. lia.
    - Z.div_mod_to_equations. lia.
    - intros i Hi. rewrite SEG. destruct WR0 as (_ & _ & W). apply (W i).
      cbn [slot_cells Cells.cells_size Cells.csize Nat.add]. lia.
    - right. lia.
    - exact LG.
    - exact RES.
    - apply (room_of b); [exact HB | reflexivity | cbn [sb_live sb_malloc]; lia | cbn [sb_bytes sb_malloc]; lia |].
      rewrite Hds. lia. }
  intros c' (L' & A' & regs' & mem' & md' & q & -> & RA' & GK & INIT & CP & REG & KP & TK & CASES).
  cbn [rf_ok rf_malloc rf_free sb_form] in CASES.
  rewrite R1.
  pose proof CP as (HM' & _ & _ & _ & PA & RP & _ & HF & _).
  assert (Hcf : cnt <> 2 ^ 64 - 1) by lia.
  assert (Hpk : Z.max 0 (lsum [] + dec_size (zs (slot_db pl))) = b64_alloc_bound (slot_nn pl))
    by (cbn [lsum]; rewrite Hds; unfold b64_alloc_bound; lia).
  assert (Hc1 : (cnt + 1) mod 2 ^ 64 = cnt + 1) by (apply Z.mod_small; lia).
  assert (UNI : exists bd lenw' Lam' bnd',
            getr regs' 10 = Z_to_bv 64 bd /\
            Mem.bytes_at (ms_segs B) mem' (spZ regs0 - 48) (Mem.le8 lenw') /\
            ledger B L' A' mem' Lam' (b64_alloc_bound (slot_nn pl)) (cnt + 1) (2 ^ 64 - 1) /\
            res_ok_slots A' bnd' /\ ublocks_kept L A A' (0, 0) /\
            (forall a, dec_writes q (dec_size (zs (slot_db pl))) (spZ regs0 - 48) a ->
               in_globals omx_G a \/ (a < alloc_ceiling /\ ~ in_img B a) \/ (spZ regs0 - 48 <= a < spZ regs0 - 40)) /\
            dec_ans L0 A0 mem' pl text bd lenw' Lam' b bnd').
  { assert (Hst : forall a, alloc_statics a -> in_globals omx_G a) by exact statics_G.
    destruct CASES as [(Hcq & _)|[(_ & Hnone & Hq0 & Hqc & Hqi & R10' & BLK & UK & LP & LG' & RES')|
      (bs & _ & Hsome & Hq0 & R10' & Hq16 & Hnq & Hns & Hqi & BLs & UK & LG' & BYQ & BYL & RES')]].
    - exfalso. exact (Hcf Hcq).
    - exists 0, (Z_to_bv 64 (2 ^ 64 - 1)), [], (sb_malloc b (slot_nn pl + 1)).
      split; [exact R10'|].
      split.
      { apply (bytes_keep (ms_segs B) mem mem'); [|intros i Hi; rewrite Mem.length_le8 in Hi; apply LP; lia].
        cbn [slot_cells Cells.cells_bytes Cells.cbytes] in BY0.
        apply Mem.bytes_at_app in BY0 as (BY0 & _). rewrite SEG. exact BY0. }
      split; [rewrite Hpk, Hc1 in LG'; exact LG'|].
      split; [eapply res_same_blocks; [exact RES | exact RES' | reflexivity | exact BLK]|].
      split; [exact UK|].
      split.
      { intros a [Ha|[(_ & Ha)|Ha]]; [left; exact (Hst a Ha) | right; left | right; right; lia].
        split; [lia|]. replace a with (q - 16 + (a - (q - 16))) by lia. apply Hqi. lia. }
      left. repeat split; assumption.
    - exists q, (Z_to_bv 64 (Z.of_nat (length bs))), [(q, dec_size (zs (slot_db pl)))],
        (sb_malloc (sb_malloc b (slot_nn pl + 1)) (dec_size (zs (slot_db pl)) + 16)).
      destruct BLs as (b1 & b2 & Eb' & Eb).
      assert (Hinq : In (q - 16, dec_size (zs (slot_db pl)) + 16) (blocks L' A'))
        by (rewrite Eb'; apply in_or_app; right; left; reflexivity).
      pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM') as PW. rewrite Eb' in PW.
      assert (DJ : forall a k, In (a, k) (blocks L A) -> (a, k) <> (q - 16, dec_size (zs (slot_db pl)) + 16) /\
                     (0 < k -> a <> q - 16)).
      { intros a k Hak. rewrite Eb in Hak.
        destruct (pw_mid _ b1 (q - 16, dec_size (zs (slot_db pl)) + 16) b2 (a, k) PW Hak) as [D|D];
          unfold ranges_disjoint in D; cbn [fst snd] in D; rewrite Hds in D;
          (split; [intros E; injection E as E1 E2; lia | lia]). }
      split; [exact R10'|].
      split; [exact BYL|].
      split; [rewrite Hpk, Hc1 in LG'; exact LG'|].
      split; [exact RES'|].
      split; [exact UK|].
      split.
      { intros a [Ha|[(_ & Ha)|Ha]]; [left; exact (Hst a Ha) | right; left | right; right; lia].
        destruct (HsKindB.block_low B API L' A' mem' md' _ _ (a - (q - 16)) HM' Hinq ltac:(lia)) as [_ Hlt].
        split; [lia|]. replace a with (q - 16 + (a - (q - 16))) by lia. apply Hqi. lia. }
      right. exists bs. split; [exact Hsome|]. split; [exact Hq0|]. split; [reflexivity|].
      split; [exact BYQ|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact (proj1 (DJ _ _ HinT))|].
      intros q' k Hq'. pose proof REL as (_ & _ & _ & _ & _ & U & _). destruct (U q' k Hq') as [Hq1 Ep].
      rewrite <- Ep. apply (proj1 (DJ (ptr_addr L q') k ltac:(unfold blocks; apply in_map_iff; exists (q', k); split; [reflexivity | exact Hq1]))). }
  destruct UNI as (bd & lenw' & Lam' & bnd' & R10' & BYL & LG' & RES' & UK & HE & ANS).
  assert (MID' : slot_mid B API regs0 L0 A0 mem0 md0 cnt0 L' A' regs' mem' md' lenw' Lam'
                   (b64_alloc_bound (slot_nn pl)) (cnt + 1) bnd').
  { eapply mid_call_c; [exact ENV | exact MID | exact CP | unfold DEC_STACK, ALLOC_STACK, SLOT_STACK; lia | exact HE | | |
      exact BYL | exact LG' | lia | exact RES' | exact RA'].
    - intros q' k _ Hq'. exact (ub_keep B API L A mem md A' HM UK q' k Hq').
    - exact INIT. }
  assert (Hpt' : In (pt, slot_nn pl + 1) (user_blocks A')) by exact (ub_keep B API L A mem md A' HM UK _ _ Hpt).
  assert (Ept' : ptr_addr L' pt = text) by (rewrite (PA _ _ Hpt Hpt'); exact Ept).
  assert (BYT' : Mem.bytes_at (ms_segs B) mem' text (slot_db pl ++ [Z_to_bv 8 0])).
  { apply (bytes_keep _ mem mem' _ _ BYT). intros i Hi. rewrite length_app, Nat2Z.inj_add, Hdl in Hi. cbn in Hi.
    apply TK. rewrite Htb. lia. }
  pose proof MID' as (_ & REL' & R2' & RS' & FR' & _).
  pose proof LG' as ((W1 & W2 & W3 & W4) & HPk & HC1 & HF1 & _ & _).
  destruct (kb_md B API L' A' mem' md' HM') as [Hh Hl].
  assert (Hsp' : bv_unsigned (getr regs' 2) = spZ regs0 - 48)
    by exact (eq_trans (f_equal bv_unsigned (RP 2 ltac:(unfold callee_saved; lia))) Hsp).
  eapply (kb_seg B regs' (Z_to_bv 64 0x133b0) mem' md' _ P Hh Hl SEG).
  - eapply sD_run with (nn := slot_nn pl) (lv := 0) (pk := b64_alloc_bound (slot_nn pl)) (lenw := lenw').
    + exact FAP.
    + exact CBA.
    + exact (eq_trans (RP 9 ltac:(unfold callee_saved; lia)) R9).
    + lia.
    + exact (eq_trans (RP 19 ltac:(unfold callee_saved; lia)) R19).
    + unfold b64_alloc_bound. lia.
    + unfold b64_alloc_bound. lia.
    + unfold b64_alloc_bound, check_bounded_alloc_c.b64_alloc_bound. lia.
    + rewrite <- SEG. apply word_mem_le8; [exact W2 | unfold b64_alloc_bound; lia | lia | lia].
    + rewrite Hsp', <- SEG. exact BYL.
  - intros ms' (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->). do 3 eexists. reflexivity.
  - intros R pc' m2 regs2 HQ HG.
    destruct HQ as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & EQ).
    injection EQ as ER Epc Em. subst R pc' m2.
    apply (KC L' A'). exists lenw', Lam', (b64_alloc_bound (slot_nn pl)), (cnt + 1), bnd', bd, pt, text.
    split.
    { split.
      { apply (mid_regs B API regs0 L0 A0 mem0 md0 cnt0 L' A' regs' mem' md' _ _ _ _ _ regs2 MID').
        - rewrite HG. reflexivity.
        - slot_kept HG. }
      split; [exact Hpt'|]. split; [exact Ept'|]. split; [exact H16|]. split; [exact FA0|].
      split; [exact BYT'|]. split; [exact ANS | exact Hnn]. }
    split; [lia|].
    split; [rewrite HG; reflexivity|].
    split; [rewrite HG; exact (eq_trans (RP 8 ltac:(unfold callee_saved; lia)) R8)|].
    split; [rewrite HG; exact (eq_trans (RP 9 ltac:(unfold callee_saved; lia)) R9)|].
    split; [rewrite HG; exact (eq_trans (RP 8 ltac:(unfold callee_saved; lia)) R8)|].
    split; [rewrite HG; exact R10'|].
    split; [rewrite HG; reflexivity|].
    split; [rewrite HG; exact R10'|].
    rewrite HG. exact (eq_trans (RP 19 ltac:(unfold callee_saved; lia)) R19).
Qed.

End D.
