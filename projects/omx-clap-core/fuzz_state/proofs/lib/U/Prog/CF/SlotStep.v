(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, module names, addresses and numbers changed; 583 of its 659 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/CF/past_nul.v, with its module paths and module names changed; 284 of its 325 lines of code are new or changed and 618 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem Frame Cells Step Exec.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger GIInit SlotInv.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require AllocSI AllocGS.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require HsKindB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF.
Import ListNotations.
Local Open Scope Z_scope.

(* The state of the entry function at its call sites, against the slot's start state (regs0, L0, A0, mem0, md0):
   the slot relation, the 48-byte frame with its saved registers, the allocation ledger, the resource bound. *)

Section Step.
Context {fx : FPState} {rc : RunCeil} {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Definition slot_env : Prop :=
  ms_segs B = rsegs /\ ms_malloc B = 0x16c7c /\ ms_free B = 0x16b3c /\
  errno_addr B + 4 <= alloc_ceiling /\
  AllocExtra B MR /\ block_slack_present B API /\ globals_free B API omx_G /\
  (forall a, (sk_ofl_head <= a < sk_ofl_head + 8) \/ a = sk_threaded \/ (sk_ofl_lock <= a < sk_ofl_lock + 4) ->
     in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ errno_at B a /\
     ~ in_globals omx_G a).

Definition slot_sp (regs0 : bvmap 5 word) : Prop :=
  spZ regs0 mod 16 = 0 /\ alloc_ceiling + SLOT_STACK <= spZ regs0 /\ spZ regs0 <= 2 ^ 47 /\
  getr regs0 4 = Z_to_bv 64 (ms_tp B).

Definition slot_cells (regs0 : bvmap 5 word) (lenw : word) : list Cells.cell :=
  [Cells.C8 lenw; Cells.C8 (getr regs0 19); Cells.C8 (getr regs0 18); Cells.C8 (getr regs0 9);
   Cells.C8 (getr regs0 8); Cells.C8 (getr regs0 1)].

Definition slot_mid (regs0 : bvmap 5 word) (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model)
    (cnt0 : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (lenw : word) (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound) : Prop :=
  slot_sp regs0 /\
  slot_rel B API omx_G SLOT_STACK (spZ regs0) L0 A0 mem0 md0 L A mem md /\
  getr regs 2 = Z_to_bv 64 (spZ regs0 - 48) /\
  (forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> getr regs (Z_to_bv 5 k) = getr regs0 (Z_to_bv 5 k)) /\
  Step.rw_cells rsegs mem (spZ regs0 - 48) (slot_cells regs0 lenw) /\
  ledger B L A mem Lam peak cnt (2 ^ 64 - 1) /\ cnt0 <= cnt <= cnt0 + 100 /\
  res_ok_slots A bnd /\ ro_agree (ms_segs B) mem /\ frm_zero fp_csr.

Definition slot_fin (regs0 : bvmap 5 word) (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model)
    (ra p n : Z) (b : sbound) (j : nat) (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    lib_post_g B API omx_G SLOT_STACK L0 A0 regs0 mem0 md0 p n b (LL 0 (m_fs md0) []) L' A' regs' mem' md' /\
    omx_GI B (S j) mem'.

Lemma slot_img_low : slot_env -> img_low B.
Proof.
  intros (SEG & _). pose proof alloc_ceiling_val as Hc.
  apply (img_low_of_check B 0x55000); [unfold img_check; rewrite SEG; vm_compute; reflexivity | lia].
Qed.

Lemma slot_sp_lo : forall regs0, slot_sp regs0 -> alloc_ceiling + SLOT_STACK <= spZ regs0 /\ spZ regs0 <= 2 ^ 47.
Proof. intros regs0 (_ & H1 & H2 & _). split; assumption. Qed.

Lemma mid_spZ : forall regs0 regs, slot_sp regs0 -> getr regs 2 = Z_to_bv 64 (spZ regs0 - 48) ->
  spZ regs = spZ regs0 - 48.
Proof.
  intros regs0 regs (_ & H1 & H2 & _) H. unfold spZ at 1. rewrite H.
  pose proof alloc_ceiling_val. unfold SLOT_STACK in *. rewrite MState.unsigned_lit by lia. reflexivity.
Qed.

Lemma mid_pre : forall regs0 L0 A0 mem0 md0 cnt0 L A regs mem md lenw Lam peak cnt bnd Kc,
  slot_mid regs0 L0 A0 mem0 md0 cnt0 L A regs mem md lenw Lam peak cnt bnd ->
  0 <= Kc <= SLOT_STACK - 48 -> lib.Reusable.YK0s.ret_ok (getr regs 1) ->
  call_pre_k B MR Kc L A regs mem md.
Proof.
  intros regs0 L0 A0 mem0 md0 cnt0 L A regs mem md lenw Lam peak cnt bnd Kc
    (SP & REL & R2 & RS & _) HK Hra.
  pose proof (mid_spZ regs0 regs SP R2) as Hsp. destruct SP as (H16 & Hlo & Hhi & Htp).
  pose proof alloc_ceiling_val. unfold SLOT_STACK in *.
  apply (slot_rel_pre B API omx_G SLOT_STACK (spZ regs0) L0 A0 mem0 md0 L A mem md Kc regs REL);
    unfold SLOT_STACK;
    first [ exact Hra | exact (eq_trans (RS 4 ltac:(lia)) Htp) | rewrite Hsp; Z.div_mod_to_equations; lia | lia ].
Qed.

Lemma mid_call : slot_env ->
  forall regs0 L0 A0 mem0 md0 cnt0 L A regs mem md lenw Lam peak cnt bnd Kc E L' A' regs' mem' md'
    Lam' peak' cnt' bnd',
  slot_mid regs0 L0 A0 mem0 md0 cnt0 L A regs mem md lenw Lam peak cnt bnd ->
  call_post_k B MR Kc L A regs mem md E L' A' regs' mem' md' ->
  0 <= Kc <= SLOT_STACK - 48 ->
  (forall a, E a -> in_globals omx_G a \/ (0 <= a < alloc_ceiling /\ ~ in_img B a)) ->
  (forall q k, In (q, k) (user_blocks A0) -> In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) ->
  (st_init_done A = true -> st_init_done A' = true) ->
  ledger B L' A' mem' Lam' peak' cnt' (2 ^ 64 - 1) -> cnt0 <= cnt' <= cnt0 + 100 ->
  res_ok_slots A' bnd' -> ro_agree (ms_segs B) mem' ->
  slot_mid regs0 L0 A0 mem0 md0 cnt0 L' A' regs' mem' md' lenw Lam' peak' cnt' bnd'.
Proof.
  intros ENV regs0 L0 A0 mem0 md0 cnt0 L A regs mem md lenw Lam peak cnt bnd Kc E L' A' regs' mem' md'
    Lam' peak' cnt' bnd' (SP & REL & R2 & RS & FR & _ & _ & _ & _ & FZ) CP HK HE HU HI LG HC RES RA.
  pose proof ENV as (SEG & _ & _ & ERR & AX & _ & GF & _).
  pose proof (slot_img_low ENV) as IL. pose proof IL as [ILi _].
  pose proof (mid_spZ regs0 regs SP R2) as Hsp. pose proof SP as (H16 & Hlo & Hhi & Htp).
  pose proof alloc_ceiling_val. pose proof alloc_ceiling_lt. unfold SLOT_STACK in *.
  pose proof CP as (HM' & _ & _ & _ & _ & RP & _ & HF & _).
  pose proof REL as (HM & _).
  assert (Elow : forall a, E a -> 0 <= a < alloc_ceiling).
  { intros a Ha. destruct (HE a Ha) as [Hg|Hl]; [|tauto].
    destruct (GF a Hg) as (_ & Hr & _). exact Hr. }
  split; [exact SP|].
  split.
  { apply (slot_rel_call B API AX IL omx_G SLOT_STACK (spZ regs0) L0 A0 mem0 md0 L A mem md Kc regs E L' A' regs' mem' md'
      REL CP); unfold SLOT_STACK; try lia.
    - intros a Ha _ He. pose proof (Elow a He). lia.
    - intros a Hi _ _ _ Hg He. destruct (HE a He) as [Hg'|(_ & Hn)]; [exact (Hg Hg') | exact (Hn Hi)].
    - intros a Ha _. right. intros He. pose proof (Elow a He). lia.
    - exact HU.
    - exact HI. }
  split; [exact (eq_trans (RP 2 ltac:(unfold callee_saved; lia)) R2)|].
  split; [intros k Hk; exact (eq_trans (RP k ltac:(unfold callee_saved; lia)) (RS k Hk))|].
  split.
  { apply (lib.U.Prog.HsKindB.rw_cells_keep mem mem' _ _ FR). intros a Ha. cbn [slot_cells Cells.cells_size Cells.csize Nat.add] in Ha.
    rewrite <- SEG. apply HF.
    - left. lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM' Ho). lia.
    - unfold scratch_k. rewrite Hsp. lia.
    - intros He. pose proof (Elow a He). lia. }
  split; [exact LG|]. split; [exact HC|]. split; [exact RES|]. split; [exact RA | exact FZ].
Qed.

Definition slot_start (regs0 : bvmap 5 word) (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model)
    (p0 : Z) (pl : list byte) (peak0 cnt0 : Z) (j : nat) : Prop :=
  slot_sp regs0 /\ MR L0 A0 mem0 md0 /\ WF A0 /\ bounded A0 /\ st_init_done A0 = true /\
  (forall a, (spZ regs0 - SLOT_STACK <= a < spZ regs0) \/ errno_at B a -> writable_at (ms_segs B) mem0 a) /\
  lib.Reusable.YK0s.ret_ok (getr regs0 1) /\
  getr regs0 10 = Z_to_bv 64 p0 /\ getr regs0 11 = Z_to_bv 64 (Z.of_nat (length pl)) /\
  0 < p0 /\ p0 + Z.of_nat (length pl) <= alloc_ceiling /\
  (pl = [] \/ exists q, In (q, Z.of_nat (length pl)) (user_blocks A0) /\ ptr_addr L0 q = p0) /\
  blk_data B mem0 p0 pl /\ ro_agree (ms_segs B) mem0 /\
  Fs.fs_sorted (m_fs md0) = true /\ sink_none B mem0 md0 /\
  alloc_words B mem0 0 peak0 cnt0 (2 ^ 64 - 1) /\ 0 <= peak0 < 2 ^ 64 /\ 0 <= cnt0 <= Z.of_nat j * 2 ^ 60 /\
  (j < 4)%nat.

Lemma start_ledger : forall regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j,
  slot_start regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j -> ledger B L0 A0 mem0 [] peak0 cnt0 (2 ^ 64 - 1).
Proof.
  intros regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AW & HP & HC & HJ).
  unfold ledger. cbn [lsum map]. split; [exact AW|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; constructor.
Qed.

Lemma alloc_words_present : forall mem live peak cnt fail, alloc_words B mem live peak cnt fail ->
  forall a, in_globals omx_G a -> mbyte (ms_segs B) mem a <> None.
Proof.
  intros mem live peak cnt fail (W1 & W2 & W3 & W4) a (lo & len & Hin & Hr).
  cbn [omx_G In] in Hin. unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
  destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-;
    [pose proof W1 as W | pose proof W2 as W | pose proof W3 as W | pose proof W4 as W];
    match type of W with word_mem _ _ ?g _ =>
      replace a with (g + Z.of_nat (Z.to_nat (a - g))) by lia; rewrite (W (Z.to_nat (a - g))) by lia; discriminate
    end.
Qed.

Lemma seg_img : slot_env -> forall a seg, find_segment rsegs a 1 = Some seg -> in_img B a.
Proof.
  intros (SEG & _) a seg F.
  destruct (kb_find_segment rsegs a 1 seg F) as (Hin & H1 & H2).
  assert (C : forallb (fun s => existsb (fun r => (bv_unsigned (fst r) <=? Z.of_N (seg_base s)) &&
              (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? bv_unsigned (fst r) + bv_unsigned (snd r)))
              (segments_reserved rsegs)) rsegs = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C seg Hin). apply existsb_exists in C as (r & Hr & Hc).
  apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
  split.
  - rewrite SEG. intros E. pose proof (f_equal (@length Segment) E) as Le. vm_compute in Le. discriminate.
  - exists r. rewrite SEG. split; [exact Hr | lia].
Qed.

Lemma blocks_wmono : slot_env -> forall L A mem md mem', MR L A mem md -> Frame.wmono rsegs mem mem' ->
  forall q n i, In (q, n) (user_blocks A) -> 0 <= i < n ->
  mem (Z_to_bv 64 (ptr_addr L q + i)) <> None -> mem' (Z_to_bv 64 (ptr_addr L q + i)) <> None.
Proof.
  intros ENV L A mem md mem' HM WM q n i Hq Hi Hx E.
  pose proof ENV as (SEG & _ & _ & _ & AX & _).
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q n HM Hq) as R. pose proof alloc_ceiling_lt.
  assert (F : find_segment rsegs (bv_unsigned (Z_to_bv 64 (ptr_addr L q + i))) 1 = None).
  { rewrite MState.unsigned_lit by lia.
    destruct (find_segment rsegs (ptr_addr L q + i) 1) as [seg|] eqn:Fs; [|reflexivity].
    exfalso. exact (ax_blocks_img AX L A mem md q n i HM Hq Hi (seg_img ENV _ _ Fs)). }
  apply (WM (Z_to_bv 64 (ptr_addr L q + i))).
  - unfold wview. destruct (mem (Z_to_bv 64 (ptr_addr L q + i))) as [bb|]; [discriminate | exfalso; exact (Hx eq_refl)].
  - unfold wview. rewrite E, F. reflexivity.
Qed.

Lemma mid_A : slot_env ->
  forall regs0 L0 A0 mem0 md0 cnt0 L A regs mem md lenw Lam peak cnt bnd regs' mem' W Lam' peak' cnt',
  slot_mid regs0 L0 A0 mem0 md0 cnt0 L A regs mem md lenw Lam peak cnt bnd ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' ->
  (forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spZ regs0 - SLOT_STACK <= x < spZ regs0 - 48) -> Frame.outside W x) ->
  (forall x, in_img B x -> ~ in_globals omx_G x -> Frame.outside W x) ->
  (forall x, 0 <= x < alloc_ceiling -> owned B L A x -> Frame.outside W x) ->
  (forall q k i, In (q, k) (user_blocks A0) -> 0 <= i < k -> Frame.outside W (ptr_addr L0 q + i)) ->
  getr regs' 2 = Z_to_bv 64 (spZ regs0 - 48) ->
  (forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> getr regs' (Z_to_bv 5 k) = getr regs0 (Z_to_bv 5 k)) ->
  ledger B L A mem' Lam' peak' cnt' (2 ^ 64 - 1) -> cnt0 <= cnt' <= cnt0 + 100 -> ro_agree (ms_segs B) mem' ->
  slot_mid regs0 L0 A0 mem0 md0 cnt0 L A regs' mem' md lenw Lam' peak' cnt' bnd.
Proof.
  intros ENV regs0 L0 A0 mem0 md0 cnt0 L A regs mem md lenw Lam peak cnt bnd regs' mem' W Lam' peak' cnt'
    (SP & REL & R2 & RS & FR & _ & _ & RES & _ & FZ) MU WM HW1 HWi HW2 HW3 R2' RS' LG HC RA.
  pose proof ENV as (SEG & _). pose proof (slot_img_low ENV) as IL.
  pose proof SP as (H16 & Hlo & Hhi & Htp). pose proof alloc_ceiling_val. unfold SLOT_STACK in *.
  pose proof REL as (HM & _).
  split; [exact SP|].
  split.
  { apply (slot_rel_A B API IL omx_G SLOT_STACK (spZ regs0) L0 A0 mem0 md0 L A mem md mem' W REL MU).
    - rewrite SEG. exact WM.
    - exact (blocks_wmono ENV L A mem md mem' HM WM).
    - intros x Hx Hs. apply HW1; [exact Hx | unfold SLOT_STACK in *; lia].
    - exact HWi.
    - exact HW2.
    - exact HW3. }
  split; [exact R2'|]. split; [exact RS'|].
  split.
  { apply (lib.U.Prog.HsKindB.rw_cells_keep mem mem' _ _ FR). intros a Ha. cbn [slot_cells Cells.cells_size Cells.csize Nat.add] in Ha.
    assert (Ho : Frame.outside W a) by (apply HW1; lia).
    split; [exact (lib.U.Prog.HsKindB.mbyte_munch rsegs W mem mem' a MU ltac:(lia) Ho)
           | exact (lib.U.Prog.HsKindB.writable_munch rsegs W mem mem' a MU ltac:(lia) Ho)]. }
  split; [exact LG|]. split; [exact HC|]. split; [exact RES|]. split; [exact RA | exact FZ].
Qed.

Lemma fin_of : slot_env ->
  forall regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j ra b L A regs mem md peak cnt,
  slot_start regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j -> getr regs0 1 = Z_to_bv 64 ra ->
  slot_rel B API omx_G SLOT_STACK (spZ regs0) L0 A0 mem0 md0 L A mem md ->
  regs_preserved regs0 regs -> getr regs 10 = Z_to_bv 64 0 ->
  ledger B L A mem [] peak cnt (2 ^ 64 - 1) -> cnt <= cnt0 + 100 ->
  ro_agree (ms_segs B) mem -> res_ok_slots A (lib_delta (Z.of_nat (length pl)) b) -> frm_zero fp_csr ->
  slot_fin regs0 L0 A0 mem0 md0 ra p0 (Z.of_nat (length pl)) b j
    (mkCfg (mkst regs (Z_to_bv 64 ra) mem (seg_rom (ms_segs B))) md).
Proof.
  intros ENV regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j ra b L A regs mem md peak cnt HS HRA REL RP R10 LG HC RA RES FZ.
  pose proof ENV as (SEG & _ & _ & _ & _ & _ & GF & SNK).
  pose proof HS as (SP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HBLK & _ & _ & FS & SN & AW & _ & HCN & HJ).
  destruct LG as (AW' & HP & HC' & _ & _ & _). cbn [lsum] in *.
  exists fx, L, A, regs, mem, md.
  split; [reflexivity|]. split; [exact FZ|].
  split.
  { apply (slot_post B API omx_G SLOT_STACK L0 A0 regs0 mem0 md0 p0 (Z.of_nat (length pl)) b L A regs mem md
      REL R10 RP FS SN SNK).
    - intros a Ha. split; apply (globals_writable B API omx_G _ a GF Ha).
      + exact (alloc_words_present mem0 _ _ _ _ AW a Ha).
      + exact (alloc_words_present mem _ _ _ _ AW' a Ha).
    - exact RA.
    - exact RES.
    - destruct pl as [|x pl']; [left; reflexivity|].
      destruct HBLK as [E|(q & Hq & Ep)]; [discriminate|]. right.
      split; [cbn [length]; lia | exists q; split; [exact Hq | exact Ep]]. }
  exists peak, cnt. split; [exact AW'|]. split; [lia|]. rewrite Nat2Z.inj_succ. split; lia.
Qed.

Definition slot_bnd (b : sbound) : Prop := sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ sb_cap b = CAP_AG.

Lemma bsum_blocks : forall L l,
  fold_right (fun b acc => snd b + acc) 0 (map (fun b => (ptr_addr L (fst b), snd b)) l) =
  fold_right (fun b acc => snd b + acc) 0 l.
Proof.
  intros L l. induction l as [|[q k] l IH]; [reflexivity|].
  change (k + fold_right (fun b acc => snd b + acc) 0 (map (fun b => (ptr_addr L (fst b), snd b)) l) =
          k + fold_right (fun b acc => snd b + acc) 0 l).
  rewrite IH. reflexivity.
Qed.

Lemma blocks_counts : forall L A L' A', blocks L' A' = blocks L A ->
  AllocSI.nblocks A' = AllocSI.nblocks A /\ AllocGS.ubytes A' = AllocGS.ubytes A.
Proof.
  intros L A L' A' E. unfold AllocSI.nblocks, AllocGS.ubytes. split.
  - rewrite <- (length_map (fun b => (ptr_addr L' (fst b), snd b)) (user_blocks A')).
    rewrite <- (length_map (fun b => (ptr_addr L (fst b), snd b)) (user_blocks A)).
    change (Z.of_nat (length (blocks L' A')) = Z.of_nat (length (blocks L A))). rewrite E. reflexivity.
  - rewrite <- (bsum_blocks L' (user_blocks A')), <- (bsum_blocks L (user_blocks A)).
    change (fold_right (fun b acc => snd b + acc) 0 (blocks L' A') = fold_right (fun b acc => snd b + acc) 0 (blocks L A)).
    rewrite E. reflexivity.
Qed.

Lemma res_restore : forall A A' b b', res_ok_slots A b -> res_ok_slots A' b' -> sb_cap b' = sb_cap b ->
  AllocSI.nblocks A' <= AllocSI.nblocks A -> AllocGS.ubytes A' <= AllocGS.ubytes A -> res_ok_slots A' b.
Proof.
  intros A A' b b' (_ & _ & _ & _ & _ & _ & N1 & U1 & L1 & Y1 & _) (H1 & H2 & H3 & H4 & H5 & H6 & _ & _ & _ & _ & Hh) Hc Hn Hu.
  rewrite Hc in Hh. repeat (split; [assumption|]). split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact Hh].
Qed.

Lemma res_same_blocks : forall L A L' A' b b', res_ok_slots A b -> res_ok_slots A' b' -> sb_cap b' = sb_cap b ->
  blocks L' A' = blocks L A -> res_ok_slots A' b.
Proof.
  intros L A L' A' b b' H1 H2 Hc E. destruct (blocks_counts L A L' A' E) as [N U].
  apply (res_restore A A' b b' H1 H2 Hc); lia.
Qed.

Lemma mid_regs : forall regs0 L0 A0 mem0 md0 cnt0 L A regs mem md lenw Lam peak cnt bnd regs',
  slot_mid regs0 L0 A0 mem0 md0 cnt0 L A regs mem md lenw Lam peak cnt bnd ->
  getr regs' 2 = getr regs 2 ->
  (forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> getr regs' (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k)) ->
  slot_mid regs0 L0 A0 mem0 md0 cnt0 L A regs' mem md lenw Lam peak cnt bnd.
Proof.
  intros regs0 L0 A0 mem0 md0 cnt0 L A regs mem md lenw Lam peak cnt bnd regs' (SP & REL & R2 & RS & REST) H2 HK.
  split; [exact SP|]. split; [exact REL|]. split; [exact (eq_trans H2 R2)|].
  split; [intros k Hk; exact (eq_trans (HK k Hk) (RS k Hk))|]. exact REST.
Qed.

Lemma start_data : forall regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j L A mem md,
  slot_start regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j ->
  slot_rel B API omx_G SLOT_STACK (spZ regs0) L0 A0 mem0 md0 L A mem md ->
  (forall k, (k <= length pl)%nat -> Mem.bytes_at (ms_segs B) mem p0 (firstn k pl)) /\
  (pl <> [] -> In (p0, Z.of_nat (length pl)) (blocks L A)).
Proof.
  intros regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j L A mem md HS (M & W & Bd & I & D & U & C & _).
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & Hpe & HBLK & BD & _).
  pose proof alloc_ceiling_lt.
  split.
  - intros k Hk. split; [lia|]. rewrite (firstn_length_le pl Hk). split; [lia|].
    intros i Hi.
    rewrite nth_error_firstn. destruct (i <? k)%nat eqn:E; [|apply Nat.ltb_ge in E; lia].
    change (Mem.mrd (ms_segs B) mem (Mem.wa (p0 + Z.of_nat i))) with (mbyte (ms_segs B) mem (p0 + Z.of_nat i)).
    destruct HBLK as [E0|(q & Hq & Ep)]; [subst pl; cbn in Hk; lia|].
    rewrite <- Ep. rewrite (C q _ (Z.of_nat i) Hq ltac:(lia)). rewrite Ep.
    rewrite (BD (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id. reflexivity.
  - intros Hne. destruct HBLK as [E0|(q & Hq & Ep)]; [contradiction|].
    destruct (U q _ Hq) as [Hq' Hpq]. unfold blocks. apply in_map_iff. exists (q, Z.of_nat (length pl)).
    cbn [fst snd]. rewrite Hpq, Ep. split; [reflexivity | exact Hq'].
Qed.

Lemma kb_seg : forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ms_segs B = rsegs ->
  Exec.evt rsegs Q (MState.MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall ms', Q ms' -> exists R pc' mem', ms' = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs)) ->
  (forall R pc' mem' regs', Q (MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs)) ->
     (forall r, getr regs' r = getr R r) ->
     SR (ms_segs B) (mkCfg (mkst regs' pc' mem' (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl SEG HE HS HK.
  apply (kb_run B regs pc mem md (fun R p m => Q (MState.MS R fp_regs p fp_csr None m (seg_rom rsegs))) P Hh Hl).
  - rewrite SEG. eapply Exec.evt_mono; [exact HE|]. intros ms' HQ. destruct (HS ms' HQ) as (R & p & m & E).
    exists R, p, m. split; [exact E | rewrite <- E; exact HQ].
  - intros R p m regs' HQ HG. rewrite SEG. rewrite SEG in HK. exact (HK R p m regs' HQ HG).
Qed.

End Step.
