(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1050 of its 1065 lines of code are new or changed and 32 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/CF/tx_put.v, with its module paths and module names changed; 14 of its 33 lines of code are new or changed and 1046 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/CF/tx_value.v, with its module paths and module names changed; 348 of its 372 lines of code are new or changed and 9 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import TlRuns.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import tx_put_c TxRet TxGlue TxCompose tx_line_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import TxCalls.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition accd (k : Z) : list byte := map (Z_to_bv 8) (concat (wind true k)).

Lemma concat_rep_snoc : forall n, concat (repeat [32; 32] n) ++ [32; 32] = concat (repeat [32; 32] (S n)).
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [repeat concat] in *. rewrite <- app_assoc. rewrite IH. reflexivity.
Qed.

Lemma accd_succ : forall k, 0 <= k -> accd k ++ [Z_to_bv 8 32; Z_to_bv 8 32] = accd (k + 1).
Proof.
  intros k Hk. unfold accd.
  change [Z_to_bv 8 32; Z_to_bv 8 32] with (map (Z_to_bv 8) [32; 32]). rewrite <- map_app. f_equal.
  unfold wind. replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia. cbn [concat].
  rewrite <- app_assoc. f_equal. apply concat_rep_snoc.
Qed.

Lemma accd_len : forall k, 0 <= k -> Z.of_nat (length (accd k)) = 1 + 2 * k.
Proof.
  intros k Hk. unfold accd, wind. rewrite length_map. cbn [concat length app].
  assert (E : forall n, length (concat (repeat [32; 32] n)) = (2 * n)%nat).
  { induction n as [|n IH]; [reflexivity|]. cbn [repeat concat]. rewrite length_app, IH. cbn [length]. lia. }
  rewrite E. lia.
Qed.

Definition kd (k : Z) : list Z := plen (wind true k).

Lemma map_rep : forall (X Y : Type) (f : X -> Y) x n, map f (repeat x n) = repeat (f x) n.
Proof. intros X Y f x n. induction n as [|n IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma rep_app : forall (X : Type) (x : X) n m, repeat x (n + m) = repeat x n ++ repeat x m.
Proof. intros X x n m. induction n as [|n IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma kd_split : forall m k, 0 <= m -> 0 < k -> kd (m + k) = kd m ++ [2] ++ repeat 2 (Z.to_nat (k - 1)).
Proof.
  intros m k Hm Hk. unfold kd, plen, wind.
  replace (Z.to_nat (m + k)) with (Z.to_nat m + S (Z.to_nat (k - 1)))%nat by lia.
  rewrite rep_app. cbn [map app]. rewrite !map_app, !map_rep. reflexivity.
Qed.

Lemma kd_succ : forall k, 0 <= k -> kd k ++ [2] = kd (k + 1).
Proof.
  intros k Hk. rewrite (kd_split k 1) by lia. replace (Z.to_nat (1 - 1)) with 0%nat by lia.
  rewrite app_nil_r. reflexivity.
Qed.

Definition canR (r : bvmap 5 word) :=
  mkR (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 1) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 2) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 4) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 5) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 6)
      (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 7) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 8) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 9) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 10) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 11) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 12)
      (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 13) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 14) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 15) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 16) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 17) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 18)
      (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 19) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 20) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 21) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 22) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 23) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 24)
      (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 25) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 26) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 27) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 28) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 29) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 30)
      (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 31).

Definition tl_fr (regs : bvmap 5 word) : list cell :=
  [C8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 18); C8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 9); C8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 8); C8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1)].

Ltac rp RP HR r :=
  first [ etransitivity; [exact (RP r ltac:(unfold callee_saved; lia)) | gval HR]
        | symmetry; etransitivity; [exact (RP r ltac:(unfold callee_saved; lia)) | gval HR] ].

Section KB.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRB : errno_addr B + 4 <= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling.
Hypothesis AX : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable.YL01.AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Variable F : ResForm.
#[local] Set Default Proof Using "All".

Definition tlQ (regs : bvmap 5 word) (t k : Z) (m : word -> option byte) : machine_state -> Prop :=
  tl_Q k (Z_to_bv 64 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32)) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) (Z_to_bv 64 t)
    (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 19) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 20) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 21) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 22) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 23)
    (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 24) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 25) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 26) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 27)
    (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 8) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 9) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 18) fp_regs fp_csr m.

Definition tl_inv (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (t d b0 len0 cap0 : Z) (txt : list byte) (bnd : rf_R F) (k : Z) : Prop :=
  forall regs2 pc2 mem2 md2 L2 A2 b2 cap2,
    evt rsegs (tlQ regs t k mem2) (MS (canR regs2) fp_regs pc2 fp_csr None mem2 (seg_rom rsegs)) ->
    tx_relx B API F TL_STACK regs t b0 len0 cap0 txt (accd (d - k)) bnd L A mem md L2 A2 mem2 md2 b2 cap2 (kd (d - k)) ->
    rw_cells rsegs mem2 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32) (tl_fr regs) ->
    SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs2 pc2 mem2 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md2)
      (tx_ret B API F TL_STACK L A regs mem md t b0 len0 cap0 txt (accd d) (kd d) bnd (fun _ _ _ => True)).

Lemma tl_sp : forall L A regs mem md t b0 len0 cap0 txt bnd ns need,
  tx_start B API F TL_STACK L A regs mem md t b0 len0 cap0 txt bnd ns need ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling + 8320 <= spZ regs /\ spZ regs < 2 ^ 63 /\ spZ regs mod 16 = 0 /\ spZ regs <= t /\
  t + 24 <= 2 ^ 64 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 10 = Z_to_bv 64 t.
Proof.
  intros L A regs mem md t b0 len0 cap0 txt bnd ns need
    ((_ & _ & _ & RET & SPal & SPK & SP63 & _) & _ & _ & R10 & SPT & Thi & _).
  unfold TL_STACK, TX_STACK, REALLOC_STACK, ALLOC_STACK in SPK.
  repeat split; try assumption; lia.
Qed.

Lemma tl_fr_keep : forall regs t R1 mem1 mem2, spZ R1 = spZ regs + -32 -> spZ regs <= t ->
  rw_cells rsegs mem1 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32) (tl_fr regs) ->
  (forall a, spZ R1 <= a < 2 ^ 64 -> ~ (t <= a < t + 24) ->
     mbyte (ms_segs B) mem2 a = mbyte (ms_segs B) mem1 a /\
     (writable_at (ms_segs B) mem1 a <-> writable_at (ms_segs B) mem2 a)) ->
  rw_cells rsegs mem2 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32) (tl_fr regs).
Proof.
  intros regs t R1 mem1 mem2 S1 SPT FR KEEP.
  apply (rw_cells_same mem1); [exact FR|]. intros a Ha. unfold tl_fr in Ha. cbn [cells_size csize] in Ha.
  pose proof (spZ_range regs) as SPR. unfold spZ in *.
  rewrite <- SEGS. destruct (KEEP a) as [E Wr]; [lia | lia |].
  split; [exact E | intros Wa; apply Wr; exact Wa].
Qed.

Lemma tl_nl_bytes : forall m, ro_agree (ms_segs B) m -> mbytes B m 0x10392 [Z_to_bv 8 10].
Proof.
  intros m RA i Hi. cbn [length Z.of_nat] in Hi. rewrite SEGS in RA |- *.
  assert (i = 0) as -> by lia.
  assert (RO : ro_addr rsegs (Z_to_bv 64 (0x10392 + 0)) = true) by (vm_compute; reflexivity).
  transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom rsegs (Z_to_bv 64 (0x10392 + 0))); [exact (RA _ RO) | vm_compute; reflexivity].
Qed.

Lemma tl_sp_bytes : forall m, ro_agree (ms_segs B) m -> mbytes B m 0x1039d [Z_to_bv 8 32; Z_to_bv 8 32].
Proof.
  intros m RA i Hi. cbn [length Z.of_nat] in Hi. rewrite SEGS in RA |- *.
  assert (i = 0 \/ i = 1) as [-> | ->] by lia.
  - assert (RO : ro_addr rsegs (Z_to_bv 64 (0x1039d + 0)) = true) by (vm_compute; reflexivity).
    transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom rsegs (Z_to_bv 64 (0x1039d + 0))); [exact (RA _ RO) | vm_compute; reflexivity].
  - assert (RO : ro_addr rsegs (Z_to_bv 64 (0x1039d + 1)) = true) by (vm_compute; reflexivity).
    transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom rsegs (Z_to_bv 64 (0x1039d + 1))); [exact (RA _ RO) | vm_compute; reflexivity].
Qed.

Lemma img_src_ok : forall stk regs t b0 len0 cap0 txt acc bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1 regs1 s n,
  tx_relx B API F stk regs t b0 len0 cap0 txt acc bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling <= spZ regs1 - TX_STACK -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling <= t -> 0 <= s -> s + n <= 2 ^ 40 ->
  (forall i, 0 <= i < n -> ro_addr rsegs (Z_to_bv 64 (s + i)) = true) ->
  forall i, 0 <= i < n ->
    ~ (t <= s + i < t + 24) /\ ~ (spZ regs1 - TX_STACK <= s + i < spZ regs1) /\ ~ (b1 <= s + i < b1 + cap1) /\
    (len0 + Z.of_nat (length acc) + n + 1 <= cap1 \/ spZ regs1 <= s + i \/
     Mem.ro_addr (ms_segs B) (Z_to_bv 64 (s + i)) = true \/
     exists a k, In (a, k) (blocks L1 A1) /\ a <> b1 /\ a <= s + i < a + k).
Proof.
  intros stk regs t b0 len0 cap0 txt acc bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1 regs1 s n R AC1 ACT Hs Hsn RO i Hi.
  pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  destruct R as ((M1 & _) & _ & _ & _ & _ & _ & _ & INV1 & _).
  split; [lia|]. split; [lia|]. split.
  - intros X. destruct (inv_low B API SEGS ERRB AX CTX _ _ _ _ _ _ _ _ _ M1 INV1 X) as [_ NI].
    apply NI. apply (ro_img B SEGS); [lia | exact (RO i Hi)].
  - right. right. left. rewrite SEGS. exact (RO i Hi).
Qed.

Lemma tl_done : forall L A regs mem md t d b0 len0 cap0 txt bnd L2 A2 mem2 md2 b2 cap2 ms',
  tx_start B API F TL_STACK L A regs mem md t b0 len0 cap0 txt bnd (kd d) (len0 + 1 + 2 * d + 1) ->
  tx_relx B API F TL_STACK regs t b0 len0 cap0 txt (accd d) bnd L A mem md L2 A2 mem2 md2 b2 cap2 (kd d) ->
  (exists can, tlQ regs t 0 mem2 can /\ Regs6ss.ms_eqv can ms') ->
  SR (ms_segs B) (mkCfg ms' md2)
    (tx_ret B API F TL_STACK L A regs mem md t b0 len0 cap0 txt (accd d) (kd d) bnd (fun _ _ _ => True)).
Proof.
  intros L A regs mem md t d b0 len0 cap0 txt bnd L2 A2 mem2 md2 b2 cap2 ms' ST R (can & HQ & EQV).
  destruct (tl_sp _ _ _ _ _ _ _ _ _ _ _ _ _ ST) as (SPK & SP63 & SPal & SPT & Thi & RET & R10).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV. unfold spZ in *.
  unfold tlQ, tl_Q in HQ.
  destruct HQ as [(Hk & _)|(_ & x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & ->)];
    [lia|].
  destruct (eqv_final _ _ _ _ _ _ _ EQV eq_refl eq_refl) as (EMS & HR).
  assert (ESP : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32)) + 32) = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2).
  { rewrite unsigned_lit by lia.
    replace (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32 + 32) with (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2)) by lia.
    apply Z_to_bv_bv_unsigned. }
  rewrite ESP in HR.
  rewrite EMS. apply SR_ret.
  exists L2, A2, (ms_regs ms'), mem2, md2.
  split. { rewrite ret_ok_pc by exact RET. rewrite SEGS. reflexivity. }
  split. { regs_pres HR. }
  split. { exists b2, cap2. exact R. }
  exact I.
Qed.

Lemma tl_next : tx_put_contract B API F ->
  forall L A regs mem md t d b0 len0 cap0 txt bnd k L2 A2 mem2 md2 b2 cap2 ms',
  tx_start B API F TL_STACK L A regs mem md t b0 len0 cap0 txt bnd (kd d) (len0 + 1 + 2 * d + 1) ->
  0 <= d <= 2 ^ 31 - 1 -> 0 < k <= d ->
  tx_relx B API F TL_STACK regs t b0 len0 cap0 txt (accd (d - k)) bnd L A mem md L2 A2 mem2 md2 b2 cap2 (kd (d - k)) ->
  rw_cells rsegs mem2 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32) (tl_fr regs) ->
  (exists can, tlQ regs t k mem2 can /\ Regs6ss.ms_eqv can ms') ->
  tl_inv L A regs mem md t d b0 len0 cap0 txt bnd (k - 1) ->
  SR (ms_segs B) (mkCfg ms' md2)
    (tx_ret B API F TL_STACK L A regs mem md t b0 len0 cap0 txt (accd d) (kd d) bnd (fun _ _ _ => True)).
Proof.
  intros TXP L A regs mem md t d b0 len0 cap0 txt bnd k L2 A2 mem2 md2 b2 cap2 ms' ST Hd Hk R FR
    (can & HQ & EQV) IH.
  destruct (tl_sp _ _ _ _ _ _ _ _ _ _ _ _ _ ST) as (SPK & SP63 & SPal & SPT & Thi & RET & R10).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  pose proof R as (_ & _ & _ & _ & _ & _ & _ & _ & RA2 & _).
  unfold tlQ, tl_Q in HQ.
  destruct HQ as [(_ & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->)|(Hk0 & _)]; [|lia].
  destruct (eqv_final _ _ _ _ _ _ _ EQV eq_refl eq_refl) as (EMS & HR).
  set (R1 := ms_regs ms') in *.
  assert (G1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 1 = Z_to_bv 64 0x15abc) by gval HR.
  assert (G2 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 2 = Z_to_bv 64 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32)) by gval HR.
  assert (S1 : spZ R1 = spZ regs + -32).
  { unfold spZ in *. transitivity (bv_unsigned (Z_to_bv 64 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32)));
      [f_equal; exact G2 | apply unsigned_lit; lia]. }
  rewrite EMS.
  replace (seg_rom rsegs) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B)) by (rewrite SEGS; reflexivity).
  change (Z_to_bv 64 0x154b8) with (Z_to_bv 64 TX_PUT).
  eapply (tx_put_call B API SEGS ERRB AX CTX F TXP TL_STACK L A regs mem md t b0 len0 cap0 txt bnd
            (kd d) (len0 + 1 + 2 * d + 1) (accd (d - k)) L2 A2 mem2 md2 b2 cap2 (kd (d - k)) R1 0x1039d 2
            [Z_to_bv 8 32; Z_to_bv 8 32] (repeat 2 (Z.to_nat (k - 1))) _ ST R).
  - rewrite <- (kd_split (d - k) k) by lia. f_equal. lia.
  - rewrite S1. unfold TL_STACK. lia.
  - rewrite S1. lia.
  - rewrite S1. Z.div_mod_to_equations. lia.
  - rewrite G1. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok. vm_compute. reflexivity.
  - gval HR.
  - gval HR.
  - gval HR.
  - gval HR.
  - lia.
  - lia.
  - lia.
  - apply tl_sp_bytes. exact RA2.
  - reflexivity.
  - apply (img_src_ok TL_STACK regs t b0 len0 cap0 txt (accd (d - k)) bnd L A mem md L2 A2 mem2 md2 b2 cap2 (kd (d - k))
             R1 0x1039d 2 R).
    + rewrite S1. unfold TX_STACK, REALLOC_STACK, ALLOC_STACK. lia.
    + lia.
    + lia.
    + lia.
    + intros i Hi. assert (i = 0 \/ i = 1) as [-> | ->] by lia; vm_compute; reflexivity.
  - rewrite accd_len by lia. cbn [length Z.of_nat]. lia.
  - intros L3 A3 regs3 mem3 md3 RP (b3 & cap3 & R3) KEEP.
    rewrite G1.
    assert (FR3 : rw_cells rsegs mem3 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32) (tl_fr regs))
      by exact (tl_fr_keep regs t R1 mem2 mem3 S1 SPT FR KEEP).
    apply (IH regs3 (Z_to_bv 64 0x15abc) mem3 md3 L3 A3 b3 cap3).
    + unfold canR.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 2) with (Z_to_bv 64 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32)) by rp RP HR 2.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 3) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) by rp RP HR 3.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 4) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) by rp RP HR 4.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 8) with (Z_to_bv 64 k) by rp RP HR 8.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 9) with (Z_to_bv 64 t) by rp RP HR 9.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 18) with (Z_to_bv 64 0x1039d) by rp RP HR 18.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 19) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 19) by rp RP HR 19.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 20) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 20) by rp RP HR 20.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 21) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 21) by rp RP HR 21.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 22) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 22) by rp RP HR 22.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 23) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 23) by rp RP HR 23.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 24) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 24) by rp RP HR 24.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 25) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 25) by rp RP HR 25.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 26) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 26) by rp RP HR 26.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 27) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 27) by rp RP HR 27.
      unfold tlQ. unfold spZ in *.
      apply tl_seg2; [lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; exact FR3].
    + rewrite accd_succ, kd_succ in R3 by lia. replace (d - k + 1) with (d - (k - 1)) in R3 by lia. exact R3.
    + exact FR3.
Qed.

Lemma tl_inv_all : tx_put_contract B API F ->
  forall L A regs mem md t d b0 len0 cap0 txt bnd,
  tx_start B API F TL_STACK L A regs mem md t b0 len0 cap0 txt bnd (kd d) (len0 + 1 + 2 * d + 1) ->
  0 <= d <= 2 ^ 31 - 1 ->
  forall n : nat, Z.of_nat n <= d -> tl_inv L A regs mem md t d b0 len0 cap0 txt bnd (Z.of_nat n).
Proof.
  intros TXP L A regs mem md t d b0 len0 cap0 txt bnd ST Hd n.
  induction n as [|n IH]; intros Hn regs2 pc2 mem2 md2 L2 A2 b2 cap2 HE R FR;
    pose proof R as ((M2 & _) & _); destruct (mr_model _ _ (aa_laws API) _ _ _ _ M2) as (Hh & Hlz & _);
    eapply (sr_evt B SEGS regs2 pc2 mem2 md2 _ _ Hh Hlz HE); intros ms' HX.
  - cbn [Z.of_nat] in R. rewrite Z.sub_0_r in R.
    exact (tl_done L A regs mem md t d b0 len0 cap0 txt bnd L2 A2 mem2 md2 b2 cap2 ms' ST R HX).
  - apply (tl_next TXP L A regs mem md t d b0 len0 cap0 txt bnd (Z.of_nat (S n)) L2 A2 mem2 md2 b2 cap2 ms'
             ST Hd ltac:(lia) R FR HX).
    replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia. apply IH. lia.
Qed.

Theorem tx_line_holds : tx_put_contract B API F -> tx_line_contract B API F.
Proof.
  intros TXP. unfold tx_line_contract.
  intros L A regs mem md t d b0 len0 cap0 txt bnd. cbv zeta. intros ST R11 Hd.
  change (map (Z_to_bv 8) (concat (wind true d))) with (accd d).
  pose proof ST as (PRE & IN & RA & _ & _ & _ & _ & TW & _ & _ & _ & REC & INV & _ & RES & _).
  pose proof PRE as (M & W & BD & _ & _ & SPK & SP63 & SWR & _ & ERRW & _).
  destruct (tl_sp _ _ _ _ _ _ _ _ _ _ _ _ _ ST) as (_ & _ & SPal & SPT & Thi & RET & R10).
  destruct (tx_start_facts B API SEGS ERRB AX CTX F _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST) as (_ & _ & _ & _ & _ & WIN & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ M) as (Hh & Hlz & _).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  unfold TL_STACK, TX_STACK, REALLOC_STACK, ALLOC_STACK in SPK, SWR.
  assert (RAr : ro_agree rsegs mem) by (rewrite <- SEGS; exact RA).
  assert (FRP : forall i, 0 <= i < 32 -> present mem (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32 + i)).
  { intros i Hi. unfold spZ in *. apply (present_of_writable B SEGS); [lia | left; lia | apply SWR; lia]. }
  edestruct (rw_of_present mem (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32) 32) as [j FRJ];
    [unfold spZ in *; lia | unfold spZ in *; lia | lia | exact FRP |].
  change (Z.to_nat 32) with 32%nat in FRJ.
  assert (FRN : rw_cells rsegs (normalize rsegs mem) (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32) [CB 32 j]).
  { apply rw_cells_norm; [exact RAr | exact FRJ |]. intros i Hi. cbn in Hi. unfold spZ in *.
    apply (ro_false B SEGS); [lia | left; lia]. }
  pose proof (mem_inv_normalize rsegs mem) as MIN.
  eapply (sr_evt_n B SEGS regs _ mem md); [exact Hh | exact Hlz | exact RAr | |].
  { unfold TX_LINE. eapply tl_pro; [exact FRN | exact MIN]. }
  intros ms' (can & s0 & HQ & HREL & RS & EQV).
  destruct HQ as (m0' & -> & MU & WM & FR0).
  destruct (final_n _ _ _ _ _ _ _ _ HREL EQV eq_refl eq_refl) as (EMS & HR & MRL & EM).
  rewrite <- EM in RS.
  pose proof (munch_rel rsegs _ mem (normalize rsegs mem) (ms_mem ms') m0' (mem_rel_normalize rsegs mem RAr) MRL RS MU)
    as MU'.
  pose proof (wmono_rel rsegs mem (normalize rsegs mem) (ms_mem ms') m0' (mem_rel_normalize rsegs mem RAr) MRL RS WM)
    as WM'.
  pose proof (ro_agree_same rsegs mem (ms_mem ms') RAr RS) as RA1.
  pose proof (rw_cells_rel _ _ _ _ MRL FR0) as FR1.
  clear MU WM FR0.
  rewrite R10, R11 in HR.
  set (R1 := ms_regs ms') in *. set (mem1 := ms_mem ms') in *.
  assert (R0 : tx_relx B API F TL_STACK regs t b0 len0 cap0 txt [] bnd L A mem md L A mem1 md b0 cap0 []).
  { apply (tx_rel_frame B API SEGS ERRB AX CTX F TL_STACK regs t b0 len0 cap0 txt bnd L A mem md mem1
             (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32) (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32 + 32));
      try assumption.
    - rewrite SEGS. exact RA1.
    - intros a Ha. unfold spZ, TL_STACK, TX_STACK, REALLOC_STACK, ALLOC_STACK in *. lia. }
  assert (G1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 1 = Z_to_bv 64 0x15aa0) by gval HR.
  assert (G2 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 2 = Z_to_bv 64 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32)) by gval HR.
  assert (S1 : spZ R1 = spZ regs + -32).
  { unfold spZ in *. transitivity (bv_unsigned (Z_to_bv 64 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32)));
      [f_equal; exact G2 | apply unsigned_lit; lia]. }
  rewrite EMS.
  replace (seg_rom rsegs) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B)) by (rewrite SEGS; reflexivity).
  change (Z_to_bv 64 0x154b8) with (Z_to_bv 64 TX_PUT).
  eapply (tx_put_call B API SEGS ERRB AX CTX F TXP TL_STACK L A regs mem md t b0 len0 cap0 txt bnd
            (kd d) (len0 + 1 + 2 * d + 1) [] L A mem1 md b0 cap0 [] R1 0x10392 1 [Z_to_bv 8 10] (repeat 2 (Z.to_nat d)) _ ST R0).
  - unfold kd, plen, wind. cbn [map app]. rewrite map_rep. reflexivity.
  - rewrite S1. unfold TL_STACK. lia.
  - rewrite S1. lia.
  - rewrite S1. unfold spZ in *. Z.div_mod_to_equations. lia.
  - rewrite G1. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok. vm_compute. reflexivity.
  - gval HR.
  - gval HR.
  - gval HR.
  - gval HR.
  - lia.
  - lia.
  - lia.
  - apply tl_nl_bytes. rewrite SEGS. exact RA1.
  - reflexivity.
  - apply (img_src_ok TL_STACK regs t b0 len0 cap0 txt [] bnd L A mem md L A mem1 md b0 cap0 [] R1 0x10392 1 R0).
    + rewrite S1. unfold spZ, TX_STACK, REALLOC_STACK, ALLOC_STACK in *. lia.
    + unfold spZ in *. lia.
    + lia.
    + lia.
    + intros i Hi. assert (i = 0) as -> by lia. vm_compute. reflexivity.
  - cbn [length Z.of_nat]. lia.
  - intros L2 A2 regs2 mem2 md2 RP (b2 & cap2 & R2) KEEP.
    rewrite G1.
    assert (FR2 : rw_cells rsegs mem2 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32) (tl_fr regs))
      by exact (tl_fr_keep regs t R1 mem1 mem2 S1 SPT FR1 KEEP).
    pose proof (tl_inv_all TXP L A regs mem md t d b0 len0 cap0 txt bnd ST Hd (Z.to_nat d) ltac:(lia)) as LOOP.
    rewrite Z2Nat.id in LOOP by lia.
    apply (LOOP regs2 (Z_to_bv 64 0x15aa0) mem2 md2 L2 A2 b2 cap2).
    + unfold canR.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 2) with (Z_to_bv 64 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32)) by rp RP HR 2.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 3) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) by rp RP HR 3.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 4) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) by rp RP HR 4.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 8) with (Z_to_bv 64 d) by rp RP HR 8.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 9) with (Z_to_bv 64 t) by rp RP HR 9.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 19) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 19) by rp RP HR 19.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 20) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 20) by rp RP HR 20.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 21) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 21) by rp RP HR 21.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 22) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 22) by rp RP HR 22.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 23) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 23) by rp RP HR 23.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 24) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 24) by rp RP HR 24.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 25) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 25) by rp RP HR 25.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 26) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 26) by rp RP HR 26.
      replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 27) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 27) by rp RP HR 27.
      unfold tlQ. unfold spZ in *.
      apply tl_seg1; [lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; exact FR2].
    + replace (d - d) with 0 by lia. exact R2.
    + exact FR2.
Qed.

End KB.
