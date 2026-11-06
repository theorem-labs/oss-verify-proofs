(* reac_box_model_block (image B, asan-ubsan, libreac v1.9.0): piece V of pb_reac_box_model_block (plan of record
   pb_reac_box_model_block.plan.md (a working note, not in this delivery), a Theorem Labs lane).

   mbB_rngW: the footprint premise of the proved _F run, B.Prog.reac_box_model_blockF.mbF_rng, at
   RNG := ProgBridge.RNG_W (w_H W) over the normalized memory, from facts at a memory m with AR (the first conjunct
   of the caller's journal).  Each footprint range is a range of visible bytes (ProgBridge.rng_of_visible):
     the image                     ProgBridge.img_vis_W
     the window [sp - 4272, sp)    the journal's window clause (apresent, YCbq.v:368)
     the window's shadow cover     am_zshadow's stack row (YG0n.v:188-191; the stack bounds are page-aligned)
     the side stack and the shadow am_areas (AF 0, kFakeStackSize) and (ASh (AF kFakeFramesOff), ..) (YG0n.v:137-139)
       of its class-0 frames
     the thread cells (fp_tls)     am_const under CtrlTSyms B (YF0x.tfib_const_lookup{,_sym}): the rows pin the
                                   witnesses that asan_tls_cells reads and make the off-image cells visible
     the row, the name             garr8 over mrestrict (w_H W) and shadow_hull_vis (the spec's own premises)
     o                             apresent and shadow_hull_vis (the spec's own premises)
     the JOIN shadow covers        am_zshadow rows (0x219e0, 0x60) / (0x21a60, 0x20) and the four redzone const rows
                                   0x7fffc348 .. 0x7fffc34b of B's bundle (YF0m.v:2371-2374, 2961-2962)
     RngBytes.rng_bytes            ProgBridge.rng_bytes_RNG_W
   The shadow consequences shcov / shspan / shkov come from the 8-aligned covers by reac_box_model_blockF.v's
   mbF_cov0 / mbF_span0 / mbF_kov0.

   rule 24: no function proved (the footprint premise of the proved run reac_box_model_block_holds_F). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcSynth.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c RcAsanFP RcAsanFPLib
  reac_box_model_block_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_box_model_blockF ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YI16 YI04 YK04 YP09 YO0f YA0n YG0f YG0v
  YG0n YG0d YCbq YI00 YF0m YF0x.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.MemNorm B.ProgBridge.
Import ListNotations.
Open Scope Z_scope.

(* ---- Visibility from the view, from a value in the restricted memory, from garr8 ---------------------------- *)

(* A hidden byte is in no segment (w_Hoff), so the rom reads nothing there. *)
Lemma mbV_hid_rom : forall (W : lib.Reusable.YA0n.world rsegs) (x : Z),
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 x) = true -> lib.Reusable.YK11.seg_rom rsegs (Z_to_bv 64 x) = None.
Proof.
  intros W x E. unfold lib.Reusable.YK11.seg_rom. cbv beta. unfold memory_read. change (Z.of_N 1) with 1.
  rewrite (lib.Reusable.YA0n.w_Hoff W _ E). reflexivity.
Qed.

(* A byte of the restricted memory is visible, and it is the byte mrd reads in the memory. *)
Lemma mbV_mbyte : forall (W : lib.Reusable.YA0n.world rsegs) (m : word -> option byte) (x : Z) (b : byte),
  lib.Reusable.YP09.mbyte rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) m) x = Some b ->
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 x) = false /\ mrd rsegs m (Z_to_bv 64 x) = Some b.
Proof.
  intros W m x b H. unfold lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in H. cbv beta in H.
  revert H. destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 x)) eqn:E; intros H.
  - rewrite (mbV_hid_rom W x E) in H. simpl in H. discriminate H.
  - split; [reflexivity | exact H].
Qed.

(* A byte the view reads is visible. *)
Lemma mbV_aview : forall (W : lib.Reusable.YA0n.world rsegs) (m : word -> option byte) (x : Z),
  lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m x <> None -> lib.Reusable.YA0n.w_H W (Z_to_bv 64 x) = false.
Proof.
  intros W m x H. destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 x)) eqn:E; [|reflexivity]. exfalso. apply H.
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict. cbv beta. rewrite E.
  rewrite (mbV_hid_rom W x E). reflexivity.
Qed.

Lemma mbV_val_mem : forall (W : lib.Reusable.YA0n.world rsegs) (m : word -> option byte) (a : Z) (n : nat) (v i : Z),
  lib.Reusable.YI04.val_mem rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) m) a n v ->
  0 <= i < Z.of_nat n -> lib.Reusable.YA0n.w_H W (Z_to_bv 64 (a + i)) = false.
Proof.
  intros W m a n v i HV Hi. pose proof (HV (Z.to_nat i) ltac:(lia)) as H.
  rewrite Z2Nat.id in H by lia. exact (proj1 (mbV_mbyte W m _ _ H)).
Qed.

Lemma mbV_garr8 : forall (W : lib.Reusable.YA0n.world rsegs) (m : word -> option byte) (base : Z) (l : list Z) (a : Z),
  lib.Reusable.YI00.garr8 rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) m) base l ->
  base <= a < base + Z.of_nat (length l) -> lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W m base l a HG Ha. destruct (HG (Z.to_nat (a - base)) ltac:(lia)) as [V _].
  pose proof (mbV_val_mem W m _ 1 _ 0 V ltac:(lia)) as X.
  rewrite Z2Nat.id in X by lia. replace (base + (a - base) + 0) with a in X by lia. exact X.
Qed.

(* ---- A value of the restricted memory pins the word that bytes_at reads there -------------------------------- *)

Lemma mbV_nth_le : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma mbV_bytes_le : forall (W : lib.Reusable.YA0n.world rsegs) (m : word -> option byte) (a : Z) (n : nat) (v : Z),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
  lib.Reusable.YI04.val_mem rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) m) a n v ->
  bytes_at rsegs m a (Z_to_le_bytes n v).
Proof.
  intros W m a n v Ha Hb Hv HV. split; [exact Ha|]. rewrite length_Z_to_le_bytes. split; [exact Hb|].
  intros i Hi. rewrite (mbV_nth_le n v i Hi).
  destruct (mbV_mbyte W m _ _ (HV i Hi)) as [_ E]. unfold wa. rewrite E. f_equal.
  unfold lib.Reusable.YO0f.le_byte. rewrite (Z.mod_small v) by lia.
  apply Z_to_bv8_mod. change 256 with (2 ^ 8). apply Z.mod_mod. lia.
Qed.

Lemma mbV_le8_eq : forall (W : lib.Reusable.YA0n.world rsegs) (m : word -> option byte) (a v : Z) (w : word),
  0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  lib.Reusable.YI04.val_mem rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) m) a 8 v ->
  bytes_at rsegs m a (le8 w) -> w = Z_to_bv 64 v.
Proof.
  intros W m a v w Ha Hb Hv HV HB.
  pose proof (mbV_bytes_le W m a 8 v Ha ltac:(cbn; lia) ltac:(cbn; lia) HV) as B0.
  replace (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)) in B0
    by (unfold le8, word_to_le_bytes; rewrite unsigned_lit by lia; reflexivity).
  symmetry. exact (fl_le8_eq [] m m a _ _ B0 HB (fun _ _ => eq_refl) (fun _ _ => I)).
Qed.

Lemma mbV_le4_eq0 : forall (W : lib.Reusable.YA0n.world rsegs) (m : word -> option byte) (a k : Z),
  0 <= a -> a + 4 <= 2 ^ 64 -> 0 <= k < 2 ^ 32 ->
  lib.Reusable.YI04.val_mem rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) m) a 4 0 ->
  bytes_at rsegs m a (le4 (Z_to_bv 64 k)) -> k = 0.
Proof.
  intros W m a k Ha Hb Hk HV HB.
  pose proof (mbV_bytes_le W m a 4 0 Ha ltac:(cbn; lia) ltac:(cbn; lia) HV) as B0.
  replace (Z_to_le_bytes 4 0) with (le4 (Z_to_bv 64 0)) in B0
    by (unfold le4; rewrite unsigned_lit by lia; reflexivity).
  symmetry. exact (fl_le4_eq [] m m a 0 k ltac:(lia) Hk B0 HB (fun _ _ => eq_refl) (fun _ _ => I)).
Qed.

(* ---- Shadow covers ---------------------------------------------------------------------------------------------- *)

(* The 8-aligned shadow word cover of a sub-range of a range whose shadow hull the view reads. *)
Lemma mbV_hull : forall (W : lib.Reusable.YA0n.world rsegs) (m : word -> option byte) (x n x' n' : Z),
  lib.Reusable.YG0d.shadow_hull_vis (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m) x n ->
  0 <= x -> x <= x' -> x' + n' <= x + n -> x + n <= 2 ^ 64 ->
  sh_cover (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) x' n'.
Proof.
  intros W m x n x' n' HS H0 H1 H2 H3. unfold sh_cover. apply B.ProgBridge.rng_of_visible.
  unfold lib.Reusable.YG0d.shadow_hull_vis, lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF in HS.
  rewrite !(Z.add_comm 0x7fff8000) in HS.
  unfold shadow_addr, ASAN_K.
  assert (M : forall u v, u <= v -> (u / 8 + 0x7fff8000) / 8 <= (v / 8 + 0x7fff8000) / 8).
  { intros u v Huv. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. }
  pose proof (M x x' H1) as M1. pose proof (M (x' + n' - 1) (x + n - 1) ltac:(lia)) as M2.
  assert (B1 : 0 <= (x' / 8 + 0x7fff8000) / 8 * 8) by (Z.div_mod_to_equations; lia).
  assert (B2 : ((x' + n' - 1) / 8 + 0x7fff8000) / 8 * 8 + 8 <= 2 ^ 64) by (Z.div_mod_to_equations; lia).
  split; [exact B1|]. split; [lia|].
  intros a Ha. apply (mbV_aview W m). apply HS. lia.
Qed.

(* The cover of [x, x + n) inside a page-aligned zone [lo, hi): its bytes are shadow bytes of the zone. *)
Lemma mbV_al : forall lo hi x n, lo mod 4096 = 0 -> hi mod 4096 = 0 -> 0 <= lo -> lo <= x -> x + n <= hi ->
  hi <= 2 ^ 64 -> 0 < n ->
  0 <= (x / 8 + 0x7fff8000) / 8 * 8 /\ ((x + n - 1) / 8 + 0x7fff8000) / 8 * 8 + 8 <= 2 ^ 64 /\
  forall a, (x / 8 + 0x7fff8000) / 8 * 8 <= a < ((x + n - 1) / 8 + 0x7fff8000) / 8 * 8 + 8 ->
    0 <= a - (0x7fff8000 + lo / 8) /\ a - (0x7fff8000 + lo / 8) < (hi - lo) / 8 /\
    8 * (a - (0x7fff8000 + lo / 8)) < hi - lo.
Proof.
  intros lo hi x n Hlo Hhi H0 H1 H2 H3 H4.
  split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
  intros a Ha. Z.div_mod_to_equations. lia.
Qed.

Lemma mbV_mod4096 : forall F c d, F mod 4096 = 0 -> d = 4096 * c -> (F + d) mod 4096 = 0.
Proof. intros F c d H ->. rewrite Z.mul_comm, Z.mod_add by lia. exact H. Qed.

(* The second-to-last word of the row is rname row: a little-endian value of bytes, so not negative. *)
Lemma mbV_rname_nonneg : forall row, 0 <= rname row.
Proof.
  intros row.
  assert (Hb : forall i, 0 <= rb row i) by (intros i; unfold rb; exact (proj1 (bv_unsigned_in_range _ _))).
  assert (H16 : forall i, 0 <= rw16 row i) by (intros i; unfold rw16; pose proof (Hb i); pose proof (Hb (S i)); lia).
  assert (H32 : forall i, 0 <= rw32 row i)
    by (intros i; unfold rw32; pose proof (H16 i); pose proof (H16 (S (S i))); lia).
  unfold rname, rw64. pose proof (H32 280%nat). pose proof (H32 (4 + 280)%nat). lia.
Qed.

Ltac mbV_row W m V :=
  split; [lia | split; [lia | ]];
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  lazymatch type of V with
  | lib.Reusable.YI04.val_mem _ _ ?base _ _ =>
      replace a with (base + (a - base)) by lia; apply (mbV_val_mem W m _ _ _ _ V); lia
  end.

Section Vis.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
(* Core: B's symbol facts and its const / zero-shadow rows (lib/Reusable/YF0m.v:2985-3009); the top Section of
   pb_reac_box_model_block carries it (plan, "Named hypotheses": CtrlTSyms B). *)
Hypothesis CTS : lib.Reusable.YF0m.CtrlTSyms B.

(* The two JOIN blocks' 8-aligned shadow word covers are visible: JOIN_0013's shadow word is zero shadow of the
   row (0x219e0, 0x60); JOIN_0014's shadow word is four redzone const rows (the owned static (0x21a40, 0x20)) and
   the zero shadow of the row (0x21a60, 0x20). *)
Lemma mbV_join : forall ly S (W : lib.Reusable.YA0n.world rsegs) (m : word -> option byte),
  lib.Reusable.YG0n.ARm B ly S (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m) ->
  sh_cover (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) JOIN_0014 32 /\
  sh_cover (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) JOIN_0013 32.
Proof.
  intros ly S W m M.
  pose proof (lib.Reusable.YG0n.am_zshadow _ _ _ _ M) as ZS.
  unfold lib.Reusable.YG0n.zshadow_ok, lib.Reusable.YG0n.zero_shadow_ranges in ZS.
  rewrite (lib.Reusable.YF0m.ts_zsh _ CTS) in ZS. rewrite Forall_forall in ZS.
  pose proof (ZS (0x21a60, 0x21a80 - 0x21a60)
                ltac:(right; unfold lib.Reusable.YF0m.Tfib_zero_shadow; cbn [In];
                      repeat (first [left; reflexivity | right]))) as Z4.
  pose proof (ZS (0x219e0, 0x21a40 - 0x219e0)
                ltac:(right; unfold lib.Reusable.YF0m.Tfib_zero_shadow; cbn [In];
                      repeat (first [left; reflexivity | right]))) as Z3.
  cbn [fst snd] in Z3, Z4.
  unfold lib.Reusable.YG0v.zero_shadow, lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.SHADOW_OFF in Z3, Z4.
  replace (0x21a60 / 8) with 0x434c in Z4 by reflexivity.
  replace ((0x21a80 - 0x21a60) / 8) with 4 in Z4 by reflexivity.
  replace (0x219e0 / 8) with 0x433c in Z3 by reflexivity.
  replace ((0x21a40 - 0x219e0) / 8) with 12 in Z3 by reflexivity.
  unfold sh_cover, JOIN_0014, JOIN_0013, shadow_addr, ASAN_K. split.
  - change (ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) 0x7fffc348 8).
    apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Z_lt_le_dec a 0x7fffc34c) as [L|L].
    + assert (E : a = 0x7fffc348 \/ a = 0x7fffc349 \/ a = 0x7fffc34a \/ a = 0x7fffc34b) by lia.
      destruct E as [-> | [-> | [-> | ->]]].
      * exact (mbV_val_mem W m 0x7fffc348 1 0xf9 0 (lib.Reusable.YF0x.tfib_const_lookup B CTS ly S
                 (lib.Reusable.YA0n.w_H W) m 0x7fffc348 1 0xf9 M ltac:(vm_compute; reflexivity)) ltac:(lia)).
      * exact (mbV_val_mem W m 0x7fffc349 1 0xf9 0 (lib.Reusable.YF0x.tfib_const_lookup B CTS ly S
                 (lib.Reusable.YA0n.w_H W) m 0x7fffc349 1 0xf9 M ltac:(vm_compute; reflexivity)) ltac:(lia)).
      * exact (mbV_val_mem W m 0x7fffc34a 1 0xf9 0 (lib.Reusable.YF0x.tfib_const_lookup B CTS ly S
                 (lib.Reusable.YA0n.w_H W) m 0x7fffc34a 1 0xf9 M ltac:(vm_compute; reflexivity)) ltac:(lia)).
      * exact (mbV_val_mem W m 0x7fffc34b 1 0xf9 0 (lib.Reusable.YF0x.tfib_const_lookup B CTS ly S
                 (lib.Reusable.YA0n.w_H W) m 0x7fffc34b 1 0xf9 M ltac:(vm_compute; reflexivity)) ltac:(lia)).
    + apply (mbV_aview W m). replace a with (0x7fff8000 + 0x434c + (a - (0x7fff8000 + 0x434c))) by lia.
      rewrite Z4 by lia. discriminate.
  - change (ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) 0x7fffc340 8).
    apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha.
    apply (mbV_aview W m). replace a with (0x7fff8000 + 0x433c + (a - (0x7fff8000 + 0x433c))) by lia.
    rewrite Z3 by lia. discriminate.
Qed.

(* V: the footprint premise of the _F run at RNG_W (w_H W), at a memory m with AR (the caller's journal). *)
Lemma mbB_rngW :
  forall STK sp0 FPj ly0 S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own ly S
         (W : lib.Reusable.YA0n.world rsegs) (m : word -> option byte) md k
         (sp tp : word) (p b o : Z) (row nb : list byte),
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FPj ly0 S0 W0 mem0 md0 own ly S W m md k ->
    B.MemNorm.ro_agree rsegs m ->
    sp0 - STK <= bv_unsigned sp - 4272 -> bv_unsigned sp <= sp0 ->
    bv_unsigned tp = B.AsanRT.RT_TP ->
    (p <> 0 ->
       0 <= p /\ p + 296 <= 2 ^ 64 /\ length row = 296%nat /\
       lib.Reusable.YI00.garr8 rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) m) p
         (map (fun x : byte => bv_unsigned x) row) /\
       lib.Reusable.YG0d.shadow_hull_vis (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m) p 296) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
       rname row + Z.of_nat (length nb) <= 2 ^ 64 /\
       lib.Reusable.YI00.garr8 rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) m) (rname row)
         (map (fun x : byte => bv_unsigned x) nb) /\
       lib.Reusable.YG0d.shadow_hull_vis (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m)
         (rname row) (Z.of_nat (length nb))) ->
    (p <> 0 -> o <> 0 ->
       0 <= o /\ o + 32 <= 2 ^ 64 /\
       (forall a, o <= a < o + 32 -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m a) /\
       lib.Reusable.YG0d.shadow_hull_vis (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m) o 32) ->
    B.Prog.reac_box_model_blockF.mbF_rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W))
      (B.MemNorm.normalize rsegs m) sp tp p b o (lib.Reusable.YG0f.ly_F ly) row nb.
Proof.
  intros STK sp0 FPj ly0 S0 W0 mem0 md0 own ly S W m md k sp tp p b o row nb HJ RO Hlo Hhi HTP HROW HNM HOUT.
  destruct HJ as (HAR & HLE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWIN & HSTK & _ & _).
  pose proof (proj1 HAR) as M.
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ M) as LY.
  destruct HLE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  destruct HSTK as (_ & _ & _ & K4 & K5 & _).
  pose proof (lib.Reusable.YG0f.lo_top _ LY) as (_ & _ & _ & HSH & HALo & HAHi & HSL).
  pose proof (lib.Reusable.YG0f.lo_F_al _ LY) as HFal.
  pose proof (lib.Reusable.YG0f.lo_app _ LY) as LA.
  unfold lib.Reusable.YG0f.owned_extents in LA.
  apply Forall_cons_iff in LA as [_ LA]. apply Forall_cons_iff in LA as [_ LA].
  apply Forall_cons_iff in LA as [IAT LA]. apply Forall_cons_iff in LA as [IAF LA].
  apply Forall_cons_iff in LA as [_ LA]. apply Forall_cons_iff in LA as [_ LA].
  apply Forall_cons_iff in LA as [IAC LA]. apply Forall_cons_iff in LA as [IAD _].
  cbn [fst snd] in IAT, IAF, IAC, IAD.
  pose proof lib.Reusable.YG0f.ASAN_CEIL_range as [CR _].
  unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg,
    lib.Reusable.YG0f.kThreadObjSize, lib.Reusable.YG0f.kFakeStackSize in IAT, IAF, IAC, IAD.
  unfold lib.Reusable.YG0f.kHighMemEnd, lib.Reusable.YG0f.kHighMemBeg, lib.Reusable.YG0f.page_aligned
    in HSH, HALo, HAHi, HSL, HFal.
  (* the image *)
  assert (RIMG : ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) 0x10000 0x5ee000).
  { pose proof (B.ProgBridge.rng_of_visible _ _ _ (B.ProgBridge.img_vis_W W)) as R.
    unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI in R. exact R. }
  assert (VIMG : forall lo len, 0x10000 <= lo -> lo + len <= 0x5fe000 -> 0 <= len ->
             B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) lo len).
  { intros lo len H1 H2 H3.
    apply (B.ProgBridge.range_visible_sub _ _ _ lo len (B.ProgBridge.img_vis_W W));
      unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI; lia. }
  (* the window: the journal's window clause *)
  assert (VWIN : B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) (bv_unsigned sp - 4272) 4272).
  { split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (HWIN a ltac:(lia))). }
  (* the window's shadow cover: am_zshadow's stack row *)
  pose proof (lib.Reusable.YG0n.am_zshadow _ _ _ _ M) as ZS.
  unfold lib.Reusable.YG0n.zshadow_ok, lib.Reusable.YG0n.zero_shadow_ranges in ZS.
  pose proof (Forall_inv ZS) as ZSTK. cbn [fst snd] in ZSTK.
  unfold lib.Reusable.YG0v.zero_shadow, lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.SHADOW_OFF in ZSTK.
  assert (CWIN : sh_cover (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (bv_unsigned sp - 4272) 4272).
  { unfold sh_cover, shadow_addr, ASAN_K. apply B.ProgBridge.rng_of_visible.
    destruct (mbV_al (lib.Reusable.YG0f.ly_stk_lo ly) (lib.Reusable.YG0f.ly_stk_hi ly) (bv_unsigned sp - 4272) 4272
                HALo HAHi ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (P1 & P2 & P3).
    split; [exact P1|]. split; [lia|]. intros a Ha.
    destruct (P3 a ltac:(lia)) as (I1 & I2 & _).
    apply (mbV_aview W m).
    replace a with (0x7fff8000 + lib.Reusable.YG0f.ly_stk_lo ly / 8 +
                    (a - (0x7fff8000 + lib.Reusable.YG0f.ly_stk_lo ly / 8))) by lia.
    rewrite (ZSTK _ (conj I1 I2)). discriminate. }
  (* the side stack and the shadow of its frames: am_areas *)
  pose proof (lib.Reusable.YG0n.am_areas _ _ _ _ M) as AA. rewrite Forall_forall in AA.
  pose proof (AA (lib.Reusable.YG0f.AF 0, lib.Reusable.YG0f.kFakeStackSize)
                ltac:(unfold lib.Reusable.YG0n.aareas; do 3 (apply in_or_app; right); left; reflexivity)) as AF0.
  pose proof (AA (lib.Reusable.YG0f.ASh (lib.Reusable.YG0f.AF lib.Reusable.YG0f.kFakeFramesOff),
                  (lib.Reusable.YG0f.kFakeStackSize - lib.Reusable.YG0f.kFakeFramesOff) / 8)
                ltac:(unfold lib.Reusable.YG0n.aareas; do 3 (apply in_or_app; right); do 5 right; left;
                      reflexivity)) as ASH.
  unfold lib.Reusable.YG0f.range_vis in AF0, ASH. cbn [fst snd lib.Reusable.YG0f.aeval] in AF0, ASH.
  unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, lib.Reusable.YG0f.kFakeFramesOff,
    lib.Reusable.YG0f.kFakeStackSize in AF0, ASH.
  replace (4096 + 32768) with 36864 in ASH by reflexivity.
  replace ((0xb09000 - 36864) / 8) with 1441792 in ASH by reflexivity.
  assert (VFS : forall lo len, lib.Reusable.YG0f.ly_F ly <= lo -> lo + len <= lib.Reusable.YG0f.ly_F ly + 0xb09000 ->
             0 <= len -> B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) lo len).
  { intros lo len H1 H2 H3. split; [lia|]. split; [lia|]. intros a Ha.
    apply (mbV_aview W m). replace a with (lib.Reusable.YG0f.ly_F ly + 0 + (a - lib.Reusable.YG0f.ly_F ly)) by lia.
    apply AF0. lia. }
  pose proof (B.ProgBridge.rng_of_visible _ _ _
                (VFS (lib.Reusable.YG0f.ly_F ly) 36864 ltac:(lia) ltac:(lia) ltac:(lia))) as RHDR.
  pose proof (B.ProgBridge.rng_of_visible _ _ _
                (VFS (lib.Reusable.YG0f.ly_F ly + 36864) 1048576 ltac:(lia) ltac:(lia) ltac:(lia))) as RFR.
  assert (CFS : sh_cover (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (lib.Reusable.YG0f.ly_F ly + 36864) 1048576).
  { unfold sh_cover, shadow_addr, ASAN_K. apply B.ProgBridge.rng_of_visible.
    destruct (mbV_al (lib.Reusable.YG0f.ly_F ly + 36864) (lib.Reusable.YG0f.ly_F ly + 0xb09000)
                (lib.Reusable.YG0f.ly_F ly + 36864) 1048576
                (mbV_mod4096 _ 9 36864 HFal eq_refl) (mbV_mod4096 _ 2825 0xb09000 HFal eq_refl)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (P1 & P2 & P3).
    split; [exact P1|]. split; [lia|]. intros a Ha.
    destruct (P3 a ltac:(lia)) as (I1 & _ & I3).
    apply (mbV_aview W m).
    replace a with (0x7fff8000 + (lib.Reusable.YG0f.ly_F ly + 36864) / 8 +
                    (a - (0x7fff8000 + (lib.Reusable.YG0f.ly_F ly + 36864) / 8))) by lia.
    apply ASH. lia. }
  pose proof (mbV_join ly S W m M) as [J4 J3].
  unfold B.Prog.reac_box_model_blockF.mbF_rng.
  refine (conj RIMG (conj (B.ProgBridge.rng_of_visible _ _ _ VWIN)
    (conj (B.Prog.reac_box_model_blockF.mbF_cov0 _ _ _ CWIN) (conj (B.Prog.reac_box_model_blockF.mbF_span0 _ _ _ CWIN)
    (conj (B.Prog.reac_box_model_blockF.mbF_kov0 _ _ _ CWIN) (conj RHDR (conj RFR
    (conj (B.Prog.reac_box_model_blockF.mbF_cov0 _ _ _ CFS) (conj (B.Prog.reac_box_model_blockF.mbF_span0 _ _ _ CFS)
    (conj (B.Prog.reac_box_model_blockF.mbF_kov0 _ _ _ CFS)
    (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (B.ProgBridge.rng_bytes_RNG_W _))))))))))))))))).
  - (* the thread cells: am_const pins the witnesses and makes each cell visible *)
    intros DT0 TS0 C0 T0 DB0 k0 HT. rewrite HTP in HT |- *.
    pose proof (B.MemNorm.mem_rel_normalize rsegs m RO) as REL.
    assert (TR : forall a bs, bytes_at rsegs (B.MemNorm.normalize rsegs m) a bs -> bytes_at rsegs m a bs)
      by (intros a bs H; exact (proj2 (B.MemNorm.bytes_at_rel rsegs m _ a bs REL) H)).
    destruct HT as (_ & _ & A3 & _ & _ & A6 & A7 & A8 & A9 & A10 & _ & _ & _ & _ & _ & _ & A17 & _ & _).
    apply TR in A3. apply TR in A7. apply TR in A8. apply TR in A9. apply TR in A10. apply TR in A17.
    unfold B.AsanRT.RT_TP in A3, A8, A17 |- *.
    pose proof (lib.Reusable.YF0x.tfib_const_lookup B CTS ly S (lib.Reusable.YA0n.w_H W) m 0x5dc648 8 0x5dc670 M
                  ltac:(vm_compute; reflexivity)) as V1.
    pose proof (lib.Reusable.YF0x.tfib_const_lookup B CTS ly S (lib.Reusable.YA0n.w_H W) m 0xa8f24 4 0 M
                  ltac:(vm_compute; reflexivity)) as V2.
    pose proof (lib.Reusable.YF0x.tfib_const_lookup B CTS ly S (lib.Reusable.YA0n.w_H W) m 0x5dc5f8 8 0x5fd9f8 M
                  ltac:(vm_compute; reflexivity)) as V3.
    pose proof (lib.Reusable.YF0x.tfib_const_lookup_sym B CTS ly S (lib.Reusable.YA0n.w_H W) m
                  (lib.Reusable.YG0f.ATsd 0) 8 (lib.Reusable.YG0f.AC 0) M ltac:(vm_compute; reflexivity)) as V4.
    pose proof (lib.Reusable.YF0x.tfib_const_lookup_sym B CTS ly S (lib.Reusable.YA0n.w_H W) m
                  (lib.Reusable.YG0f.AC 152) 8 (lib.Reusable.YG0f.AT 0) M ltac:(vm_compute; reflexivity)) as V5.
    pose proof (lib.Reusable.YF0x.tfib_const_lookup_sym B CTS ly S (lib.Reusable.YA0n.w_H W) m
                  (lib.Reusable.YG0f.ATp 8) 8 (lib.Reusable.YG0f.AD 0) M ltac:(vm_compute; reflexivity)) as V6.
    pose proof (lib.Reusable.YF0x.tfib_const_lookup_sym B CTS ly S (lib.Reusable.YA0n.w_H W) m
                  (lib.Reusable.YG0f.AT 48) 8 (lib.Reusable.YG0f.ANum 0x5dcd88) M ltac:(vm_compute; reflexivity)) as V7.
    pose proof (lib.Reusable.YF0x.tfib_const_lookup_sym B CTS ly S (lib.Reusable.YA0n.w_H W) m
                  (lib.Reusable.YG0f.AT 56) 8 (lib.Reusable.YG0f.ANum 0x5dce64) M ltac:(vm_compute; reflexivity)) as V8.
    pose proof (lib.Reusable.YF0x.tfib_const_lookup_sym B CTS ly S (lib.Reusable.YA0n.w_H W) m
                  (lib.Reusable.YG0f.AD 24) 8 (lib.Reusable.YG0f.ATp 0) M ltac:(vm_compute; reflexivity)) as V9.
    cbn [lib.Reusable.YG0f.aeval] in V4, V5, V6, V7, V8, V9.
    rewrite (lib.Reusable.YG0n.am_tsd _ _ _ _ M), (lib.Reusable.YF0m.ts_tsd _ CTS) in V4.
    rewrite (lib.Reusable.YF0m.ts_tp _ CTS) in V6, V9.
    unfold lib.Reusable.YF0m.TFIB_TSD in V4. unfold lib.Reusable.YF0m.TFIB_TP in V6, V9.
    rewrite !Z.add_0_r in V4. rewrite !Z.add_0_r in V5. rewrite !Z.add_0_r in V6.
    assert (EDT : DT0 = Z_to_bv 64 0x5dc670)
      by (apply (mbV_le8_eq W m 0x5dc648 _ DT0); [lia | lia | lia | exact V1 | exact A3]).
    assert (Ek : k0 = 0) by (apply (mbV_le4_eq0 W m 0xa8f24 k0); [lia | lia | exact A6 | exact V2 | exact A7]).
    assert (ETS : TS0 = Z_to_bv 64 0x5fd9f8)
      by (apply (mbV_le8_eq W m 0x5dc5f8 _ TS0); [lia | lia | lia | exact V3 | exact A8]).
    subst DT0 k0 TS0. rewrite unsigned_lit in A9 by lia.
    assert (EC : C0 = Z_to_bv 64 (lib.Reusable.YG0f.ly_C ly))
      by (apply (mbV_le8_eq W m 0x5fd9f8 _ C0); [lia | lia | lia | exact V4 | exact A9]).
    subst C0. rewrite unsigned_lit in A10 by lia.
    assert (ET : T0 = Z_to_bv 64 (lib.Reusable.YG0f.ly_T ly))
      by (apply (mbV_le8_eq W m (lib.Reusable.YG0f.ly_C ly + 152) _ T0); [lia | lia | lia | exact V5 | exact A10]).
    assert (EDB : DB0 = Z_to_bv 64 (lib.Reusable.YG0f.ly_D ly))
      by (apply (mbV_le8_eq W m (0x5dc650 + 8) _ DB0); [lia | lia | lia | exact V6 | exact A17]).
    subst T0 DB0.
    unfold B.Prog.RcAsanFP.fp_tls. rewrite !unsigned_lit by lia.
    unfold B.Prog.asan_stack_malloc_c.TLS_INDEX, B.Prog.asan_stack_malloc_c.REAL_TLS_GET_ADDR,
      B.Prog.asan_stack_malloc_c.TSD_KEY_INITED, B.Prog.asan_stack_malloc_c.TSD_KEY, B.Prog.asan_stack_malloc_c.GOT_CF,
      B.Prog.asan_stack_malloc_c.CF, B.Prog.asan_stack_malloc_c.GOT_VERBOSITY, B.Prog.asan_stack_malloc_c.VERBOSITY,
      B.Prog.asan_stack_malloc_c.DTLS_TPOFF.
    repeat (apply Forall_cons; [cbv beta; cbn [fst snd]; apply B.ProgBridge.rng_of_visible | ]).
    all: first
      [ apply Forall_nil
      | apply VIMG; lia
      | mbV_row W m V5
      | mbV_row W m V9
      | split; [lia | split; [lia | ]]; intros a Ha;
        destruct (Z_lt_le_dec a (lib.Reusable.YG0f.ly_T ly + 56));
        [ replace a with (lib.Reusable.YG0f.ly_T ly + 48 + (a - (lib.Reusable.YG0f.ly_T ly + 48))) by lia;
          apply (mbV_val_mem W m _ _ _ _ V7); lia
        | replace a with (lib.Reusable.YG0f.ly_T ly + 56 + (a - (lib.Reusable.YG0f.ly_T ly + 56))) by lia;
          apply (mbV_val_mem W m _ _ _ _ V8); lia ] ].
  - (* the row *)
    intros Hp. destruct (HROW Hp) as (Hp0 & Hpb & Hlen & HG & HSV).
    pose proof (mbV_hull W m p 296 (p + 16) 275 HSV Hp0 ltac:(lia) ltac:(lia) Hpb) as C.
    split; [| split; [exact (B.Prog.reac_box_model_blockF.mbF_cov0 _ _ _ C) |
                      split; [exact (B.Prog.reac_box_model_blockF.mbF_span0 _ _ _ C) |
                              exact (B.Prog.reac_box_model_blockF.mbF_kov0 _ _ _ C)]]].
    apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha.
    apply (mbV_garr8 W m p _ a HG). rewrite length_map, Hlen. lia.
  - (* the output block *)
    intros Hp Ho. destruct (HOUT Hp Ho) as (Ho0 & Hob & HP & HSV).
    pose proof (mbV_hull W m o 32 o 32 HSV Ho0 ltac:(lia) ltac:(lia) Hob) as C.
    split; [| split; [exact (B.Prog.reac_box_model_blockF.mbF_cov0 _ _ _ C) |
                      split; [exact (B.Prog.reac_box_model_blockF.mbF_span0 _ _ _ C) |
                              exact (B.Prog.reac_box_model_blockF.mbF_kov0 _ _ _ C)]]].
    apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha.
    exact (proj1 (HP a Ha)).
  - (* JOIN_0014 *)
    intros _. exact (conj (B.Prog.reac_box_model_blockF.mbF_cov0 _ _ _ J4)
                      (conj (B.Prog.reac_box_model_blockF.mbF_span0 _ _ _ J4)
                            (B.Prog.reac_box_model_blockF.mbF_kov0 _ _ _ J4))).
  - (* JOIN_0013 *)
    intros _. exact (conj (B.Prog.reac_box_model_blockF.mbF_cov0 _ _ _ J3)
                      (conj (B.Prog.reac_box_model_blockF.mbF_span0 _ _ _ J3)
                            (B.Prog.reac_box_model_blockF.mbF_kov0 _ _ _ J3))).
  - (* the name *)
    intros Hp Hb Hh Hr. destruct (HNM Hp Hb Hh Hr) as (Hnb & HG & HSV).
    pose proof (mbV_rname_nonneg row) as Hr0.
    pose proof (mbV_hull W m (rname row) (Z.of_nat (length nb)) (rname row) (Z.of_nat (length nb)) HSV Hr0
                  ltac:(lia) ltac:(lia) Hnb) as C.
    split; [| split; [exact (B.Prog.reac_box_model_blockF.mbF_cov0 _ _ _ C) |
                      split; [exact (B.Prog.reac_box_model_blockF.mbF_span0 _ _ _ C) |
                              exact (B.Prog.reac_box_model_blockF.mbF_kov0 _ _ _ C)]]].
    apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha.
    apply (mbV_garr8 W m _ _ a HG). rewrite length_map. lia.
Qed.

End Vis.

Print Assumptions mbB_rngW.
