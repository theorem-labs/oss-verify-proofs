(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 2004 of its 2120 lines of code are new or changed and 895 lines of the source are left out. *)
(* Segment F30 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): 0x8275c-0x82794, the call of
   reac_ctrl_classify_box_frame (plan-asan section 2 row F30, section 4 CLS). rule 24: no function proved.
   v1.9.0: moved onto a Theorem Labs lane's v1.9 cut bundle (a working branch, 2026-10-28); the commit messages name the
   builds that check it and the FACTS sha of each.
   With s3 = S(fr), s1 = A, s7 = Phi, s2 = len the block runs
     0x8275c-0x82768  sb zero,56(s3) .. sb zero,59(s3)   -- the shadow bytes of fr+448 .. fr+479 become 0
     0x8276c          li a0,4
     0x82770          sb a0,60(s3)                        -- shadow of fr+480: the first 4 of 8 bytes usable
     0x82774          sb a0,66(s3)                        -- shadow of fr+528: the first 4 of 8 bytes usable
     0x82778          ld a4,160(s1)                       -- a4 = [A+160] = fr+528 (v, the event cell)
     0x8277c          li a0,-1
     0x82780          sw a0,0(a4)                         -- [v, v+4) = -1
     0x82784          mv a0,s7                            -- a0 = Phi (f)
     0x82788          mv a1,s2                            -- a1 = len (n)
     0x8278c          ld a2,168(s1)                       -- a2 = [A+168] = fr+2624 (u = our[])
     0x82790          ld a3,208(s1)                       -- a3 = [A+208] = fr+448 (o, the 36-byte result cell)
     0x82794          jal reac_ctrl_classify_box_frame
   The six shadow stores make [fr+448, fr+484) and [fr+528, fr+532) addressable, which is what the callee's
   premises on o and v need. The callee is used through its contract (lib/A/Prog/reac_ctrl_classify_box_frame_c.v),
   run on the normalized memory (F30Call: the contract asks mem_inv, a cut carries ro_agree); its run writes o, v,
   the window [sp-8864, sp), the class-1 side-stack bytes and the window's shadow. FRA moves by f30_fra_run (the
   pattern of a Theorem Labs lane's F36.v), ENT by Tac_slot.ent_munch and ent_mat, FLSI / LK / FLS / LT by F29's *_keep
   transports. The record part of FLS (the 50 bytes at Phi) holds only under 50 <= len, and the contract asks for it
   only then; the short arm (len <= 49) calls the classifier with the same registers.
   Cuts: the entry Inv_A8275c_at (F29's exit) and the exit Inv_A82798_at are SlotInv.v's official bodies. *)
From Stdlib Require Import ZArith List Bool Lia Permutation Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcClassify.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLay reac_ctrl_classify_box_frame_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib
  reac_ctrl_classify_box_frame_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_parse_c bcmp_wrap_c memcmp_c
  asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs F29.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c.
Module MC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.memcmp_c.
Module RP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parse_c.
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.

Module PCB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_classify_box_frame_c.
Module RL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcLay.

(* The callee's stack need (its window is [sp - K30, sp)). *)
Definition K30 : Z := REAC_CTRL_CLASSIFY_BOX_FRAME_K.

(* The classify result cell is the 36 bytes of ctrlparse. *)
Lemma tB_length : forall inp j, length (t_B inp j) = 36%nat.
Proof. intros inp j. apply ctrlparse_length. Qed.
(* ---- addressability from the shadow bytes the segment writes. *)

Lemma b8_rd : forall m a v, b8 m a v -> mrd rsegs m (wa a) = Some (Z_to_bv 8 v).
Proof.
  intros m a v (H0 & H1 & H). specialize (H 0%nat ltac:(cbn; lia)).
  cbn [Z.of_nat nth_error] in H. rewrite Z.add_0_r in H. exact H.
Qed.

(* One 8-byte chunk of the frame, with its single shadow byte: k usable bytes (k = 8 when the byte is 0). *)
Lemma addr_chunk : forall m a k (b : byte), 0 <= a -> a mod 8 = 0 -> 0 <= k <= 8 -> a + k <= APPMEM_END ->
  (forall i, 0 <= i < k -> app_mem (a + i)) ->
  mrd rsegs m (wa (shadow_addr a)) = Some b ->
  (bv_signed b = 0 \/ k <= bv_signed b <= 7) ->
  addressable m a k.
Proof.
  intros m a k b Ha Ha8 Hk Hend Happ Hrd Hok.
  split; [exact Ha|]. split; [lia|]. split; [exact Hend|].
  intros i Hi. split; [exact (Happ i Hi)|]. exists b. split.
  - rewrite (sh_off a i 0 Ha Ha8 ltac:(lia)), Z.add_0_r. exact Hrd.
  - unfold shadow_ok. replace ((a + i) mod 8) with i by (Z.div_mod_to_equations; lia).
    destruct Hok as [H0 | H1]; [left; exact H0 | right; lia].
Qed.

Lemma addr_app : forall m p n1 n2, 0 <= n1 -> 0 <= n2 ->
  addressable m p n1 -> addressable m (p + n1) n2 -> addressable m p (n1 + n2).
Proof.
  intros m p n1 n2 Hn1 Hn2 (H1 & _ & H3 & H4) (G1 & _ & G3 & G4).
  split; [exact H1|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z_lt_ge_dec i n1) as [Hlt|Hge].
  - exact (H4 i ltac:(lia)).
  - replace (p + i) with (p + n1 + (i - n1)) by lia. exact (G4 (i - n1) ltac:(lia)).
Qed.

(* Two disjoint ranges are ordered. *)
Lemma ivl_dj : forall a1 b1 a2 b2, a1 < b1 -> a2 < b2 ->
  (forall x, a1 <= x < b1 -> a2 <= x < b2 -> False) -> b1 <= a2 \/ b2 <= a1.
Proof.
  intros a1 b1 a2 b2 H1 H2 H.
  destruct (Z_le_gt_dec b1 a2) as [Hle|Hgt]; [left; exact Hle|].
  destruct (Z_le_gt_dec b2 a1) as [Hle2|Hgt2]; [right; exact Hle2|].
  exfalso. apply (H (Z.max a1 a2)); lia.
Qed.

Lemma c4_cb : forall m a (v : word), rw_cells rsegs m a [C4 v] -> rw_cells rsegs m a [CB 4 (le4 v)].
Proof.
  intros m a v ((Hwf & Hba) & Hwr). split; [split|].
  - cbn [cells_wf cell_wf]. split; [apply length_le4 | exact I].
  - cbn [cells_bytes cbytes] in *. exact Hba.
  - cbn [cells_size csize Nat.add] in *. exact Hwr.
Qed.

(* The shadow of an application range lies in the shadow region. *)
Lemma sh_hi : forall x y z, HIGHMEM_BEG <= x -> y <= APPMEM_END -> shadow_addr x <= z < shadow_addr y ->
  in_shadow z.
Proof.
  unfold in_shadow, shadow_addr, ASAN_K, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END.
  intros x y z Hx Hy Hz. right. Z.div_mod_to_equations. lia.
Qed.

(* n readable, writable bytes of a stack-like range form a cell. *)
Lemma rw_of_stk : forall m lo hi a n, stk rsegs m lo hi -> lo <= a -> 0 <= n -> a + n <= hi ->
  exists bs, rw_cells rsegs m a [CB (Z.to_nat n) bs].
Proof.
  intros m lo hi a n (Hlo & Hhi & H) Ha Hn Hah.
  destruct (ba_present m (Z.to_nat n) a ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (bs & Hbs & Hlen).
  { intros i Hi. exact (proj2 (H (a + Z.of_nat i) ltac:(lia))). }
  exists bs. split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact Hlen | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hbs.
  - assert (E : Z.of_nat (cells_size [CB (Z.to_nat n) bs]) = n).
    { cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. reflexivity. }
    rewrite E. split; [lia|]. split; [lia|].
    intros i Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

Lemma stk_sub : forall m lo hi lo' hi', stk rsegs m lo hi -> lo <= lo' -> hi' <= hi -> 0 <= lo' -> hi' <= 2 ^ 64 ->
  stk rsegs m lo' hi'.
Proof.
  intros m lo hi lo' hi' (H1 & H2 & H) Hl Hh Hl0 Hh0.
  split; [exact Hl0|]. split; [exact Hh0|]. intros a Ha. exact (H a ltac:(lia)).
Qed.


(* A byte of a carried list, read at its address. *)
Lemma rd_at : forall m a bs i (b : byte), bytes_at rsegs m a bs -> nth_error bs i = Some b ->
  mrd rsegs m (wa (a + Z.of_nat i)) = Some b.
Proof.
  intros m a bs i b (H0 & H1 & H) Hi.
  assert (Hlt : (i < length bs)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  rewrite (H i Hlt). exact Hi.
Qed.

Lemma sh_idx : forall a i, 0 <= a -> a mod 8 = 0 -> 0 <= i -> shadow_addr (a + i) = shadow_addr a + i / 8.
Proof. unfold shadow_addr. intros a i H0 H8 Hi. Z.div_mod_to_equations. lia. Qed.

(* The 36 bytes of the classify result cell, from the five shadow bytes the segment writes. *)
Lemma addr36 : forall m a (b0 b4 : byte), 0 <= a -> a mod 8 = 0 -> a + 36 <= APPMEM_END ->
  (forall i, 0 <= i < 36 -> app_mem (a + i)) ->
  (forall k, 0 <= k < 4 -> mrd rsegs m (wa (shadow_addr a + k)) = Some b0) ->
  mrd rsegs m (wa (shadow_addr a + 4)) = Some b4 ->
  bv_signed b0 = 0 -> bv_signed b4 = 4 -> addressable m a 36.
Proof.
  intros m a b0 b4 Ha Ha8 Hend Happ H0 H4 Sb0 Sb4.
  split; [exact Ha|]. split; [lia|]. split; [exact Hend|].
  intros i Hi. split; [exact (Happ i Hi)|].
  rewrite (sh_idx a i Ha Ha8 ltac:(lia)).
  destruct (Z_lt_ge_dec i 32) as [Hlt|Hge].
  - exists b0. split; [apply H0; Z.div_mod_to_equations; lia | unfold shadow_ok; left; exact Sb0].
  - exists b4. split.
    + replace (i / 8) with 4 by (Z.div_mod_to_equations; lia). exact H4.
    + unfold shadow_ok. right. rewrite Sb4. split; [|lia].
      replace ((a + i) mod 8) with (i - 32) by (Z.div_mod_to_equations; lia). lia.
Qed.

(* mbyte and mrd are the same read. *)
Lemma mb_mrd : forall m a, mbyte rsegs m a = mrd rsegs m (wa a).
Proof. intros m a. reflexivity. Qed.

(* Eight present bytes at a are the little-endian image of a word (the proof of
   lib/A/Prog/reac_box_model_block.v's rd8_le8; that file is not imported here). *)
Lemma rd8_le8 : forall m a, 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> exists b, mrd rsegs m (wa (a + i)) = Some b) ->
  exists w : word, bytes_at rsegs m a (le8 w).
Proof.
  intros m a Ha Hl H.
  destruct (H 0 ltac:(lia)) as [b0 E0]. destruct (H 1 ltac:(lia)) as [b1 E1].
  destruct (H 2 ltac:(lia)) as [b2 E2]. destruct (H 3 ltac:(lia)) as [b3 E3].
  destruct (H 4 ltac:(lia)) as [b4 E4]. destruct (H 5 ltac:(lia)) as [b5 E5].
  destruct (H 6 ltac:(lia)) as [b6 E6]. destruct (H 7 ltac:(lia)) as [b7 E7].
  exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7])).
  assert (EL : le8 (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7])) = [b0; b1; b2; b3; b4; b5; b6; b7]).
  { rewrite <- store_bytes_8. cbn [width_bytes]. rewrite unsigned_lit_wrap.
    rewrite Z_to_le_bytes_mod by (cbn; lia).
    exact (StrFun.Z_to_le_bytes_to_Z [b0; b1; b2; b3; b4; b5; b6; b7]). }
  rewrite EL. split; [lia|]. split; [cbn; lia|].
  intros i Hi. cbn [length] in Hi.
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn [nth_error]; simpl Z.of_nat;
    [rewrite Z.add_0_r in E0; replace (a + Z.of_nat 0) with a by lia; exact E0
    | exact E1 | exact E2 | exact E3 | exact E4 | exact E5 | exact E6 | exact E7 | lia].
Qed.

(* A word_mem witness is the le8 word at its address (its value taken mod 2^64). *)
Lemma wm_le8 : forall m a v, word_mem rsegs m a v -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  bytes_at rsegs m a (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v Hv Ha Hb.
  assert (Hv' : word_mem rsegs m a (v mod 2 ^ 64)).
  { intros k Hk. rewrite (Hv k Hk). f_equal. f_equal. unfold le_byte.
    change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity. }
  pose proof (Z.mod_pos_bound v (2 ^ 64) ltac:(lia)) as Hr.
  pose proof (word_mem_le8 rsegs m a (v mod 2 ^ 64) Hv' Hr Ha Hb) as H8.
  replace (Z_to_bv 64 v) with (Z_to_bv 64 (v mod 2 ^ 64)); [exact H8|].
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* The shadow byte of an address outside an 8-aligned range is outside the range's shadow. *)
Lemma sh_dj_out : forall lo hi y, 0 <= lo -> lo <= hi -> 0 <= y -> lo mod 8 = 0 -> hi mod 8 = 0 ->
  (y < lo \/ hi <= y) -> (shadow_addr y < shadow_addr lo \/ shadow_addr hi <= shadow_addr y).
Proof. unfold shadow_addr. intros lo hi y H1 H2 H3 H4 H5 H6. Z.div_mod_to_equations. lia. Qed.

(* A contiguous app range lies wholly in the low or wholly in the high app memory. *)
Lemma app_split : forall lo hi, lo < hi -> (forall a, lo <= a < hi -> app_mem a) ->
  hi <= LOWMEM_END \/ HIGHMEM_BEG <= lo.
Proof.
  intros lo hi Hlt H. destruct (Z_le_gt_dec hi LOWMEM_END) as [L|L]; [left; exact L|right].
  destruct (Z_le_gt_dec HIGHMEM_BEG lo) as [L2|L2]; [exact L2|exfalso].
  destruct (Z_le_gt_dec lo LOWMEM_END) as [L3|L3].
  - pose proof (H LOWMEM_END ltac:(lia)) as Ha. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
  - pose proof (H lo ltac:(lia)) as Ha. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

(* The shadow bytes of a contiguous app range are in the shadow. *)
Lemma sh_ivl : forall lo hi x, (forall a, lo <= a < hi -> app_mem a) -> lo < hi ->
  shadow_addr lo <= x < shadow_addr hi -> in_shadow x.
Proof.
  intros lo hi x Happ Hlt Hx.
  assert (Hlo : 0 <= lo)
    by (pose proof (Happ lo ltac:(lia)) as H; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia).
  assert (Hhi : hi <= APPMEM_END)
    by (pose proof (Happ (hi - 1) ltac:(lia)) as H; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia).
  unfold in_shadow, shadow_addr in *. destruct (app_split lo hi Hlt Happ) as [HL|HH].
  - left. unfold ASAN_K, LOWMEM_END, LOWSHADOW_END in *. Z.div_mod_to_equations. lia.
  - right. unfold ASAN_K, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *. Z.div_mod_to_equations. lia.
Qed.

(* A range of 1-byte-addressable bytes is addressable. *)
Lemma addr_rng : forall m lo hi, 0 <= lo -> lo <= hi -> hi <= APPMEM_END ->
  (forall a, lo <= a < hi -> addressable m a 1) -> addressable m lo (hi - lo).
Proof.
  intros m lo hi H0 H1 H2 H. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H (lo + i) ltac:(lia)) as (_ & _ & _ & Hb).
  pose proof (Hb 0 ltac:(lia)) as Hb0. rewrite Z.add_0_r in Hb0. exact Hb0.
Qed.

(* A sub-range of an addressable range is addressable. *)
Lemma addr_sub : forall m p n p' n', addressable m p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n ->
  addressable m p' n'.
Proof.
  intros m p n p' n' (H0 & Hn & He & H) H1 H2 H3. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p' + i) with (p + (p' - p + i)) by lia. apply H. lia.
Qed.

(* The class-1 ranges of the side stack in numbers (fs_B 1 = 128, fs_M 1 = 8192). *)
Lemma fsh1 : forall FS, SM.fs_hint FS 1 = FS + 8.
Proof. intros FS. unfold SM.fs_hint. cbn. lia. Qed.
Lemma fsf1 : forall FS, SM.fs_flag FS 1 0 = FS + 20480.
Proof. intros FS. unfold SM.fs_flag. cbn. lia. Qed.
Lemma fsM1 : SM.fs_M 1 = 8192.
Proof. reflexivity. Qed.
Lemma fsfr0 : forall FS, SM.fs_frame FS 1 0 = FS + 1085440.
Proof. intros FS. unfold SM.fs_frame, SM.fs_B. cbn. lia. Qed.
Lemma fsfrM : forall FS, SM.fs_frame FS 1 (SM.fs_M 1) = FS + 2134016.
Proof. intros FS. unfold SM.fs_frame, SM.fs_B, SM.fs_M. cbn. lia. Qed.

Lemma fpw1_eq : forall FS, fp_w [1%nat] FS =
  [(FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016))].
Proof.
  intros FS. unfold fp_w, fp_w1. cbn [flat_map app].
  rewrite fsh1, fsf1, fsfr0, fsfrM, fsM1.
  replace (FS + 8 + 8) with (FS + 16) by lia. replace (FS + 20480 + 8192) with (FS + 28672) by lia.
  reflexivity.
Qed.
(* ---- The run from 0x8275c to the call site: six shadow stores, the event store, four register loads. *)
Lemma f30_stores :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (S3 A fr phi n : Z) (shb junk vb0 : list byte),
    x19 = Z_to_bv 64 S3 -> x9 = Z_to_bv 64 A -> x23 = Z_to_bv 64 phi -> x18 = Z_to_bv 64 n ->
    rw_cells rsegs m (S3 + 56) [CB 11 shb] ->
    rw_cells rsegs m (fr + 448) [CB 36 junk] ->
    rw_cells rsegs m (fr + 528) [CB 4 vb0] ->
    ro_cells rsegs m (A + 160) [C8 (Z_to_bv 64 (fr + 528))] ->
    ro_cells rsegs m (A + 168) [C8 (Z_to_bv 64 (fr + 2624))] ->
    ro_cells rsegs m (A + 208) [C8 (Z_to_bv 64 (fr + 448))] ->
    0 <= S3 -> (S3 + 67 <= fr \/ fr + 3136 <= S3) -> S3 + 392 <= A -> 0 <= fr -> fr + 3136 <= A ->
    A + 416 <= 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => exists m' mid,
         ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 phi) (Z_to_bv 64 n) (Z_to_bv 64 (fr + 2624))
                       (Z_to_bv 64 (fr + 448)) (Z_to_bv 64 (fr + 528)) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
                       x26 x27 x28 x29 x30 x31)
                  Fr (Z_to_bv 64 0x82794) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 56, S3 + 67); (fr + 528, fr + 532)] m m' /\ wmono rsegs m m' /\
         rw_cells rsegs m' (S3 + 56)
           [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 4);
            CB 5 mid; C1 (Z_to_bv 8 4)] /\
         rw_cells rsegs m' (fr + 448) [CB 36 junk] /\
         rw_cells rsegs m' (fr + 528) [CB 4 (le4 (Z_to_bv 64 (-1)))])
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
               x28 x29 x30 x31) Fr (Z_to_bv 64 0x8275c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 Fr fc m S3 A fr phi n shb junk vb0 -> -> -> -> HRWs HRWo HRWv HR160 HR168 HR208
    HS30 HS3fr HS3A Hfr0 HfrA HA64.
  pose proof (munch_refl [(S3 + 56, S3 + 67); (fr + 528, fr + 532)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound rsegs m (S3 + 56) [CB 11 shb] HRWs) as HB1.
  cbn [cells_size csize Nat.add] in HB1.
  pose proof (rw_cells_bound rsegs m (fr + 448) [CB 36 junk] HRWo) as HB2.
  cbn [cells_size csize Nat.add] in HB2.
  (* 0x8275c .. 0x82768: four zero shadow bytes *)
  step. rewrite le1_byte, (unsigned_lit 0) by lia. mem_after_store.
  step. rewrite le1_byte, (unsigned_lit 0) by lia. mem_after_store.
  step. rewrite le1_byte, (unsigned_lit 0) by lia. mem_after_store.
  step. rewrite le1_byte, (unsigned_lit 0) by lia. mem_after_store.
  (* 0x8276c li a0,4 ; 0x82770 sb a0,60(s3) ; 0x82774 sb a0,66(s3) *)
  step.
  step. rewrite le1_byte, (unsigned_lit 4) by lia. mem_after_store.
  step. rewrite le1_byte, (unsigned_lit 4) by lia. mem_after_store.
  (* 0x82778 ld a4,160(s1) ; 0x8277c li a0,-1 ; 0x82780 sw a0,0(a4) *)
  step. step. step.
  match goal with H : rw_cells rsegs ?mm (fr + 528) [C4 ?v] |- _ =>
    replace v with (Z_to_bv 64 (-1)) in H by (apply bv_eq; vm_compute; reflexivity);
    apply c4_cb in H
  end.
  (* 0x82784 mv a0,s7 ; 0x82788 mv a1,s2 ; 0x8278c ld a2,168(s1) ; 0x82790 ld a3,208(s1) *)
  step. step. step. step.
  match goal with |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with
    | Hs : rw_cells rsegs mm (S3 + 56) [_; _; _; _; _; CB 5 ?mid; _] |- _ =>
        apply evt_done; exists mm, mid;
        split; [reflexivity|]; split; [assumption|]; split; [assumption|];
        split; [exact Hs|]; split; assumption
    end
  end.
Qed.

(* ---- Model facts of turn j (a Theorem Labs lane's F36.v, f36_bz_range .. f36_len_nonneg): the frame length is
   nonnegative. *)
Lemma f30_bz_range : forall b : byte, 0 <= RcIdentModel.bz b < 256.
Proof.
  intros b. unfold RcIdentModel.bz. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

Lemma f30_fL_nonneg : forall inp c, 0 <= f_L inp c.
Proof.
  intros inp c. unfold f_L, inb.
  pose proof (f30_bz_range (RcIdentModel.nthb inp (Z.to_nat c))).
  pose proof (f30_bz_range (RcIdentModel.nthb inp (Z.to_nat (c + 1)))).
  destruct (2 <=? f_left inp c); lia.
Qed.

Lemma f30_fc_range : forall inp j, 0 <= fc inp j <= nlen inp.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn [fc]. unfold c0, nlen. lia.
  - change (fc inp (S j)) with (f_next inp (fc inp j)). pose proof (f30_fL_nonneg inp (fc inp j)).
    unfold f_next, f_body, f_len, f_h, f_left in *. lia.
Qed.

Lemma f30_len_nonneg : forall inp j, 0 <= t_len inp j.
Proof.
  intros inp j. pose proof (f30_fc_range inp j) as R. pose proof (f30_fL_nonneg inp (fc inp j)) as Lf.
  unfold t_len. unfold f_len, f_h, f_left in *. lia.
Qed.

(* The image's write-execute separation, by computation (lib/A/BzBridge.v's wx_apart_asan). *)
Lemma f30_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

(* No byte at or above GT = 0x5fe000 is read-only (F29.ro_lo). *)
Lemma f30_ro_false : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. destruct (ro_addr rsegs (wa a)) eqn:E; [|reflexivity].
  pose proof (ro_lo _ E) as Lo. rewrite wa_unsigned in Lo by lia. lia.
Qed.

(* ---- The call 0x82794 (jal reac_ctrl_classify_box_frame) by the callee's contract. The callee asks mem_inv of the
   caller's memory and a cut carries only ro_agree (FRA, push 5b), so the run is made on the normalized memory
   (MemNorm.evt_normalize, SlotInv.v FRA comment) and every premise and post fact moves across mem_rel (the pattern
   of a Theorem Labs lane's F36.v, f36_evt_call / f36_call_norm). The module imports the contract file's own imports, so its
   premises are stated with the contract's names. *)
Module F30Call.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcClassify
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_classify_box_frame_c.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.memcmp_c OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.RcAsanFP
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parse_c.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_classify_box_frame_c.

Lemma f30_stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo ->
  (stk rsegs m lo hi <-> stk rsegs m0 lo hi).
Proof.
  intros m m0 lo hi R Hlo.
  split; intros (H0 & H1 & H); (split; [exact H0|]); (split; [exact H1|]); intros a Ha;
    destruct (H a Ha) as (Hw & b & Hb);
    (assert (E : ro_addr rsegs (wa a) = false) by (apply f30_ro_false; lia)).
  - split; [rewrite (wview_rel_rw rsegs m m0 _ R E); exact Hw|].
    exists b. rewrite <- (mrd_rel rsegs m m0 _ R). exact Hb.
  - split; [rewrite <- (wview_rel_rw rsegs m m0 _ R E); exact Hw|].
    exists b. rewrite (mrd_rel rsegs m m0 _ R). exact Hb.
Qed.

Lemma f30_srw_rel : forall m m0, mem_rel rsegs m m0 -> (shadow_rw m <-> shadow_rw m0).
Proof.
  intros m m0 R. unfold shadow_rw.
  split; intros H a Ha; destruct (H a Ha) as (Hw & b & Hb);
    (assert (E : ro_addr rsegs (wa a) = false)
       by (apply f30_ro_false; unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha;
           lia)).
  - split; [rewrite (wview_rel_rw rsegs m m0 _ R E); exact Hw|].
    exists b. rewrite <- (mrd_rel rsegs m m0 _ R). exact Hb.
  - split; [rewrite <- (wview_rel_rw rsegs m m0 _ R E); exact Hw|].
    exists b. rewrite (mrd_rel rsegs m m0 _ R). exact Hb.
Qed.

Lemma f30_addr_rel : forall m m0 p n, mem_rel rsegs m m0 -> (addressable m p n <-> addressable m0 p n).
Proof.
  intros m m0 p n R.
  assert (MR : forall a, mrd rsegs m a = mrd rsegs m0 a) by (intros a; exact (mrd_rel rsegs m m0 a R)).
  unfold addressable, addr_byte. setoid_rewrite MR. reflexivity.
Qed.

Lemma f30_cells_rel : forall m m0, mem_rel rsegs m m0 -> (asan_cells m <-> asan_cells m0).
Proof.
  intros m m0 R.
  assert (BR : forall a bs, bytes_at rsegs m a bs <-> bytes_at rsegs m0 a bs)
    by (intros a bs; exact (bytes_at_rel rsegs m m0 a bs R)).
  unfold asan_cells. setoid_rewrite BR. reflexivity.
Qed.

Lemma f30_tls_rel : forall m m0 TP DT TS C T DB k, mem_rel rsegs m m0 ->
  (asan_tls_cells m TP DT TS C T DB k <-> asan_tls_cells m0 TP DT TS C T DB k).
Proof.
  intros m m0 TP DT TS C T DB k R.
  assert (BR : forall a bs, bytes_at rsegs m a bs <-> bytes_at rsegs m0 a bs)
    by (intros a bs; exact (bytes_at_rel rsegs m m0 a bs R)).
  unfold asan_tls_cells. setoid_rewrite BR. reflexivity.
Qed.

Lemma f30_fp_rel : forall cs m m0 TP FS lo hi W D, mem_rel rsegs m m0 ->
  (fp cs m TP FS lo hi W D <-> fp cs m0 TP FS lo hi W D).
Proof.
  intros cs m m0 TP FS lo hi W D R.
  assert (BR : forall a bs, bytes_at rsegs m a bs <-> bytes_at rsegs m0 a bs)
    by (intros a bs; exact (bytes_at_rel rsegs m m0 a bs R)).
  assert (CR : forall c, fp_cls m FS c <-> fp_cls m0 FS c)
    by (intros c; unfold fp_cls; setoid_rewrite BR; reflexivity).
  assert (FR : Forall (fp_cls m FS) cs <-> Forall (fp_cls m0 FS) cs)
    by (split; apply Forall_impl; intros c; apply CR).
  assert (PR : fs_place m FS <-> fs_place m0 FS).
  { unfold fs_place. split; intros (H1 & H2 & H3 & H4 & H5);
      (split; [exact H1|]); (split; [exact H2|]); (split; [exact H3|]); (split; [exact H4|]).
    - apply (proj1 (f30_stk_rel m m0 FS (FS + FS_SIZE) R ltac:(unfold ASAN_GT in H3; lia))). exact H5.
    - apply (proj2 (f30_stk_rel m m0 FS (FS + FS_SIZE) R ltac:(unfold ASAN_GT in H3; lia))). exact H5. }
  unfold fp. split; intros (DT & TS & C & T & DB & k & HT & HB1 & HP & HB2 & HB3 & HC & Hrest);
    exists DT, TS, C, T, DB, k.
  - split; [apply (f30_tls_rel m m0 _ _ _ _ _ _ _ R); exact HT|].
    split; [apply BR; exact HB1|]. split; [apply PR; exact HP|].
    split; [apply BR; exact HB2|]. split; [apply BR; exact HB3|].
    split; [apply FR; exact HC | exact Hrest].
  - split; [apply (f30_tls_rel m m0 _ _ _ _ _ _ _ R); exact HT|].
    split; [apply BR; exact HB1|]. split; [apply PR; exact HP|].
    split; [apply BR; exact HB2|]. split; [apply BR; exact HB3|].
    split; [apply FR; exact HC | exact Hrest].
Qed.

Lemma f30_clstls_rel : forall m m0 TP FS lo hi, mem_rel rsegs m m0 ->
  (reac_ctrl_classify_box_frame_tls m TP FS lo hi <-> reac_ctrl_classify_box_frame_tls m0 TP FS lo hi).
Proof.
  intros m m0 TP FS lo hi R. unfold reac_ctrl_classify_box_frame_tls.
  split; intros H DT TS C T DB k HT; apply H; apply (f30_tls_rel m m0 _ _ _ _ _ _ _ R); exact HT.
Qed.

(* A writable cell list at or above GT reads the same in a memory and its normalized image. *)
Lemma f30_rw_rel : forall m m0 a cs, mem_rel rsegs m m0 -> 0x5fe000 <= a ->
  (rw_cells rsegs m a cs <-> rw_cells rsegs m0 a cs).
Proof.
  intros m m0 a cs R Ha. unfold rw_cells, cells_at.
  split; intros ((Hwf & Hb) & Hw); (split; [split; [exact Hwf|] |]).
  - apply (proj1 (bytes_at_rel rsegs m m0 a _ R)). exact Hb.
  - apply (wr_at_norm rsegs m m0 a _ R Hw). intros i Hi.
    destruct Hw as (H0 & H1 & _). apply f30_ro_false. lia.
  - apply (proj2 (bytes_at_rel rsegs m m0 a _ R)). exact Hb.
  - exact (wr_at_rel rsegs m m0 a _ R Hw).
Qed.

Lemma f30_evt_call : reac_ctrl_classify_box_frame_contract ->
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n u o v S FS : Z)
         (fr us junk vb : list byte),
    x10 = Z_to_bv 64 f -> x11 = Z_to_bv 64 n -> x12 = Z_to_bv 64 u -> x13 = Z_to_bv 64 o -> x14 = Z_to_bv 64 v ->
    x2 = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= u < 2^64 -> 0 <= o < 2^64 -> 0 <= v < 2^64 -> S < 2^64 ->
    S mod 16 = 0 ->
    REAC_CTRL_CLASSIFY_BOX_FRAME_K <= S -> stk rsegs m (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    length fr = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fr /\
                (f + 50 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= f)) ->
    o <> 0 -> o mod 4 = 0 -> o + 36 <= 2^64 -> rw_cells rsegs m o [CB 36 junk] ->
    (o + 36 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= o) ->
    (50 <= n -> o + 36 <= f \/ f + 50 <= o) -> (o + 36 <= u \/ u + 6 <= o) ->
    length us = 6%nat ->
    (50 <= n -> u + 6 <= 2^64 /\ bytes_at rsegs m u us /\
                (u + 6 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= u)) ->
    v <> 0 -> v mod 4 = 0 -> v + 4 <= 2^64 -> rw_cells rsegs m v [CB 4 vb] ->
    (v + 4 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= v) ->
    (v + 4 <= o \/ o + 36 <= v) -> (v + 4 <= f \/ f + 50 <= v) -> (v + 4 <= u \/ u + 6 <= v) ->
    mem_inv rsegs m ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K ->
    (50 <= n -> addressable m f 50 /\ addressable m u 6 /\ app_mem (u + 6) /\ app_mem (u + 7)) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m v 4 -> (v + 4 <= RT_LO \/ RT_HI <= v) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S (reac_ctrl_classify_box_frame_W o v S)
      (reac_ctrl_classify_box_frame_D f n u o v) ->
    reac_ctrl_classify_box_frame_tls m (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82798) x2 x3 x4 t0' t1' t2' x8 x9 (Z_to_bv 64 (cl_r (classify n fr us)))
                       a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x82798) fc None m' (seg_rom rsegs) /\
         munch ([(o, o + 36); (v, v + 4); (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K, S)] ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S /\
         rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))] /\
         rw_cells rsegs m' v [CB 4 (reac_ctrl_classify_box_frame_ev (classify n fr us) vb)] /\
         asan_cells m' /\ shadow_rw m' /\
         addressable m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K /\
         fp [1%nat] m' (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S
           (reac_ctrl_classify_box_frame_W o v S) (reac_ctrl_classify_box_frame_D f n u o v) /\
         reac_ctrl_classify_box_frame_tls m' (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
               x28 x29 x30 x31) F (Z_to_bv 64 0x82794) fc None m (seg_rom rsegs)).
Proof.
  intros HC x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m f n u o v S FS fr us junk vb E10 E11 E12 E13 E14 Esp
    Hf Hn Hu Ho Hv HS Hmod HKS HST Hfrl HF50 Ho0 Ho4 Ho36 HRo HoW Hof Hou Husl HU50 Hv0 Hv4 Hv4b HRv HvW
    Hvo Hvf Hvu HMI HAC HSW Hhi Hsp HADW HA50 HADo Hoapp HoCF HADv HvRT HADB HRB HRM HGC HC254 HC255 HFP HTLS.
  step. (* 0x82794 jal reac_ctrl_classify_box_frame, ra = 0x82798 *)
  pose proof HC as HC'. unfold reac_ctrl_classify_box_frame_contract in HC'.
  eapply evt_cut.
  { eapply HC' with (f := f) (n := n) (u := u) (o := o) (v := v) (S := S) (FS := FS) (fr := fr) (us := us)
      (junk := junk) (vb := vb).
    all: first [ assumption | reflexivity ]. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & ST' & HRo' & HRv' & AC' & SW' & AD' & FP' & TL').
  subst ms'.
  lazymatch goal with
  | |- LE.evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done. cbv beta. do 15 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact HRo'|]. split; [exact HRv'|]. split; [exact AC'|]. split; [exact SW'|].
  split; [exact AD'|]. split; [exact FP' | exact TL'].
Qed.

Lemma f30_call_norm : reac_ctrl_classify_box_frame_contract ->
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n u o v S FS : Z)
         (fr us junk vb : list byte),
    x10 = Z_to_bv 64 f -> x11 = Z_to_bv 64 n -> x12 = Z_to_bv 64 u -> x13 = Z_to_bv 64 o -> x14 = Z_to_bv 64 v ->
    x2 = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= u < 2^64 -> 0 <= o < 2^64 -> 0 <= v < 2^64 -> S < 2^64 ->
    S mod 16 = 0 ->
    REAC_CTRL_CLASSIFY_BOX_FRAME_K <= S -> stk rsegs m (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    length fr = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fr /\
                (f + 50 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= f)) ->
    o <> 0 -> o mod 4 = 0 -> o + 36 <= 2^64 -> rw_cells rsegs m o [CB 36 junk] ->
    (o + 36 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= o) ->
    (50 <= n -> o + 36 <= f \/ f + 50 <= o) -> (o + 36 <= u \/ u + 6 <= o) ->
    length us = 6%nat ->
    (50 <= n -> u + 6 <= 2^64 /\ bytes_at rsegs m u us /\
                (u + 6 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= u)) ->
    v <> 0 -> v mod 4 = 0 -> v + 4 <= 2^64 -> rw_cells rsegs m v [CB 4 vb] ->
    (v + 4 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= v) ->
    (v + 4 <= o \/ o + 36 <= v) -> (v + 4 <= f \/ f + 50 <= v) -> (v + 4 <= u \/ u + 6 <= v) ->
    ro_agree rsegs m ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K ->
    (50 <= n -> addressable m f 50 /\ addressable m u 6 /\ app_mem (u + 6) /\ app_mem (u + 7)) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m v 4 -> (v + 4 <= RT_LO \/ RT_HI <= v) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S (reac_ctrl_classify_box_frame_W o v S)
      (reac_ctrl_classify_box_frame_D f n u o v) ->
    reac_ctrl_classify_box_frame_tls m (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    0x5fe000 <= o -> 0x5fe000 <= v ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82798) x2 x3 x4 t0' t1' t2' x8 x9 (Z_to_bv 64 (cl_r (classify n fr us)))
                       a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x82798) fc None m' (seg_rom rsegs) /\
         munch ([(o, o + 36); (v, v + 4); (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K, S)] ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_agree rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S /\
         rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))] /\
         rw_cells rsegs m' v [CB 4 (reac_ctrl_classify_box_frame_ev (classify n fr us) vb)] /\
         asan_cells m' /\ shadow_rw m' /\
         addressable m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K /\
         fp [1%nat] m' (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S
           (reac_ctrl_classify_box_frame_W o v S) (reac_ctrl_classify_box_frame_D f n u o v) /\
         reac_ctrl_classify_box_frame_tls m' (bv_unsigned x4) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
               x28 x29 x30 x31) F (Z_to_bv 64 0x82794) fc None m (seg_rom rsegs)).
Proof.
  intros HC x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m f n u o v S FS fr us junk vb E10 E11 E12 E13 E14 Esp
    Hf Hn Hu Ho Hv HS Hmod HKS HST Hfrl HF50 Ho0 Ho4 Ho36 HRo HoW Hof Hou Husl HU50 Hv0 Hv4 Hv4b HRv HvW
    Hvo Hvf Hvu HRO HAC HSW Hhi Hsp HADW HA50 HADo Hoapp HoCF HADv HvRT HADB HRB HRM HGC HC254 HC255 HFP HTLS
    Hog Hvg.
  pose proof (mem_rel_normalize rsegs m HRO) as R.
  assert (BR : forall a bs, bytes_at rsegs m a bs <-> bytes_at rsegs (normalize rsegs m) a bs)
    by (intros a bs; exact (bytes_at_rel rsegs m (normalize rsegs m) a bs R)).
  assert (Hlo : 0x5fe000 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) by (unfold HIGHMEM_BEG in Hhi; lia).
  eapply LE.evt_mono.
  { eapply (evt_normalize rsegs _ _ F _ fc None m (seg_rom rsegs) f30_wx HRO).
    apply (f30_evt_call HC x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
             x25 x26 x27 x28 x29 x30 x31 F fc (normalize rsegs m) f n u o v S FS fr us junk vb
             E10 E11 E12 E13 E14 Esp Hf Hn Hu Ho Hv HS Hmod HKS).
    - apply (proj1 (f30_stk_rel m _ _ _ R Hlo)). exact HST.
    - exact Hfrl.
    - intros H50. destruct (HF50 H50) as (P1 & P2 & P3 & P4).
      split; [exact P1|]. split; [exact P2|]. split; [apply BR; exact P3 | exact P4].
    - exact Ho0.
    - exact Ho4.
    - exact Ho36.
    - apply (proj1 (f30_rw_rel m _ _ _ R Hog)). exact HRo.
    - exact HoW.
    - exact Hof.
    - exact Hou.
    - exact Husl.
    - intros H50. destruct (HU50 H50) as (P1 & P2 & P3).
      split; [exact P1|]. split; [apply BR; exact P2 | exact P3].
    - exact Hv0.
    - exact Hv4.
    - exact Hv4b.
    - apply (proj1 (f30_rw_rel m _ _ _ R Hvg)). exact HRv.
    - exact HvW.
    - exact Hvo.
    - exact Hvf.
    - exact Hvu.
    - exact (mem_inv_normalize rsegs m).
    - apply (proj1 (f30_cells_rel m _ R)). exact HAC.
    - apply (proj1 (f30_srw_rel m _ R)). exact HSW.
    - exact Hhi.
    - exact Hsp.
    - apply (proj1 (f30_addr_rel m _ _ _ R)). exact HADW.
    - intros H50. destruct (HA50 H50) as (P1 & P2 & P3 & P4).
      split; [apply (proj1 (f30_addr_rel m _ _ _ R)); exact P1|].
      split; [apply (proj1 (f30_addr_rel m _ _ _ R)); exact P2|].
      split; [exact P3 | exact P4].
    - apply (proj1 (f30_addr_rel m _ _ _ R)). exact HADo.
    - exact Hoapp.
    - exact HoCF.
    - apply (proj1 (f30_addr_rel m _ _ _ R)). exact HADv.
    - exact HvRT.
    - apply (proj1 (f30_addr_rel m _ _ _ R)). exact HADB.
    - apply BR. exact HRB.
    - apply BR. exact HRM.
    - apply BR. exact HGC.
    - apply BR. exact HC254.
    - apply BR. exact HC255.
    - apply (proj1 (f30_fp_rel _ m _ _ _ _ _ _ _ R)). exact HFP.
    - apply (proj1 (f30_clstls_rel m _ _ _ _ _ R)). exact HTLS. }
  intros s (s0' & HQ & REL & SAME).
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                  E0 & MU & WM & MI & ST & HRo' & HRv' & AC' & SW' & AD' & FP' & TL').
  subst s0'.
  destruct s as [R' F' pc' sv' rv' fc' m' ro'].
  unfold ms_rel, MS in REL.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in REL, SAME.
  destruct REL as (ER & EF & Epc & Esv & Erv & Efc & Erom & RM).
  subst R' F' pc' sv' rv' fc' ro'.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) m' m0' R RM SAME MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) m' m0' R RM SAME WM)|].
  split; [exact (ro_agree_same rsegs m m' HRO SAME)|].
  split; [apply (proj2 (f30_stk_rel m' m0' _ _ RM Hlo)); exact ST|].
  split; [apply (proj2 (f30_rw_rel m' m0' _ _ RM Hog)); exact HRo'|].
  split; [apply (proj2 (f30_rw_rel m' m0' _ _ RM Hvg)); exact HRv'|].
  split; [apply (proj2 (f30_cells_rel m' m0' RM)); exact AC'|].
  split; [apply (proj2 (f30_srw_rel m' m0' RM)); exact SW'|].
  split; [apply (proj2 (f30_addr_rel m' m0' _ _ RM)); exact AD'|].
  split; [apply (proj2 (f30_fp_rel _ m' m0' _ _ _ _ _ _ RM)); exact FP'|].
  apply (proj2 (f30_clstls_rel m' m0' _ _ _ _ RM)). exact TL'.
Qed.

End F30Call.


Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis CLS : reac_ctrl_classify_box_frame_contract.

Local Notation STKLO mem md := (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
Local Notation OWNED H mem md := (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md).
Local Notation AINFS mem a := (AC.a_in_fs AC.ASYMS mem a).


(* FSREC (the side-arm FakeStack frame record) across a run that writes no app byte below stklo outside the frame
   body [fr + 24, fr + 3136) and the class-1 ranges of the side stack FS: the tp word is in the low image, the
   class-6 flag byte is in FS's header and the slot's last word is above the frame body, all below stklo and off
   the class-1 ranges (Tac_slot.fsrec_munch, with the class-1 writes of the classify call's side-stack frame). *)
Lemma f30_fsrec_keep : forall hb mem mem' md W fr FS,
  FSREC fr mem ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) hb mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  munch W mem mem' ->
  (forall x, app_mem x -> x < STKLO mem md -> ~ (fr + 24 <= x < fr + 3136) -> ~ (FS + 8 <= x < FS + 16) ->
     ~ (FS + 20480 <= x < FS + 28672) -> ~ (FS + 1085440 <= x < FS + 2134016) -> outside W x) ->
  FSREC fr mem'.
Proof.
  intros hb mem mem' md W fr FS (FS0 & j & Htp & HFSr & Hj & Hfr & Hflag & Htail) HAH HwFS HFSr' MU HW.
  assert (E0 : FS0 = FS).
  { pose proof (word_mem_le8 rsegs mem (AC.as_tp AC.ASYMS) FS HwFS HFSr'
                  ltac:(unfold AC.as_tp, AC.ASYMS, RT_TP; cbn; lia)
                  ltac:(unfold AC.as_tp, AC.ASYMS, RT_TP; cbn; lia)) as Hb1.
    pose proof (word_mem_le8 rsegs mem (AC.as_tp AC.ASYMS) FS0 Htp HFSr
                  ltac:(unfold AC.as_tp, AC.ASYMS, RT_TP; cbn; lia)
                  ltac:(unfold AC.as_tp, AC.ASYMS, RT_TP; cbn; lia)) as Hb2.
    pose proof (fl_le8_eq [] mem mem (AC.as_tp AC.ASYMS) (Z_to_bv 64 FS0) (Z_to_bv 64 FS) Hb2 Hb1
                  (munch_refl [] mem) (fun _ _ => I)) as E.
    apply (f_equal (bv_unsigned (n := 64))) in E. rewrite !unsigned_lit in E by lia. exact E. }
  subst FS0.
  destruct (AC.a_laws_fs_place _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
              hb mem md FS HAH Htp HFSr) as (HGTb & HFSlo & _ & Happ).
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HB6 : SM.fs_B 6 = 4096) by reflexivity.
  assert (HM6 : SM.fs_M 6 = 256) by reflexivity.
  assert (Hfl : SM.fs_flag FS 6 j = FS + 36352 + j) by (unfold SM.fs_flag; cbn; lia).
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfr; unfold SM.fs_frame, SM.fs_B; cbn; lia).
  rewrite HM6 in Hj.
  exists FS, j.
  split.
  { intros k Hk.
    assert (Htpv : 0 <= AC.as_tp AC.ASYMS + Z.of_nat k < AC.GT) by (unfold AC.as_tp, AC.ASYMS, AC.GT; cbn; lia).
    assert (Hap : app_mem (AC.as_tp AC.ASYMS + Z.of_nat k)) by (unfold app_mem, LOWMEM_END; rewrite HGTv in Htpv; left; lia).
    assert (Hx : 0 <= AC.as_tp AC.ASYMS + Z.of_nat k < 2 ^ 64) by (rewrite HGTv in Htpv; lia).
    assert (Hm : mem' (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))
                 = mem (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))).
    { apply MU. rewrite unsigned_lit by exact Hx.
      apply HW; [exact Hap | lia ..]. }
    unfold mbyte. rewrite Hm. exact (Htp k Hk). }
  split; [exact HFSr|].
  split; [rewrite HM6; exact Hj|].
  split; [exact Hfr|].
  split.
  { eapply fl_bytes; [exact Hflag | exact MU |].
    cbn [length]. intros x Hx. apply HW; [| lia ..].
    replace x with (SM.fs_flag FS 6 j) by lia. apply Happ. lia. }
  { eapply fl_bytes; [exact Htail | exact MU |].
    rewrite length_le8. intros x Hx. apply HW; [| rewrite HB6 in *; lia ..].
    apply Happ. rewrite HB6 in *. lia. }
Qed.

(* FRA across the callee's run: it writes its own window [sp - 9136, sp), the class-0/1/2 side-stack bytes and the
   shadow of its window.  RT by RT_meta_write (every shadow byte is readable again: the callee's shadow_rw), AH and
   stklo by a_laws_fs_store (the written bytes are the window, the side stack or the shadow of either), and every
   other FRA cell is outside the write set: the low image, the frame body and its 392 shadow bytes (the cut keeps
   the frame apart from the classes 0-2 and the window), the spills at [s1 + 24] / [s1 + 16] / [s1 + 304] (v1.9
   FRA: s5 at [A + 24], fr at [A + 16]) and the saved registers (above sp), and the entry window (still backed
   inside [sp - 9136, sp)). *)
Lemma f30_fra_run : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  STKLO mem' md = STKLO mem md ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = 392%nat) ->
  (forall x, 0 <= x < 6283264 -> outside W x) ->
  (forall x, fr <= x < fr + 24 -> outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 24 <= x < bv_unsigned (getr regs 9) + 32 -> outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 16 <= x < bv_unsigned (getr regs 9) + 24 -> outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 304 <= x < bv_unsigned (getr regs 9) + 312 -> outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> outside W x) ->
  (forall x, g_S g - AF.SLOT_STACK <= x < g_S g -> outside W x \/ exists b, mrd rsegs mem' (wa x) = Some b) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + 3136) -> addressable mem' a 1) ->
  (FSREC fr mem -> FSREC fr mem') ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HAH' HSTK HshR Hshnew HWlo HWhdr HWsel HWfr24
    HWspill HWsaved HWwin HAG' HWA' HREC E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (unfold stk in Hwin; destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A).
  { unfold rg in Hr9. rewrite Hr9. apply MState.unsigned_lit. exact HA64. }
  rewrite HbvA in HWsel, HWspill, HWfr24.
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
    rewrite MState.unsigned_lit by lia. exact (HWlo x ltac:(lia)). }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HshR)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hthr in Hx. cbn in Hx. lia.
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hlock in Hx. cbn in Hx. lia.
    - intros k Hk. rewrite KBlo.
      + exact (Hohd k Hk).
      + rewrite Hhead. lia.
      + rewrite Hhead. lia. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|]. split; [exact Hs5|]. split; [exact HAm|]. split; [exact HAS|]. split; [exact Hspa|].
  split; [exact Hfa|]. split; [exact HA416|]. split; [exact HS4|]. split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWspill x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr24 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWfr24 x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split; [|split].
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
        exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + exact (HREC Hrec). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split; [exact Hshnew|].
  split; [exact (stk_tr W mem mem' _ _ Hwin MU WM HWwin)|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split; [intros a Ha; exact (WM (Z_to_bv 64 a) (Herrno a Ha))|].
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|]. split; [exact HSHI2|]. split; [exact HSHI3|].
  split; [exact Hhb | exact Hlive].
Qed.

(* A heap block lies below the real stack. *)
Lemma fra_blk_lo : forall g fr hb regs mem md p n, FRA B APIf ra g fr hb regs mem md ->
  In (p, n) (hb ++ g_H g) -> p + n <= STKLO mem md.
Proof.
  intros g fr hb regs mem md p n HFRA Hin.
  destruct HFRA as (A & sp & s5 & HRT & HAH & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  exact (proj1 (proj2 (proj2 (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md p n HAH Hin)))).
Qed.

(* The value of the spill at [A + off] with A the register value of s1. *)
Lemma spill_at : forall regs m off v A, rg regs 9 A -> HIGHMEM_BEG <= A -> A + 416 <= 2 ^ 64 -> 0 <= off <= 408 ->
  spill regs m off v -> q64 m (A + off) v.
Proof.
  intros regs m off v A HA HAlo HAhi Hoff (A1 & HA1 & Hq).
  pose proof (rg_mod regs 9 A1 A HA1 HA) as E.
  pose proof Hq as (Hb0 & Hb1 & _). rewrite length_le8 in Hb1. change (Z.of_nat 8) with 8 in Hb1.
  rewrite (Z.mod_small A) in E by (unfold HIGHMEM_BEG in *; lia).
  pose proof (Z.div_mod A1 (2 ^ 64) ltac:(lia)) as D.
  assert (EA : A1 = A).
  { pose proof (Z.mod_pos_bound A1 (2 ^ 64) ltac:(lia)). unfold HIGHMEM_BEG in *. lia. }
  subst A1. exact Hq.
Qed.

(* Two adjacent byte lists read as one. *)
Lemma bytes_at_app : forall m a bs cs, bytes_at rsegs m a bs ->
  bytes_at rsegs m (a + Z.of_nat (length bs)) cs -> bytes_at rsegs m a (bs ++ cs).
Proof.
  intros m a bs cs (Ha & Hb & Hbs) (_ & Hc & Hcs). split; [exact Ha|].
  split; [rewrite length_app; lia|].
  intros i Hi. rewrite length_app in Hi. rewrite nth_error_app.
  destruct (Nat.ltb_spec i (length bs)) as [Hlt|Hge].
  - apply Hbs. lia.
  - replace (a + Z.of_nat i) with (a + Z.of_nat (length bs) + Z.of_nat (i - length bs)) by lia.
    apply Hcs. lia.
Qed.

(* a_laws_thread, read once (a Theorem Labs lane's instruction of 2026-10-28 15:32Z, until Contract.v generation N+1 names its
   inner conjuncts): the TSD main record's word C at RT_TSDMAIN, the AsanThread word T at C + 152, their ranges,
   the eight bytes at C + 152 (owned, app memory) and the sixteen at T + 48 (owned, present).  This is the only
   place F30 reads the law.  It takes each part BY NAME from a Theorem Labs lane's field record fsf_thr_fields
   (Tac_fsfree.v, fsf_thread_fields matches every field to a conjunct by `eassumption`), so no position in the
   law's conjunction is counted here; the statement types every part.  v1.9 (48004cf7bfc) had inserted
   `word_mem (as_tp B - 88) RT_TSDMAIN` and the RT_TSDK bytes at positions 2 and 3, before `exists C T`. *)
Lemma f30_thread : forall H mem md, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  exists C T, word_mem rsegs mem RT_TSDMAIN C /\ 0 < C < 2 ^ 64 /\ 0 < T < 2 ^ 64 /\
    word_mem rsegs mem (C + 152) T /\
    (forall i, 0 <= i < 8 -> OWNED H mem md (C + 152 + i) /\ app_mem (C + 152 + i)) /\
    (forall i, 0 <= i < 16 -> OWNED H mem md (T + 48 + i) /\ exists b, mbyte rsegs mem (T + 48 + i) = Some b).
Proof.
  intros H mem md HAH.
  destruct (fsf_thread_fields (APIf rc) H mem md HAH) as (C & T & HF).
  exists C, T.
  split; [eapply fthr_tsd_word; exact HF|].
  split; [eapply fthr_tsd_range; exact HF|].
  split; [eapply fthr_thr_range; exact HF|].
  split; [eapply fthr_thr_word; exact HF|].
  split; intros i Hi; [eapply fthr_thr_cell | eapply fthr_t48]; eassumption.
Qed.

(* The side stack's thread cells (asan_stack_malloc's asan_tls_cells) read off RT and the heap invariant, with the
   three app-memory ranges (the TSD record word C + 152, the AsanThread's frame-allocation cells T + 48, the DTLS
   link's bytes DB + 24) below the real stack and off the side stack (the allocator owns them, or AH names them). *)
Lemma f30_tls_cells : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  exists DT TS C T DB k,
    SM.asan_tls_cells mem (AC.as_tp AC.ASYMS) DT TS C T DB k /\
    bv_unsigned DT = RT_TP + 32 /\ bv_unsigned TS = RT_TSDMAIN /\ k = 0 /\
    (forall x, (bv_unsigned C + 152 <= x < bv_unsigned C + 160 \/
                bv_unsigned T + 48 <= x < bv_unsigned T + 64 \/
                bv_unsigned DB + 24 <= x < bv_unsigned DB + 32) ->
       app_mem x /\ x < STKLO mem md /\ ~ AINFS mem x).
Proof.
  intros g fr hb regs mem md HFRA.
  pose proof HFRA as (A & sp & s5 & HRT & HAH & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (RT_fs_cells _ _ _ HRT) as (Hfs1 & Hfs2 & Hfs3 & Hfs4 & (FSw & HFSw & HFSok) & _).
  pose proof (RT_uw_cells _ _ _ HRT) as (Huw1 & Huw2 & Huw3 & Huw4 & _).
  pose proof (RT_cf_cells _ _ _ HRT) as (Hcf1 & _ & _ & _ & _ & Hcf6 & _ & _).
  pose proof (RT_opt_cells _ _ _ HRT) as (_ & _ & Hopt3 & Hopt4).
  pose proof (RT_real_cells _ _ _ HRT) as Hreals.
  set (FS := bv_unsigned FSw).
  assert (HwTP : word_mem rsegs mem (AC.as_tp AC.ASYMS) FS).
  { change (AC.as_tp AC.ASYMS) with RT_TP. exact (bytes_at_le8_word rsegs mem RT_TP FSw HFSw). }
  assert (HFSr : 0 <= FS < 2 ^ 64) by (unfold FS; pose proof (bv_unsigned_in_range 64 FSw); change (bv_modulus 64) with (2^64) in *; lia).
  (* thread record (AH9), through f30_thread *)
  destruct (f30_thread (hb ++ g_H g) mem md HAH) as (C0 & T0 & HwC & HCr & HTr & HwT & HCown & HT48).
  (* side stack / DTLS (AH's fs state) *)
  destruct (AC.a_laws_fs_state _ _ _ _ _ LAWS (hb ++ g_H g) mem md FS HAH HwTP HFSr)
    as (_ & (DB0 & HDBr & HwDB & HDBnz & HwDB24 & HDBwin) & HTCapp).
  (* the app-memory ranges are below the stack (owned / AH) and off the side stack *)
  assert (owned_lt : forall a, OWNED (hb ++ g_H g) mem md a -> app_mem a -> a < STKLO mem md).
  { intros a Ho Hap. destruct (Z_lt_ge_dec a (STKLO mem md)) as [H|H]; [exact H|exfalso].
    assert (Hap' : a < APPMEM_END) by (destruct Hap as [Hap|Hap]; unfold LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia).
    destruct (AC.a_laws_not_owned _ _ _ _ _ LAWS (hb ++ g_H g) mem md a HAH
                (or_intror (or_intror (or_intror (conj (Z.ge_le _ _ H) Hap'))))) as (Hno & _).
    exact (Hno Ho). }
  assert (owned_nfs : forall a, OWNED (hb ++ g_H g) mem md a -> ~ AINFS mem a).
  { intros a Ho Hfs.
    destruct (AC.a_laws_not_owned _ _ _ _ _ LAWS (hb ++ g_H g) mem md a HAH
                (or_intror (or_intror (or_introl Hfs)))) as (Hno & _).
    exact (Hno Ho). }
  pose proof (HTCapp C0 T0 HwC ltac:(lia) HwT ltac:(lia)) as HT48app.
  exists (Z_to_bv 64 (RT_TP + 32)), (Z_to_bv 64 RT_TSDMAIN), (Z_to_bv 64 C0),
         (Z_to_bv 64 T0), (Z_to_bv 64 DB0), 0.
  assert (EDT : bv_unsigned (Z_to_bv 64 (RT_TP + 32)) = RT_TP + 32)
    by (rewrite unsigned_lit; [reflexivity | unfold RT_TP; lia]).
  assert (ETS : bv_unsigned (Z_to_bv 64 RT_TSDMAIN) = RT_TSDMAIN)
    by (rewrite unsigned_lit; [reflexivity | unfold RT_TSDMAIN; lia]).
  assert (EC : bv_unsigned (Z_to_bv 64 C0) = C0) by (rewrite unsigned_lit; [reflexivity | lia]).
  assert (ET : bv_unsigned (Z_to_bv 64 T0) = T0) by (rewrite unsigned_lit; [reflexivity | lia]).
  assert (EDB : bv_unsigned (Z_to_bv 64 DB0) = DB0) by (rewrite unsigned_lit; [reflexivity | lia]).
  (* the 16 bytes at T0 + 48 as two words *)
  assert (HT48b : forall i, 0 <= i < 8 -> exists b, mrd rsegs mem (wa (T0 + 48 + i)) = Some b).
  { intros i Hi. destruct (HT48 i ltac:(lia)) as (_ & b & Hb). exists b. rewrite <- mb_mrd. exact Hb. }
  assert (HT56b : forall i, 0 <= i < 8 -> exists b, mrd rsegs mem (wa (T0 + 56 + i)) = Some b).
  { intros i Hi. destruct (HT48 (i + 8) ltac:(lia)) as (_ & b & Hb). exists b.
    replace (T0 + 56 + i) with (T0 + 48 + (i + 8)) by lia. rewrite <- mb_mrd. exact Hb. }
  assert (HTlo : 0 <= T0) by lia.
  assert (HThi : T0 + 48 + 16 <= 2 ^ 64).
  { pose proof (HT48app 15 ltac:(lia)) as Ha. destruct Ha as [Ha|Ha]; unfold LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha; lia. }
  assert (HC152b : C0 + 160 <= 2 ^ 64).
  { destruct (HCown 7 ltac:(lia)) as (_ & Ha). destruct Ha as [Ha|Ha]; unfold LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha; lia. }
  assert (HDB24b : DB0 + 32 <= 2 ^ 64).
  { pose proof (HDBwin (DB0 + 31) ltac:(lia)) as (Ha & _). destruct Ha as [Ha|Ha]; unfold LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha; lia. }
  destruct (rd8_le8 mem (T0 + 48) ltac:(lia) ltac:(lia) HT48b) as (tb & Htb).
  destruct (rd8_le8 mem (T0 + 56) ltac:(lia) ltac:(lia) HT56b) as (te & Hte).
  assert (Htbte : bytes_at rsegs mem (T0 + 48) (le8 tb ++ le8 te)).
  { apply bytes_at_app; [exact Htb|]. rewrite length_le8. replace (T0 + 48 + Z.of_nat 8) with (T0 + 56) by lia. exact Hte. }
  split.
  { unfold SM.asan_tls_cells. change (AC.as_tp AC.ASYMS) with RT_TP.
    split; [exact Hfs1|].
    split; [exact (real_cell_of mem SM.REAL_TLS_GET_ADDR SM.MUSL_TLS_GET_ADDR Hreals ltac:(vm_compute; reflexivity))|].
    split; [exact Hfs3|].
    split; [rewrite EDT; replace (RT_TP + 32 + 8) with (RT_TP + 40) by lia; exact Hfs4|].
    split; [exact Huw1|].
    split; [lia|].
    split; [exact Huw2|].
    split; [exact Huw4|].
    split; [rewrite ETS, Z.mul_0_r, Z.add_0_r; exact (wm_le8 mem RT_TSDMAIN C0 HwC ltac:(unfold RT_TSDMAIN; lia) ltac:(unfold RT_TSDMAIN; lia))|].
    split; [rewrite EC; exact (wm_le8 mem (C0 + 152) T0 HwT ltac:(lia) ltac:(lia))|].
    split; [rewrite ET; exists tb, te; exact Htbte|].
    split; [exact Hcf1|].
    split; [exact Hcf6|].
    split; [exact Hopt3|].
    split; [exact Hopt4|].
    split; [exact Hfs2|].
    split; [change (RT_TP + 8) with (AC.as_tp AC.ASYMS + 8); exact (wm_le8 mem (AC.as_tp AC.ASYMS + 8) DB0 HwDB ltac:(unfold AC.as_tp, AC.ASYMS, RT_TP; cbn; lia) ltac:(unfold AC.as_tp, AC.ASYMS, RT_TP; cbn; lia))|].
    split; [rewrite EDB; exact HDBnz|].
    rewrite EDB.
    exact (wm_le8 mem (DB0 + 24) (AC.as_tp AC.ASYMS) HwDB24 ltac:(lia) ltac:(lia)). }
  split; [exact EDT|]. split; [exact ETS|]. split; [reflexivity|].
  intros x Hx. rewrite EC, ET, EDB in Hx.
  destruct Hx as [Hx|[Hx|Hx]].
  - destruct (HCown (x - (C0 + 152)) ltac:(lia)) as (Ho & Hap).
    assert (Hxe : C0 + 152 + (x - (C0 + 152)) = x) by lia. rewrite Hxe in Ho, Hap.
    split; [exact Hap|]. split; [exact (owned_lt _ Ho Hap) | exact (owned_nfs _ Ho)].
  - destruct (HT48 (x - (T0 + 48)) ltac:(lia)) as (Ho & _).
    pose proof (HT48app (x - (T0 + 48)) ltac:(lia)) as Hap.
    assert (Hxe : T0 + 48 + (x - (T0 + 48)) = x) by lia. rewrite Hxe in Ho, Hap.
    split; [exact Hap|]. split; [exact (owned_lt _ Ho Hap) | exact (owned_nfs _ Ho)].
  - destruct (HDBwin x ltac:(lia)) as (Hap & Hlt & _ & Hnfs & _).
    split; [exact Hap|]. split; [exact Hlt | exact Hnfs].
Qed.

(* fp_dj from a pointwise separation: a property every byte of W has and no byte of X has. *)
Lemma dj_all : forall W X : list ivl,
  (forall w x, In w W -> In x X -> RL.ly_dj (fst w) (snd w) (fst x) (snd x)) -> fp_dj W X.
Proof.
  intros W X H. unfold fp_dj. apply Forall_forall. intros w Hw. apply Forall_forall. intros x Hx.
  exact (H w x Hw Hx).
Qed.

Lemma dj_pt : forall (W X : list ivl) (P : Z -> Prop),
  (forall w, In w W -> fst w < snd w) -> (forall y, In y X -> fst y < snd y) ->
  (forall w x, In w W -> fst w <= x < snd w -> P x) ->
  (forall y x, In y X -> fst y <= x < snd y -> ~ P x) ->
  fp_dj W X.
Proof.
  intros W X P HWp HXp HW HX. apply dj_all. intros w y Hw Hy.
  exact (ivl_dj (fst w) (snd w) (fst y) (snd y) (HWp w Hw) (HXp y Hy)
           (fun x H1 H2 => HX y x Hy H2 (HW w x Hw H1))).
Qed.

(* The class-1 and class-0 side-stack addresses in numbers (the AC. copies of the layout formulas). *)
Lemma afshint1 : forall FS, AC.a_fs_hint FS 1 = FS + 8.
Proof. intros FS. unfold AC.a_fs_hint. cbn. lia. Qed.
Lemma afsflag1 : forall FS j, AC.a_fs_flag FS 1 j = FS + 20480 + j.
Proof. intros FS j. unfold AC.a_fs_flag. cbn. lia. Qed.
Lemma afsM1 : AC.a_fs_M 1 = 8192.
Proof. reflexivity. Qed.
Lemma fsfr00 : forall FS, SM.fs_frame FS 0 0 = FS + 36864.
Proof. intros FS. unfold SM.fs_frame, SM.fs_B. cbn. lia. Qed.

(* The side-stack premises of reac_ctrl_classify_box_frame_contract at the call 0x82794, from FRA alone: RT's
   static TLS cells and the heap invariant's side-stack state give fp's cells; fra_win gives the window, fra_loc
   the frame's place, and FRA's side-arm bound (the frame is a class-6 frame, FS + 6328320 <= fr) puts the frame
   above the class-1 frames of the side stack, which is what keeps the callee's data ranges (the harness buffer f,
   our[] u, the result o, the event cell v) apart from the bytes its own frame request may write.  The harness
   buffer (a data range only when 50 <= len) is a live block, so it lies below the real stack and off the side
   stack. *)
Lemma f30_fp : forall g fr hb phi len regs mem md,
  FRA B APIf ra g fr hb regs mem md ->
  (50 <= len -> In (phi, len) (hb ++ g_H g)) ->
  exists FS,
    word_mem rsegs mem (AC.as_tp AC.ASYMS) FS /\ 0 <= FS < 2 ^ 64 /\
    AC.a_fs_ok mem FS /\ FS + AC.FS_SIZE <= STKLO mem md /\
    (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a) /\
    (forall x, fr <= x < fr + 3136 ->
       AC.GT <= x /\ (STKLO mem md <= x < APPMEM_END \/ FS + 36864 + 6 * 2 ^ 20 <= x < FS + AC.FS_SIZE)) /\
    fp [1%nat] mem (AC.as_tp AC.ASYMS) FS (AC.aspZ regs - K30) (AC.aspZ regs)
      (reac_ctrl_classify_box_frame_W (fr + 448) (fr + 528) (AC.aspZ regs))
      (reac_ctrl_classify_box_frame_D phi len (fr + 2624) (fr + 448) (fr + 528)) /\
    reac_ctrl_classify_box_frame_tls mem (AC.as_tp AC.ASYMS) FS (AC.aspZ regs - K30) (AC.aspZ regs).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb phi len regs mem md HFRA Hin.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (fra_loc B APIf ra g fr hb regs mem md HFRA)
    as (FS & (FSw & HFSw & EFS) & HGTFS & HFSlo & HFSapp & Hhi & Hfr0 & HGTfr & Hfrapp & Hfrloc).
  destruct (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hlow & Hstkwin).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfrA & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hshb & Hwin & Hsaved & Herrno & HAG & HWAd & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  pose proof (bv_unsigned_in_range 64 FSw) as HFSr0. change (bv_modulus 64) with (2 ^ 64) in HFSr0.
  assert (HFSr : 0 <= FS < 2 ^ 64) by lia.
  assert (ETP : AC.as_tp AC.ASYMS = RT_TP) by reflexivity.
  assert (HwTP : word_mem rsegs mem (AC.as_tp AC.ASYMS) FS).
  { rewrite ETP, <- EFS. exact (bytes_at_le8_word rsegs mem RT_TP FSw HFSw). }
  destruct (AC.a_laws_fs_state _ _ _ _ _ LAWS (hb ++ g_H g) mem md FS HAH HwTP HFSr) as (HFSok & _ & _).
  destruct (AC.a_laws_fs_place _ _ _ _ _ LAWS (hb ++ g_H g) mem md FS HAH HwTP HFSr) as (_ & _ & HFSmod & _).
  destruct (f30_tls_cells g fr hb regs mem md HFRA) as (DT & TS & C & T & DB & k & HTLS & EDT & ETS & Ek & Hap3).
  pose proof HFSok as (HFSpres & HFS88 & HFS96 & HFShint & HFSflag).
  unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & Hwv).
  assert (HspE : sp <= APPMEM_END) by (unfold APPMEM_END in *; lia).
  assert (Hasp : AC.aspZ regs = sp) by exact Haspz.
  assert (Hlo1 : STKLO mem md <= sp - K30)
    by (rewrite Hasp in Hlow; unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, FN_STACK, AF.SLOT_STACK in *; lia).
  assert (Happw : forall a, sp - K30 <= a < sp -> app_mem a)
    by (intros a Ha; unfold app_mem; right; unfold HIGHMEM_BEG, APPMEM_END in *; lia).
  assert (Hfsrange : forall x, FS <= x < FS + AC.FS_SIZE -> AINFS mem x)
    by (intros x Hx; exact (a_fs_in AC.ASYMS mem FS x HwTP HFSr Hx)).
  assert (Hphib : 50 <= len -> forall x, phi <= x < phi + 50 -> app_mem x /\ ~ AINFS mem x).
  { intros H50 x Hx.
    destruct (AC.a_laws_blocks _ _ _ _ _ LAWS (hb ++ g_H g) mem md phi len HAH (Hin H50))
      as (_ & _ & _ & _ & Hphiall).
    destruct (Hphiall x ltac:(lia)) as (Hap & _ & _ & _ & Hnfs). split; [exact Hap | exact Hnfs]. }
  assert (Hfrb : forall x, fr <= x < fr + 3136 ->
            AC.GT <= x /\ (STKLO mem md <= x < APPMEM_END \/ FS + 36864 + 6 * 2 ^ 20 <= x < FS + AC.FS_SIZE)).
  { intros x Hx. split; [lia|].
    destruct Hfrloc as [[Hl1 Hl2]|[Hl1 Hl2]]; [left; lia|].
    destruct Hloc as [[_ [_ Hreal]] | [_ [Hfsb _]]].
    - left. exact (Hreal x Hx).
    - right. pose proof (Hfsb FS HwTP HFSr) as Hc. assert (E20 : 2 ^ 20 = 1048576) by reflexivity. lia. }
  assert (HFSsh : forall x, shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016) -> in_shadow x).
  { intros x Hx. apply (sh_ivl (FS + 1085440) (FS + 2134016) x);
      [intros a Ha; apply HFSapp; unfold AC.FS_SIZE; lia | lia | exact Hx]. }
  assert (HWsh : forall x, shadow_addr (sp - K30) <= x < shadow_addr sp -> in_shadow x).
  { intros x Hx. apply (sh_ivl (sp - K30) sp x);
      [exact Happw | unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K; lia | exact Hx]. }
  exists FS.
  split; [exact HwTP|]. split; [exact HFSr|]. split; [exact HFSok|]. split; [exact HFSlo|].
  split; [exact HFSapp|]. split; [exact Hfrb|].
  rewrite Hasp.
  split.
  { unfold fp. exists DT, TS, C, T, DB, k.
    split; [exact HTLS|].
    split; [rewrite ETP, <- EFS, Z_to_bv_bv_unsigned; exact HFSw|].
    split.
    { unfold SM.fs_place. split; [unfold AC.GT in *; lia|].
      split; [exact HFSmod|]. split; [unfold SM.ASAN_GT, AC.GT in *; lia|].
      split; [intros a Ha; apply HFSapp; unfold AC.FS_SIZE, SM.FS_SIZE in *; lia|].
      unfold stk. split; [lia|].
      split; [unfold SM.FS_SIZE, AC.FS_SIZE, APPMEM_END, FN_STACK, AF.SLOT_STACK in *; lia|].
      intros a Ha. destruct (HFSpres a ltac:(unfold AC.FS_SIZE, SM.FS_SIZE in *; lia)) as (Hwr & b & Hb).
      split; [exact Hwr|]. exists b. rewrite <- mb_mrd. exact Hb. }
    split; [exact (wm_le8 mem (FS + 88) 20 HFS88 ltac:(lia) ltac:(unfold AC.FS_SIZE, APPMEM_END in *; lia))|].
    split.
    { split; [lia|]. split; [cbn; unfold AC.FS_SIZE, APPMEM_END in *; lia|].
      intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|cbn in Hi; lia].
      cbn [nth_error]. simpl Z.of_nat. rewrite Z.add_0_r, <- mb_mrd. exact HFS96. }
    split.
    { constructor; [|constructor]. split; [lia|].
      destruct (HFShint 1%nat ltac:(lia)) as (h & Hh). rewrite afshint1 in Hh.
      assert (Hpres : forall i, (i < Z.to_nat 8192)%nat ->
                exists b, mrd rsegs mem (wa (FS + 20480 + Z.of_nat i)) = Some b).
      { intros i Hi. destruct (HFSpres (FS + 20480 + Z.of_nat i) ltac:(unfold AC.FS_SIZE; lia)) as (_ & b & Hb).
        exists b. rewrite <- mb_mrd. exact Hb. }
      destruct (ba_present mem (Z.to_nat 8192) (FS + 20480) ltac:(lia)
                  ltac:(unfold AC.FS_SIZE, APPMEM_END in *; lia) Hpres) as (flags & Hfl & Hfll).
      exists (Z_to_bv 64 h), flags.
      split; [rewrite fsh1; exact (wm_le8 mem (FS + 8) h Hh ltac:(lia) ltac:(unfold AC.FS_SIZE, APPMEM_END in *; lia))|].
      split; [rewrite fsf1; exact Hfl|].
      split; [rewrite fsM1, Hfll; lia|].
      apply Forall_forall. intros b Hb.
      destruct (In_nth_error _ _ Hb) as (i & Hi).
      assert (Hib : (i < Z.to_nat 8192)%nat) by (rewrite <- Hfll; apply nth_error_Some; rewrite Hi; discriminate).
      pose proof Hfl as (_ & _ & Hflb). pose proof (Hflb i ltac:(lia)) as Hre. rewrite Hi in Hre.
      destruct (HFSflag 1%nat (Z.of_nat i) ltac:(lia) ltac:(rewrite afsM1; lia)) as [HH|HH];
        rewrite afsflag1, mb_mrd, Hre in HH; injection HH as <-; [left | right]; reflexivity. }
    split; [unfold SM.FS_SIZE, AC.FS_SIZE in *; lia|].
    split; [exact Happw|].
    split.
    { apply (dj_pt _ _ (fun x => AC.GT <= x /\
              (STKLO mem md <= x < APPMEM_END \/ FS + 36864 + 6 * 2 ^ 20 <= x < FS + AC.FS_SIZE))).
      - intros [wl wh] Hw. unfold reac_ctrl_classify_box_frame_W in Hw. cbn [In] in Hw.
        destruct Hw as [E|[E|[E|[]]]]; injection E as <- <-; cbn [fst snd];
          unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K in *; lia.
      - intros [yl yh] Hy. unfold fp_tls in Hy. rewrite fsfr00 in Hy. cbn [In app] in Hy.
        destruct Hy as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]]]]];
          injection E as <- <-; cbn [fst snd]; lia.
      - intros [wl wh] x Hw Hx. unfold reac_ctrl_classify_box_frame_W in Hw. cbn [In] in Hw.
        cbn [fst snd] in Hx.
        destruct Hw as [E|[E|[E|[]]]]; injection E as <- <-; cbn [fst snd] in Hx.
        + unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K in *.
          split; [unfold AC.GT, HIGHMEM_BEG in *; lia | left; lia].
        + apply Hfrb. lia.
        + apply Hfrb. lia.
      - intros [yl yh] x Hy Hx HP. destruct HP as (HG & Hd).
        unfold fp_tls in Hy. rewrite fsfr00 in Hy. cbn [In app] in Hy. cbn [fst snd] in Hx.
        destruct Hy as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]]]]];
          injection E as <- <-; cbn [fst snd] in Hx; rewrite ?ETP, ?EDT, ?ETS, ?Ek in Hx;
          first
            [ (destruct (Hap3 x ltac:(lia)) as (_ & Hlt3 & Hnfs3);
               destruct Hd as [Hd|Hd];
               [ lia | exact (Hnfs3 (Hfsrange x ltac:(unfold AC.FS_SIZE in *; lia))) ])
            | (destruct Hd as [Hd|Hd]; unfold AC.FS_SIZE in *; lia)
            | (unfold AC.GT, RT_TP, RT_TSDMAIN, SM.TLS_INDEX, SM.REAL_TLS_GET_ADDR, SM.TSD_KEY_INITED,
                 SM.TSD_KEY, SM.GOT_CF, SM.CF, SM.GOT_VERBOSITY, SM.VERBOSITY, SM.DTLS_TPOFF in *; lia) ]. }
    { apply (dj_pt _ _ (fun x => app_mem x /\ ~ (FS <= x < FS + 2134016))).
      - intros [dl dh] Hd. unfold reac_ctrl_classify_box_frame_D in Hd.
        destruct (len <? 50); cbn [In app] in Hd;
          [ destruct Hd as [E|[E|[]]] | destruct Hd as [E|[E|[E|[E|[]]]]] ]; injection E as <- <-; cbn [fst snd];
          lia.
      - intros [yl yh] Hy. rewrite fpw1_eq in Hy. cbn [In] in Hy.
        destruct Hy as [E|[E|[E|[E|[]]]]]; injection E as <- <-; cbn [fst snd]; try lia.
        unfold shadow_addr. Z.div_mod_to_equations. lia.
      - intros [dl dh] x Hd Hx. unfold reac_ctrl_classify_box_frame_D in Hd.
        destruct (len <? 50) eqn:Elen; cbn [In app] in Hd; cbn [fst snd] in Hx.
        + destruct Hd as [E|[E|[]]]; injection E as <- <-; cbn [fst snd] in Hx;
            (split; [apply Hfrapp; lia|];
             destruct (Hfrb x ltac:(lia)) as (_ & [Hc|Hc]); unfold AC.FS_SIZE in *; lia).
        + apply Z.ltb_ge in Elen.
          destruct Hd as [E|[E|[E|[E|[]]]]]; injection E as <- <-; cbn [fst snd] in Hx.
          * destruct (Hphib Elen x ltac:(lia)) as (Hap & Hnfs). split; [exact Hap|].
            intros Hc. exact (Hnfs (Hfsrange x ltac:(unfold AC.FS_SIZE in *; lia))).
          * split; [apply Hfrapp; lia|].
            destruct (Hfrb x ltac:(lia)) as (_ & [Hc|Hc]); unfold AC.FS_SIZE in *; lia.
          * split; [apply Hfrapp; lia|].
            destruct (Hfrb x ltac:(lia)) as (_ & [Hc|Hc]); unfold AC.FS_SIZE in *; lia.
          * split; [apply Hfrapp; lia|].
            destruct (Hfrb x ltac:(lia)) as (_ & [Hc|Hc]); unfold AC.FS_SIZE in *; lia.
      - intros [yl yh] x Hy Hx (Hap & Hnf). rewrite fpw1_eq in Hy. cbn [In] in Hy. cbn [fst snd] in Hx.
        destruct Hy as [E|[E|[E|[E|[]]]]]; injection E as <- <-; cbn [fst snd] in Hx;
          [ lia | lia | lia | exact (app_not_shadow x Hap (HFSsh x Hx)) ]. } }
  (* the tls premise: any thread-cell tuple of mem is this one (fl_tls_same with the empty write set) *)
  intros DT' TS' C' T' DB' k' HTLS'.
  destruct (fl_tls_same mem mem [] (AC.as_tp AC.ASYMS) DT TS C T DB k DT' TS' C' T' DB' k'
              HTLS HTLS' (munch_refl [] mem)
              ltac:(apply Forall_forall; intros d _ x _; exact I)) as (E1 & E2 & E3 & E4 & E5 & E6).
  subst DT' TS' C' T' DB' k'.
  apply (dj_pt _ _ (fun x => x < AC.GT \/ (app_mem x /\ ~ (FS <= x < FS + AC.FS_SIZE)))).
  - intros [yl yh] Hy. unfold fp_tls in Hy. cbn [In] in Hy.
    destruct Hy as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]]]];
      injection E as <- <-; cbn [fst snd]; lia.
  - intros [yl yh] Hy. rewrite fpw1_eq in Hy. cbn [In app] in Hy.
    destruct Hy as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; cbn [fst snd]; try lia;
      unfold shadow_addr; Z.div_mod_to_equations;
      unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K in *; lia.
  - intros [yl yh] x Hy Hx. unfold fp_tls in Hy. cbn [In] in Hy. cbn [fst snd] in Hx.
    destruct Hy as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]]]];
      injection E as <- <-; cbn [fst snd] in Hx; rewrite ?ETP, ?EDT, ?ETS, ?Ek in Hx;
      first
        [ (right; destruct (Hap3 x ltac:(lia)) as (Hap & _ & Hnfs); split;
           [exact Hap | intros Hc; exact (Hnfs (Hfsrange x Hc))])
        | (left; unfold AC.GT, RT_TP, RT_TSDMAIN, SM.TLS_INDEX, SM.REAL_TLS_GET_ADDR, SM.TSD_KEY_INITED,
             SM.TSD_KEY, SM.GOT_CF, SM.CF, SM.GOT_VERBOSITY, SM.VERBOSITY, SM.DTLS_TPOFF in *; lia) ].
  - intros [yl yh] x Hy Hx HP. rewrite fpw1_eq in Hy. cbn [In app] in Hy. cbn [fst snd] in Hx.
    destruct Hy as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; cbn [fst snd] in Hx;
      first
        [ (destruct HP as [HP|(Hap & Hnf)]; unfold AC.GT, AC.FS_SIZE in *; lia)
        | (destruct HP as [HP|(Hap & Hnf)];
           [ pose proof (HFSsh x Hx) as Hs; unfold in_shadow, LOWMEM_END, HIGHSHADOW_BEG, AC.GT in *; lia
           | exact (app_not_shadow x Hap (HFSsh x Hx)) ])
        | (destruct HP as [HP|(Hap & Hnf)];
           [ pose proof (HWsh x Hx) as Hs; unfold in_shadow, LOWMEM_END, HIGHSHADOW_BEG, AC.GT in *; lia
           | exact (app_not_shadow x Hap (HWsh x Hx)) ]) ].
Qed.

(* outside, range by range. *)
Lemma outside_In : forall W x, (forall lo hi, In (lo, hi) W -> ~ (lo <= x < hi)) -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; cbn [outside]; [exact I|].
  split; [apply H; left; reflexivity | apply IH; intros l h Hin; apply H; right; exact Hin].
Qed.

(* The flag byte of a class other than 1 lies in the side stack's header, off the class-1 flag bytes. *)
Lemma afsflag_other : forall FS c j, (c <= 10)%nat -> c <> 1%nat -> 0 <= j < AC.a_fs_M c ->
  FS + 4096 <= AC.a_fs_flag FS c j < FS + 36864 /\ ~ (FS + 20480 <= AC.a_fs_flag FS c j < FS + 28672).
Proof.
  intros FS c j Hc Hne Hj. unfold AC.a_fs_flag. unfold AC.a_fs_M in Hj.
  destruct c as [|[|[|[|[|[|[|[|[|[|[|c]]]]]]]]]]];
    try (exfalso; revert Hc Hne; clear; lia);
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj |- *;
    first [ lia | (vm_compute (2 ^ 15) in *; vm_compute in Hj; lia) ].
Qed.

(* and the hint word of a class other than 1 (its eight bytes) misses the class-1 hint word. *)
Lemma afshint_other : forall FS c, (c <= 10)%nat -> c <> 1%nat ->
  FS <= AC.a_fs_hint FS c /\ AC.a_fs_hint FS c + 8 <= FS + 88 /\
  (AC.a_fs_hint FS c + 8 <= FS + 8 \/ FS + 16 <= AC.a_fs_hint FS c).
Proof.
  intros FS c Hc Hne. unfold AC.a_fs_hint.
  assert (Hz : Z.of_nat c <> 1) by lia. assert (Hz2 : 0 <= Z.of_nat c <= 10) by lia. lia.
Qed.

(* The side stack's state after a run that writes only the class-1 ranges of the side stack (and bytes outside it):
   the class-1 hint word, flag bytes and frames, and the header words, are those of the callee's fp at the return;
   the hint words and flag bytes of the other classes are unchanged. *)
Lemma f30_fs_ok : forall m m' FS Wa TP lo hi Wc Dc,
  AC.a_fs_ok m FS ->
  munch Wa m m' ->
  (forall x, FS <= x < FS + 36864 ->
     ~ (FS + 8 <= x < FS + 16) -> ~ (FS + 20480 <= x < FS + 28672) -> outside Wa x) ->
  fp [1%nat] m' TP FS lo hi Wc Dc ->
  AC.a_fs_ok m' FS.
Proof.
  intros m m' FS Wa TP lo hi Wc Dc (HOK1 & HOK2 & HOK3 & HOK4 & HOK5) MU HOUT
    (DT & TS & C & T & DB & k & _ & _ & HP & H88 & H96 & HCL & _ & _ & _ & _).
  pose proof HP as (HFS0 & HFSmod & HFSgt & HFSapp & HSTK).
  pose proof (Forall_inv HCL) as (_ & h1 & flags & Hh1 & Hfl & Hfll & Hflb).
  assert (HFSb : 0 <= FS /\ FS + AC.FS_SIZE <= 2 ^ 64)
    by (unfold stk in HSTK; unfold SM.FS_SIZE, AC.FS_SIZE in *; lia).
  split.
  { intros a Ha. destruct HSTK as (_ & _ & HS).
    destruct (HS a ltac:(unfold AC.FS_SIZE in Ha; unfold SM.FS_SIZE; lia)) as (Hw & b & Hb).
    split; [exact Hw | exists b; rewrite mb_mrd; exact Hb]. }
  split.
  { pose proof (bytes_at_le8_word rsegs m' (FS + 88) (Z_to_bv 64 20) H88) as HW.
    rewrite unsigned_lit in HW by lia. exact HW. }
  split.
  { pose proof H88 as _. pose proof (rd_at m' (FS + 96) [Z_to_bv 8 0] 0%nat (Z_to_bv 8 0) H96 eq_refl) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r in HH. rewrite mb_mrd. exact HH. }
  split.
  { intros c Hc. destruct (Nat.eq_dec c 1) as [->|Hne].
    + exists (bv_unsigned h1). rewrite afshint1. rewrite fsh1 in Hh1.
      exact (bytes_at_le8_word rsegs m' (FS + 8) h1 Hh1).
    + destruct (HOK4 c Hc) as (h & Hh). exists h.
      apply (word_mem_frame rsegs m m' _ _ Hh). intros kk Hk.
      destruct (afshint_other FS c Hc Hne) as (Hr1 & Hr2 & Hdj).
      unfold mbyte. rewrite MU; [reflexivity|].
      rewrite unsigned_lit by (unfold AC.FS_SIZE in *; lia).
      apply HOUT; [unfold AC.FS_SIZE in *; lia | lia | lia]. }
  { intros c j Hc Hj. destruct (Nat.eq_dec c 1) as [->|Hne].
    + rewrite afsflag1.
      assert (Hjn : (Z.to_nat j < length flags)%nat)
        by (rewrite <- Nat2Z.id; apply Z2Nat.inj_lt; [lia|lia|rewrite Hfll; rewrite fsM1 in *; rewrite afsM1 in Hj; lia]).
      pose proof Hfl as (_ & _ & Hflr). rewrite fsf1 in Hflr.
      pose proof (Hflr (Z.to_nat j) Hjn) as Hre.
      destruct (nth_error flags (Z.to_nat j)) as [b|] eqn:En;
        [|exfalso; apply nth_error_None in En; lia].
      rewrite Z2Nat.id in Hre by lia.
      pose proof (proj1 (Forall_forall _ flags) Hflb b (nth_error_In _ _ En)) as Hb01.
      rewrite mb_mrd. destruct Hb01 as [->| ->]; [left | right]; exact Hre.
    + destruct (afsflag_other FS c j Hc Hne Hj) as (Hr & Hnot).
      destruct (HOK5 c j Hc Hj) as [HH|HH]; [left|right];
        (unfold mbyte in *; rewrite MU; [exact HH|];
         rewrite unsigned_lit by (unfold AC.FS_SIZE in *; lia);
         apply HOUT; [unfold AC.FS_SIZE in *; lia | lia | exact Hnot]). }
Qed.

Lemma seg_F30 : forall j, Hat B APIf ra (Inv_A82798_at B APIf ra) j -> Hat B APIf ra (Inv_A8275c_at B APIf ra) j.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros j Hexit g c HInv.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK & HFLS & HLT).
  subst c. pose proof (proj1 FF) as SEGS.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (fra_loc B APIf ra g fr _ regs mem md HFRA)
    as (FSa & (FSw & HFSw & EFS) & _ & _ & _ & Hhi & Hfr0 & HGTfr & Hfrapp & _).
  destruct (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hlow & Hstkwin).
  destruct (fra_frame B APIf ra g fr _ regs mem md HFRA) as (HfrK & HfrA9 & HFSb & Hfrwr).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfrA & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & (sh & Hsh & Hshl) & Hwin & Hsaved & Herrno & HAG & HWAd &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  (* the turn's registers, record and spills (FLS, FLSI) *)
  pose proof HFLS as (_ & Hs2 & Hs6b & Hs7 & Hs8k & Hs9f & Hrec & Hsp152 & Hsp280).
  pose proof HFLSI as (((Hsp40 & Hsp120 & Hsp136 & Hsp160 & Hsp168 & Hsp176 & Hsp208 & Hsp248p & Haddu & HbyPp &
    HinPp & _ & _ & _ & _) & Hsp128 & Hstkfr & Hsp144 & Hadd17) & Hsp216 & Hsp224 & Hsp248 & (HinP & HpadP & HbyP) &
    _).
  pose proof (f30_len_nonneg (g_in g) j) as Hlen0. change (t_len (g_in g) j) with (flen g j) in Hlen0.
  assert (HinB : 50 <= flen g j -> In (phi, flen g j) (hb1 phi (AC.a_size (flen g j)) ++ g_H g)).
  { intros H50. cbn [In hb1 app]. left. f_equal. unfold AC.a_size. lia. }
  destruct (f30_fp g fr (hb1 phi (AC.a_size (flen g j))) phi (flen g j) regs mem md HFRA HinB)
    as (FS & HwTP & HFSr & HFSok & HFSlo & HFSapp & Hfrb & HFP & HTLS).
  pose proof Hwin as (Hw0 & Hw1 & Hwv).
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  pose proof Haspz as Easp. unfold AC.aspZ in Easp. rewrite Easp in Rsp.
  rewrite Haspz in Hlow, HfrK, Hstkwin, HFP, HTLS.
  (* the frame is apart from the callee's window (fra_frame, K30 <= FN_STACK) *)
  assert (Hfrwin : fr + 3136 <= sp - K30 \/ sp <= fr)
    by (apply HfrK; unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, FN_STACK, AF.SLOT_STACK; lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A).
  { pose proof Hwin as (HwA0 & HwA1 & _).
    unfold rg in Hr9. rewrite Hr9. apply unsigned_lit. lia. }
  pose proof HFP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & (_ & _ & HFSgt0 & _ & _) & _).
  assert (Lsv : length (saved_bytes ra g) = 104%nat)
    by (unfold saved_bytes; rewrite !length_app, !length_le8; reflexivity).
  pose proof Hsaved as (_ & HSv & _). rewrite Lsv in HSv. change (Z.of_nat 104) with 104 in HSv.
  assert (HAhi : HIGHMEM_BEG <= A) by (unfold FN_STACK, AF.SLOT_STACK in *; lia).
  assert (HappE : sp <= APPMEM_END) by (unfold APPMEM_END in *; lia).
  assert (HspK : HIGHMEM_BEG <= sp - K30)
    by (unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, FN_STACK, AF.SLOT_STACK in *; lia).
  assert (HFSw2 : FS + AC.FS_SIZE <= sp - K30)
    by (unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, FN_STACK, AF.SLOT_STACK in *; lia).
  assert (EK30 : K30 = 8864) by reflexivity.
  assert (EKC : REAC_CTRL_CLASSIFY_BOX_FRAME_K = 8864) by reflexivity.
  assert (HFSe : FS + AC.FS_SIZE <= APPMEM_END) by lia.
  (* every value of register 9 is the spill base A up to a multiple of 2 ^ 64 *)
  assert (HAmod : forall A1, rg regs 9 A1 -> exists q, A1 = 2 ^ 64 * q + A).
  { intros A1 HA1. pose proof (rg_mod regs 9 A1 A HA1 Hr9) as E.
    rewrite (Z.mod_small A) in E by (unfold HIGHMEM_BEG, APPMEM_END in *; lia).
    exists (A1 / 2 ^ 64). pose proof (Z.div_mod A1 (2 ^ 64) ltac:(lia)). lia. }
  assert (Hfr8 : fr mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (Hsp8 : sp mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (HFS8 : FS mod 8 = 0).
  { destruct (AC.a_laws_fs_place _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md FS HAH HwTP HFSr)
      as (_ & _ & Hm4 & _). Z.div_mod_to_equations. lia. }
  set (S3 := Sfr fr) in *.
  assert (HSh : forall x, S3 <= x < S3 + 392 ->
    in_shadow x /\ shadow_addr (fr + 8 * (x - S3)) = x /\ fr <= fr + 8 * (x - S3) < fr + 3136).
  { intros x Hx.
    assert (E : shadow_addr (fr + 8 * (x - S3)) = x) by (rewrite sh_frame_of by lia; unfold S3, Sfr; lia).
    split; [rewrite <- E; apply shadow_of_app, Hfrapp; lia | split; [exact E | lia]]. }
  pose proof (in_shadow_bnd _ (proj1 (HSh S3 ltac:(lia)))) as HS3a.
  pose proof (in_shadow_bnd _ (proj1 (HSh (S3 + 391) ltac:(lia)))) as HS3b.
  assert (Hshout : forall y lo hi, 0 <= y -> 0 <= lo -> lo <= hi -> 8 * hi <= 3136 ->
            ~ (fr + 8 * lo <= y < fr + 8 * hi) -> ~ (S3 + lo <= shadow_addr y < S3 + hi)).
  { intros y lo hi Hy0 Hb1 Hb2 Hb3 Hn Hc.
    pose proof (sh_frame fr y (shadow_addr y - S3) Hfr0 Hfr8 Hy0 ltac:(unfold S3, Sfr; lia)) as Hz.
    apply Hn. lia. }
  assert (HFSsh : forall x, shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016) -> in_shadow x).
  { intros x Hx. apply (sh_ivl (FS + 1085440) (FS + 2134016) x);
      [intros a Ha; apply HFSapp; unfold AC.FS_SIZE; lia | lia | exact Hx]. }
  assert (Happw : forall a, sp - K30 <= a < sp -> app_mem a)
    by (intros a Ha; unfold app_mem; right; unfold APPMEM_END in *; lia).
  assert (HWsh : forall x, shadow_addr (sp - K30) <= x < shadow_addr sp -> in_shadow x).
  { intros x Hx. apply (sh_ivl (sp - K30) sp x);
      [exact Happw | unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K; lia | exact Hx]. }
  destruct HHB as (Hphi0 & Hphad).
  assert (Hasz1 : 1 <= AC.a_size (flen g j)) by (unfold AC.a_size; lia).
  assert (Hasz : flen g j <= AC.a_size (flen g j)) by (unfold AC.a_size; lia).
  assert (Hphapp : forall x, phi <= x < phi + AC.a_size (flen g j) -> app_mem x).
  { intros x Hx. exact (addressable_app mem phi (AC.a_size (flen g j)) Hphad x Hx). }
  pose proof Hphad as (Hphp0 & _ & HphE & _).
  assert (Hphfr : forall x, phi <= x < phi + AC.a_size (flen g j) -> fr <= x < fr + 3136 -> False).
  { intros x Hx Hx'. exact (fra_blk B APIf ra g fr _ regs mem md phi (AC.a_size (flen g j)) x HFRA
                             (or_introl eq_refl) Hx Hx'). }
  assert (Hphlo : phi + AC.a_size (flen g j) <= STKLO mem md)
    by exact (fra_blk_lo g fr _ regs mem md phi (AC.a_size (flen g j)) HFRA (or_introl eq_refl)).
  assert (Hphfs : forall x, phi <= x < phi + AC.a_size (flen g j) -> ~ (FS <= x < FS + AC.FS_SIZE)).
  { destruct (AC.a_laws_blocks _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi
                (AC.a_size (flen g j)) HAH ltac:(left; reflexivity)) as (_ & _ & _ & _ & Hall).
    intros x Hx Hc. destruct (Hall x ltac:(lia)) as (_ & _ & _ & _ & Hnfs).
    exact (Hnfs (a_fs_in AC.ASYMS mem FS x HwTP HFSr Hc)). }
  (* the cells the segment writes *)
  pose proof (ba_sub mem S3 sh 56 11 Hsh ltac:(lia)) as Hsh11. change (Z.of_nat 56) with 56 in Hsh11.
  assert (Hwr11 : wr_at rsegs mem (S3 + 56) 11).
  { split; [unfold LOWMEM_END in *; lia|]. split; [unfold HIGHMEM_BEG in *; lia|]. intros i Hi.
    exact (proj1 (RT_shadow_rw _ _ _ HRT (S3 + 56 + i) (proj1 (HSh (S3 + 56 + i) ltac:(lia))))). }
  assert (HRWs : rw_cells rsegs mem (S3 + 56) [CB 11 (firstn 11 (skipn 56 sh))]).
  { split; [split|].
    - cbn [cells_wf cell_wf]. split; [rewrite length_firstn, length_skipn; lia | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hsh11.
    - cbn [cells_size csize Nat.add]. exact Hwr11. }
  destruct (rw_of_stk mem fr (fr + 3136) (fr + 448) 36 Hstkfr ltac:(lia) ltac:(lia) ltac:(lia)) as (junk & HRWo).
  cbn [Z.to_nat] in HRWo.
  destruct (rw_of_stk mem fr (fr + 3136) (fr + 528) 4 Hstkfr ltac:(lia) ltac:(lia) ltac:(lia)) as (vb0 & HRWv).
  cbn [Z.to_nat] in HRWv.
  pose proof (ro_c8 mem (A + 160) (Z_to_bv 64 (fr + 528))
                (spill_at regs mem 160 (fr + 528) A Hr9 HAhi ltac:(lia) ltac:(lia) Hsp160)) as HR160.
  pose proof (ro_c8 mem (A + 168) (Z_to_bv 64 (fr + 2624))
                (spill_at regs mem 168 (fr + 2624) A Hr9 HAhi ltac:(lia) ltac:(lia) Hsp168)) as HR168.
  pose proof (ro_c8 mem (A + 208) (Z_to_bv 64 (fr + 448))
                (spill_at regs mem 208 (fr + 448) A Hr9 HAhi ltac:(lia) ltac:(lia) Hsp208)) as HR208.
  assert (HdjSfr : S3 + 67 <= fr \/ fr + 3136 <= S3).
  { pose proof (Hfrapp fr ltac:(lia)) as H1. pose proof (Hfrapp (fr + 3135) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H1, H2.
    unfold LOWMEM_END, HIGHMEM_BEG in HS3a, HS3b. lia. }
  (* the write set of the whole segment *)
  assert (HWout : forall q, ~ in_shadow q -> ~ (fr + 448 <= q < fr + 484) -> ~ (fr + 528 <= q < fr + 532) ->
            ~ (sp - K30 <= q < sp) -> ~ (FS + 8 <= q < FS + 16) -> ~ (FS + 20480 <= q < FS + 28672) ->
            ~ (FS + 1085440 <= q < FS + 2134016) ->
            outside ([(S3 + 56, S3 + 67); (fr + 528, fr + 532)] ++
                     [(fr + 448, fr + 448 + 36); (fr + 528, fr + 528 + 4); (sp - K30, sp)] ++
                     fp_w [1%nat] FS ++ [(shadow_addr (sp - K30), shadow_addr sp)]) q).
  { intros q Hns H1 H2 H3 H4 H5 H6. apply outside_In. intros lo hi Hin.
    rewrite fpw1_eq in Hin. cbn [In app] in Hin.
    destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]; injection E as <- <-;
      first [ (intros Hc; apply H1; lia) | (intros Hc; apply H2; lia) | (intros Hc; apply H3; lia)
            | (intros Hc; apply H4; lia) | (intros Hc; apply H5; lia) | (intros Hc; apply H6; lia)
            | (intros Hc; apply Hns; exact (proj1 (HSh q ltac:(lia))))
            | (intros Hc; apply Hns; exact (HFSsh q Hc))
            | (intros Hc; apply Hns; exact (HWsh q Hc)) ]. }
  assert (HWsh2 : forall q, in_shadow q -> ~ (S3 + 56 <= q < S3 + 67) ->
            ~ (shadow_addr (FS + 1085440) <= q < shadow_addr (FS + 2134016)) ->
            ~ (shadow_addr (sp - K30) <= q < shadow_addr sp) ->
            outside ([(S3 + 56, S3 + 67); (fr + 528, fr + 532)] ++
                     [(fr + 448, fr + 448 + 36); (fr + 528, fr + 528 + 4); (sp - K30, sp)] ++
                     fp_w [1%nat] FS ++ [(shadow_addr (sp - K30), shadow_addr sp)]) q).
  { intros q Hs H1 H2 H3. apply outside_In. intros lo hi Hin.
    rewrite fpw1_eq in Hin. cbn [In app] in Hin.
    destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]; injection E as <- <-;
      first [ exact H1 | exact H2 | exact H3
            | (intros Hc; exact (app_not_shadow q (Hfrapp q ltac:(lia)) Hs))
            | (intros Hc; exact (app_not_shadow q (Happw q ltac:(lia)) Hs))
            | (intros Hc; exact (app_not_shadow q (HFSapp q ltac:(unfold AC.FS_SIZE; lia)) Hs)) ]. }
  assert (HWrange : forall q, (q < 0 \/ 2 ^ 64 <= q) ->
            outside ([(S3 + 56, S3 + 67); (fr + 528, fr + 532)] ++
                     [(fr + 448, fr + 448 + 36); (fr + 528, fr + 528 + 4); (sp - K30, sp)] ++
                     fp_w [1%nat] FS ++ [(shadow_addr (sp - K30), shadow_addr sp)]) q).
  { intros q Hq. apply outside_In. intros lo hi Hin.
    rewrite fpw1_eq in Hin. cbn [In app] in Hin.
    pose proof (in_shadow_bnd _ (HFSsh (shadow_addr (FS + 1085440))
                  ltac:(unfold shadow_addr; Z.div_mod_to_equations; lia))) as Hb1.
    pose proof (in_shadow_bnd _ (HFSsh (shadow_addr (FS + 2134016) - 1)
                  ltac:(unfold shadow_addr; Z.div_mod_to_equations; lia))) as Hb2.
    pose proof (in_shadow_bnd _ (HWsh (shadow_addr (sp - K30))
                  ltac:(unfold shadow_addr, K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K;
                        Z.div_mod_to_equations; lia))) as Hb3.
    pose proof (in_shadow_bnd _ (HWsh (shadow_addr sp - 1)
                  ltac:(unfold shadow_addr, K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K;
                        Z.div_mod_to_equations; lia))) as Hb4.
    destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]; injection E as <- <-;
      unfold LOWMEM_END, HIGHMEM_BEG, APPMEM_END, AC.FS_SIZE, AC.GT,
        K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K in *; lia. }
  rewrite SEGS.
  apply (sl_run_lib regs (Z_to_bv 64 0x8275c) mem md
    (fun R0 pc' mem3 => pc' = Z_to_bv 64 0x82798 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 21 = getr regs 21 /\ getr R0 22 = getr regs 22 /\
       getr R0 23 = getr regs 23 /\ getr R0 24 = getr regs 24 /\ getr R0 25 = getr regs 25 /\
       getr R0 26 = getr regs 26 /\ getr R0 10 = Z_to_bv 64 (cl_r (t_cls (g_in g) j)) /\
       munch ([(S3 + 56, S3 + 67); (fr + 528, fr + 532)] ++
              [(fr + 448, fr + 448 + 36); (fr + 528, fr + 528 + 4); (sp - K30, sp)] ++
              fp_w [1%nat] FS ++ [(shadow_addr (sp - K30), shadow_addr sp)]) mem mem3 /\
       wmono rsegs mem mem3 /\ ro_agree rsegs mem3 /\ shadow_rw mem3 /\
       stk rsegs mem3 (sp - K30) sp /\ AC.a_fs_ok mem3 FS /\
       rw_cells rsegs mem3 (fr + 448) [CB 36 (t_B (g_in g) j)] /\
       (exists vb3, rw_cells rsegs mem3 (fr + 528) [CB 4 vb3]) /\
       (forall e, t_cls (g_in g) j = Some e -> u32 mem3 (fr + 528) e) /\
       addressable mem3 (fr + 448) 36 /\ addressable mem3 (fr + 528) 4 /\
       addressable mem3 (fr + 2624) 6 /\ addressable mem3 (sp - K30) K30)
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* the six shadow stores, the event store, the four argument loads, then the call *)
    eapply evt_cut.
    { unfold Regs6ss.mkR_of.
      eapply f30_stores with (m := mem) (S3 := S3) (A := A) (fr := fr) (phi := phi) (n := flen g j)
        (shb := firstn 11 (skipn 56 sh)) (junk := junk) (vb0 := vb0);
      [ unfold rg in Hr19; exact Hr19 | unfold rg in Hr9; exact Hr9 | unfold rg in Hs7; exact Hs7
      | unfold rg in Hs2; exact Hs2 | exact HRWs | exact HRWo | exact HRWv | exact HR160 | exact HR168
      | exact HR208 | unfold LOWMEM_END in *; lia | exact HdjSfr
      | unfold HIGHMEM_BEG in *; lia | lia | exact HfrA | lia ]. }
    intros ms' (m2 & mid & Ems & MU1 & WM1 & Hsh2 & Ho2 & Hv2). subst ms'.
    destruct Hsh2 as ((Hwf2 & Hba2) & Hwr2).
    assert (Hmid : length mid = 5%nat) by (cbn [cells_wf cell_wf] in Hwf2; tauto).
    cbn [cells_bytes cbytes app] in Hba2.
    assert (R0 : mrd rsegs m2 (wa (S3 + 56)) = Some (Z_to_bv 8 0))
      by (replace (S3 + 56) with (S3 + 56 + Z.of_nat 0) by lia; apply (rd_at m2 _ _ 0%nat _ Hba2); reflexivity).
    assert (R1 : mrd rsegs m2 (wa (S3 + 57)) = Some (Z_to_bv 8 0))
      by (replace (S3 + 57) with (S3 + 56 + Z.of_nat 1) by lia; apply (rd_at m2 _ _ 1%nat _ Hba2); reflexivity).
    assert (R2 : mrd rsegs m2 (wa (S3 + 58)) = Some (Z_to_bv 8 0))
      by (replace (S3 + 58) with (S3 + 56 + Z.of_nat 2) by lia; apply (rd_at m2 _ _ 2%nat _ Hba2); reflexivity).
    assert (R3 : mrd rsegs m2 (wa (S3 + 59)) = Some (Z_to_bv 8 0))
      by (replace (S3 + 59) with (S3 + 56 + Z.of_nat 3) by lia; apply (rd_at m2 _ _ 3%nat _ Hba2); reflexivity).
    assert (R4 : mrd rsegs m2 (wa (S3 + 60)) = Some (Z_to_bv 8 4))
      by (replace (S3 + 60) with (S3 + 56 + Z.of_nat 4) by lia; apply (rd_at m2 _ _ 4%nat _ Hba2); reflexivity).
    assert (R10 : mrd rsegs m2 (wa (S3 + 66)) = Some (Z_to_bv 8 4)).
    { replace (S3 + 66) with (S3 + 56 + Z.of_nat 10) by lia. apply (rd_at m2 _ _ 10%nat _ Hba2).
      destruct mid as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 mid']]]]]]; cbn in Hmid; try discriminate.
      reflexivity. }
    assert (HW1app : forall x, app_mem x -> ~ (fr + 528 <= x < fr + 532) ->
              outside [(S3 + 56, S3 + 67); (fr + 528, fr + 532)] x).
    { intros x Hx Hv. apply outside_In. intros lo hi Hin. cbn [In] in Hin.
      destruct Hin as [E|[E|[]]]; injection E as <- <-;
        [intros Hc; exact (app_not_shadow x Hx (proj1 (HSh x ltac:(lia)))) | exact Hv]. }
    assert (HnotW1 : forall y, app_mem y -> ~ (fr + 448 <= y < fr + 536) ->
              outside [(S3 + 56, S3 + 67); (fr + 528, fr + 532)] (shadow_addr y)).
    { intros y Hy Hn.
      assert (Hy0 : 0 <= y) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hy; lia).
      apply outside_In. intros lo hi Hin. cbn [In] in Hin.
      destruct Hin as [E|[E|[]]]; injection E as <- <-.
      - exact (Hshout y 56 67 Hy0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      - intros Hc.
        exact (app_not_shadow (shadow_addr y) (Hfrapp (shadow_addr y) ltac:(lia)) (shadow_of_app y Hy)). }
    assert (HpresM : forall x, 0 <= x < 2 ^ 64 -> (exists b, mrd rsegs mem (wa x) = Some b) ->
              exists b, mrd rsegs m2 (wa x) = Some b).
    { intros x Hx Hp.
      assert (Hcase : (S3 + 56 <= x < S3 + 67) \/ (fr + 528 <= x < fr + 532) \/
                      (~ (S3 + 56 <= x < S3 + 67) /\ ~ (fr + 528 <= x < fr + 532))) by lia.
      destruct Hcase as [Hc|[Hc|(Hn1 & Hn2)]].
      - replace x with (S3 + 56 + (x - (S3 + 56))) by lia.
        apply (ba_some m2 (S3 + 56) _ _ Hba2).
        cbn [length]. rewrite length_app. cbn [length]. lia.
      - destruct Hv2 as ((_ & Hbv) & _). cbn [cells_bytes cbytes app] in Hbv.
        rewrite app_nil_r in Hbv.
        replace x with (fr + 528 + (x - (fr + 528))) by lia.
        apply (ba_some m2 (fr + 528) _ _ Hbv). rewrite length_le4. cbn [Z.of_nat]. lia.
      - unfold mrd in *. rewrite MU1; [exact Hp|]. rewrite wa_unsigned by lia.
        apply outside_In. intros lo hi Hin. cbn [In] in Hin.
        destruct Hin as [E|[E|[]]]; injection E as <- <-; assumption. }
    assert (Hshp2 : forall a, in_shadow a -> exists b, mrd rsegs m2 (wa a) = Some b).
    { intros a Ha. pose proof (in_shadow_bnd a Ha) as Hb.
      apply HpresM; [unfold LOWMEM_END, HIGHMEM_BEG in *; lia|].
      exact (proj2 (RT_shadow_rw _ _ _ HRT a Ha)). }
    assert (Hrtdj1 : rt_disjoint [(S3 + 56, S3 + 67); (fr + 528, fr + 532)]).
    { unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
        RT_AGLOB, RT_AGLOB_LEN.
      unfold LOWMEM_END in HS3a. unfold AC.GT in HGTfr. cbn [disjoint_from].
      repeat split; first [left; lia | right; lia | exact I]. }
    assert (RT2 : AsanRTInv.RT sp m2 md)
      by exact (RT_meta_write sp sp mem m2 md md _ HRT MU1 WM1 Hrtdj1 Hshp2).
    assert (Hmeta1 : forall q, fs_meta FS q -> outside [(S3 + 56, S3 + 67); (fr + 528, fr + 532)] q).
    { intros q Hq. pose proof (fs_meta_below FS q Hq) as Hbq. pose proof (fs_meta_ge FS q Hq) as Hgq.
      apply HW1app.
      - apply HFSapp. unfold AC.FS_SIZE. lia.
      - destruct (Hfrb (fr + 528) ltac:(lia)) as (_ & [Hc|Hc]); unfold AC.FS_SIZE in *; lia. }
    assert (Hagree1 : forall q, 0 <= q < 2 ^ 64 ->
      ~ AC.a_store_ok (hb1 phi (AC.a_size (flen g j)) ++ g_H g) (STKLO mem md) q -> ~ (FS <= q < FS + AC.FS_SIZE) ->
      ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) -> m2 (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
    { intros q Hq Hns Hnf Hnsh. apply MU1. rewrite unsigned_lit by lia.
      apply outside_In. intros lo hi Hin. cbn [In] in Hin.
      destruct Hin as [E|[E|[]]]; injection E as <- <-; intros Hc.
      - destruct (HSh q ltac:(lia)) as (_ & Eq & Hb).
        destruct (Hfrb (fr + 8 * (q - S3)) ltac:(lia)) as (_ & [Hr1|Hr1]).
        + apply Hns. unfold AC.a_store_ok. right; right; right. exists (fr + 8 * (q - S3)).
          split; [symmetry; exact Eq | right; left; lia].
        + apply Hnsh. exists (fr + 8 * (q - S3)). split; [unfold AC.FS_SIZE in *; lia | symmetry; exact Eq].
      - destruct (Hfrb q ltac:(lia)) as (_ & [Hr1|Hr1]).
        + apply Hns. unfold AC.a_store_ok. right; left. exact Hr1.
        + apply Hnf. unfold AC.FS_SIZE in *. lia. }
    destruct (a_fs_ok_store_AH AC.ASYMS _ _ _ _ _ _ mem m2 md FS LAWS HAH HwTP HFSr
                ltac:(unfold AC.FS_SIZE, APPMEM_END in *; lia) MU1
                (fun q _ Hw => WM1 _ Hw) (fun q Hq Hp => HpresM q Hq Hp) Hmeta1 Hagree1)
      as (HAH2 & _ & HSTK2 & _).
    assert (Hsh380_2 : exists sh2, bytes_at rsegs m2 S3 sh2 /\ length sh2 = 392%nat).
    { apply ba_present; [unfold LOWMEM_END in *; lia | unfold HIGHMEM_BEG in *; lia|].
      intros i Hi. apply Hshp2. apply HSh. lia. }
    assert (HAG2 : forall a, in_globals AF.frame_AG a -> addressable m2 a 1).
    { intros a Hin. pose proof (ag_bound a Hin) as Hab.
      apply (addr_keep _ mem m2 a 1 (HAG a Hin) MU1). intros i Hi.
      apply HnotW1; [destruct (HAG a Hin) as (_ & _ & _ & Hb); exact (proj1 (Hb i Hi))|].
      unfold AC.GT in HGTfr. lia. }
    assert (Hstk2S : stk rsegs m2 (g_S g - AF.SLOT_STACK) (g_S g)).
    { apply (fl_stk _ mem m2 _ _ Hwin MU1 WM1). intros x Hx. right.
      apply HpresM; [unfold AF.SLOT_STACK, APPMEM_END, HIGHMEM_BEG in *; lia|].
      exact (proj2 (Hwv x Hx)). }
    assert (HroM2 : ro_agree rsegs m2).
    { apply (ro_agree_same rsegs mem m2 Hro). intros a Ha. pose proof (ro_lo a Ha) as Hlo'.
      pose proof (bv_unsigned_in_range 64 a) as Ra. change (bv_modulus 64) with (2 ^ 64) in Ra.
      apply MU1. apply HW1app; [unfold app_mem; left; unfold LOWMEM_END; lia | unfold AC.GT in *; lia]. }
    assert (HFRA2 : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs m2 md).
    { apply (f30_fra_run g fr _ regs regs mem m2 md _ HFRA MU1 WM1 HroM2 Hrtdj1 HAH2 HSTK2 Hshp2 Hsh380_2);
        try reflexivity; rewrite ?HbvA.
      - intros x Hx. apply HW1app; [unfold app_mem; left; unfold LOWMEM_END; lia | unfold AC.GT in *; lia].
      - intros x Hx. apply HW1app; [apply Hfrapp; lia | lia].
      - intros x Hx. apply HW1app; [unfold app_mem; right; unfold HIGHMEM_BEG, APPMEM_END in *; lia | lia].
      - intros x Hx. apply HW1app; [unfold app_mem; right; unfold HIGHMEM_BEG, APPMEM_END in *; lia | lia].
      - intros x Hx. apply HW1app; [unfold app_mem; right; unfold HIGHMEM_BEG, APPMEM_END in *; lia | lia].
      - intros x Hx. apply HW1app; [unfold app_mem; right; unfold HIGHMEM_BEG, APPMEM_END in *; lia | lia].
      - intros x Hx. right. destruct Hstk2S as (_ & _ & HS). destruct (HS x Hx) as (_ & b & Hb).
        exists b. rewrite <- mb_mrd. exact Hb.
      - exact HAG2.
      - intros a H1 H2. apply (addr_keep _ mem m2 a 1 (HWAd a H1 H2) MU1). intros i Hi.
        apply HnotW1; [unfold app_mem; right; unfold AF.SLOT_STACK, HIGHMEM_BEG, APPMEM_END in *; lia|].
        intros Hc. apply H2. lia.
      - intros Hrec0. apply (f30_fsrec_keep _ mem m2 md _ fr FS Hrec0 HAH HwTP HFSr MU1).
        intros x Hx Hxlo Hxb _ _ _. apply HW1app; [exact Hx|]. intros Hc. apply Hxb. lia. }
    assert (Htpout : forall kk, 0 <= kk < 8 ->
              outside [(S3 + 56, S3 + 67); (fr + 528, fr + 532)] (AC.as_tp AC.ASYMS + kk)).
    { intros kk Hk. apply HW1app;
        [unfold app_mem; left; unfold AC.as_tp, AC.ASYMS, RT_TP, LOWMEM_END; cbn; lia|].
      unfold AC.as_tp, AC.ASYMS, RT_TP, AC.GT in *; cbn in *; lia. }
    destruct (f30_fp g fr (hb1 phi (AC.a_size (flen g j))) phi (flen g j) regs m2 md HFRA2 HinB)
      as (FS2 & HwTP2 & HFSr2 & HfsOK2 & _ & _ & _ & HFP2 & HTLS2).
    assert (EFS2 : FS2 = FS).
    { assert (HwTPm2 : word_mem rsegs m2 (AC.as_tp AC.ASYMS) FS).
      { apply (word_mem_frame rsegs mem m2 (AC.as_tp AC.ASYMS) FS HwTP). intros kk Hk.
        unfold mbyte. rewrite MU1; [reflexivity|].
        rewrite unsigned_lit by (unfold AC.as_tp, AC.ASYMS, RT_TP; cbn; lia). exact (Htpout kk Hk). }
      pose proof (word_mem_le8 rsegs m2 (AC.as_tp AC.ASYMS) FS HwTPm2 HFSr
                    ltac:(unfold AC.as_tp, AC.ASYMS, RT_TP; cbn; lia)
                    ltac:(unfold AC.as_tp, AC.ASYMS, RT_TP; cbn; lia)) as Hb1.
      pose proof (word_mem_le8 rsegs m2 (AC.as_tp AC.ASYMS) FS2 HwTP2 HFSr2
                    ltac:(unfold AC.as_tp, AC.ASYMS, RT_TP; cbn; lia)
                    ltac:(unfold AC.as_tp, AC.ASYMS, RT_TP; cbn; lia)) as Hb2.
      pose proof (fl_le8_eq [] m2 m2 (AC.as_tp AC.ASYMS) (Z_to_bv 64 FS2) (Z_to_bv 64 FS) Hb2 Hb1
                    (munch_refl [] m2) (fun _ _ => I)) as E.
      apply (f_equal (bv_unsigned (n := 64))) in E. rewrite !unsigned_lit in E by lia. exact E. }
    subst FS2.
    assert (Aphi2 : 50 <= flen g j -> addressable m2 phi 50).
    { intros H50. apply (addr_keep _ mem m2 phi 50 (addressable_prefix mem phi _ 50 Hphad ltac:(lia)) MU1).
      intros i Hi. apply HnotW1; [apply Hphapp; lia|]. intros Hc. apply (Hphfr (phi + i)); lia. }
    assert (Au2 : addressable m2 (fr + 2624) 6).
    { apply (addr_keep _ mem m2 _ 6 Haddu MU1). intros i Hi. apply HnotW1; [apply Hfrapp; lia | lia]. }
    assert (Hbcad : addressable mem RP.REAC_CTRL_PARSE_BC 6).
    { replace 6 with (RP.REAC_CTRL_PARSE_BC + 6 - RP.REAC_CTRL_PARSE_BC) by lia.
      apply addr_rng; [unfold RP.REAC_CTRL_PARSE_BC; lia | lia
                      | unfold RP.REAC_CTRL_PARSE_BC, APPMEM_END; lia|].
      intros a Ha. apply HAG. exists 0x21200, 7. split; [|unfold RP.REAC_CTRL_PARSE_BC in Ha; lia].
      unfold AF.frame_AG. cbn [In]. repeat (first [left; reflexivity | right]). }
    assert (Abc2 : addressable m2 RP.REAC_CTRL_PARSE_BC 6).
    { apply (addr_keep _ mem m2 _ 6 Hbcad MU1). intros i Hi.
      destruct Hbcad as (_ & _ & _ & Hb). destruct (Hb i Hi) as (Hbap & _).
      apply HnotW1; [exact Hbap|]. unfold RP.REAC_CTRL_PARSE_BC, AC.GT in *. lia. }
    assert (Hwad : addressable mem (sp - K30) K30).
    { replace K30 with (sp - (sp - K30)) at 2 by lia.
      apply addr_rng; [unfold HIGHMEM_BEG in *; lia | unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K; lia
                      | unfold APPMEM_END in *; lia|].
      intros a Ha. apply HWAd.
      - unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, AF.SLOT_STACK in *. lia.
      - intros Hc. destruct Hfrwin as [Hd|Hd]; lia. }
    assert (Aw2 : addressable m2 (sp - K30) K30).
    { apply (addr_keep _ mem m2 _ _ Hwad MU1). intros i Hi.
      apply HnotW1; [apply Happw; unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K in *; lia|].
      destruct Hfrwin as [Hc|Hc]; unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, AF.SLOT_STACK in *; lia. }
    assert (Ao2 : addressable m2 (fr + 448) 36).
    { apply (addr36 m2 (fr + 448) (Z_to_bv 8 0) (Z_to_bv 8 4)).
      - lia.
      - Z.div_mod_to_equations. lia.
      - unfold APPMEM_END. pose proof (Hfrapp (fr + 3135) ltac:(lia)) as H1.
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H1. lia.
      - intros i Hi. apply Hfrapp. lia.
      - intros k Hk. rewrite (sh_off fr 448 56 Hfr0 Hfr8 ltac:(lia)). fold (Sfr fr). fold S3.
        assert (Hk4 : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
        destruct Hk4 as [-> | [-> | [-> | ->]]]; rewrite <- Z.add_assoc; cbn [Z.add]; assumption.
      - rewrite (sh_off fr 448 56 Hfr0 Hfr8 ltac:(lia)). fold (Sfr fr). fold S3.
        rewrite <- Z.add_assoc. cbn [Z.add]. exact R4.
      - vm_compute. reflexivity.
      - vm_compute. reflexivity. }
    assert (Av2 : addressable m2 (fr + 528) 4).
    { apply (addr_chunk m2 (fr + 528) 4 (Z_to_bv 8 4)).
      - lia.
      - Z.div_mod_to_equations. lia.
      - lia.
      - pose proof (Hfrapp (fr + 3135) ltac:(lia)) as H1.
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H1. unfold APPMEM_END. lia.
      - intros i Hi. apply Hfrapp. lia.
      - rewrite (sh_off fr 528 66 Hfr0 Hfr8 ltac:(lia)). fold (Sfr fr). fold S3. exact R10.
      - right. replace (bv_signed (Z_to_bv 8 4)) with 4 by (vm_compute; reflexivity). lia. }
    assert (Hbphi2m : 50 <= flen g j -> bytes_at rsegs m2 phi (t_g (g_in g) j)).
    { intros H50. destruct (Hrec H50) as (_ & _ & Hbphi & _ & _).
      eapply fl_bytes; [exact Hbphi | exact MU1 |]. rewrite t_g_length. intros x Hx.
      change (Z.of_nat 50) with 50 in Hx.
      apply HW1app; [apply Hphapp; lia|]. intros Hc. apply (Hphfr x); lia. }
    assert (Hour2 : bytes_at rsegs m2 (fr + 2624) (OUR (g_in g))).
    { destruct HLK as (_ & _ & HOUR). unfold OURb in HOUR.
      eapply fl_bytes; [exact HOUR | exact MU1 |]. rewrite OUR_length. intros x Hx.
      change (Z.of_nat 6) with 6 in Hx. apply HW1app; [apply Hfrapp; lia | lia]. }
    assert (Hstk2w : stk rsegs m2 (sp - K30) sp).
    { apply (fl_stk _ mem m2 _ _ (stk_sub mem (g_S g - AF.SLOT_STACK) (g_S g) (sp - K30) sp Hwin
               ltac:(unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, FN_STACK, AF.SLOT_STACK in *; lia)
               ltac:(lia) ltac:(unfold HIGHMEM_BEG in *; lia) ltac:(lia)) MU1 WM1).
      intros x Hx. left. apply HW1app; [apply Happw; lia|].
      destruct Hfrwin as [Hc|Hc]; unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, AF.SLOT_STACK in *; lia. }
    pose proof (RT_real_cells _ _ _ RT2) as Hreal2.
    pose proof (RT_cf_cells _ _ _ RT2) as (Hcf1 & _ & _ & _ & _ & _ & Hcf240 & _).
    assert (HC254 : bytes_at rsegs m2 (BW.CF + 254) [Z_to_bv 8 1]).
    { pose proof (ba_sub m2 (RT_CF + 240) (cf_b [0; 0; 0; 0; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0])
                    14 1 Hcf240 ltac:(cbn; lia)) as HH.
      cbn [cf_b map firstn skipn Z.of_nat] in HH. exact HH. }
    assert (HC255 : bytes_at rsegs m2 (BW.CF + 255) [Z_to_bv 8 1]).
    { pose proof (ba_sub m2 (RT_CF + 240) (cf_b [0; 0; 0; 0; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0])
                    15 1 Hcf240 ltac:(cbn; lia)) as HH.
      cbn [cf_b map firstn skipn Z.of_nat] in HH. exact HH. }
    eapply evt_cut.
    { eapply (F30Call.f30_call_norm CLS) with (f := phi) (n := flen g j) (u := fr + 2624) (o := fr + 448) (v := fr + 528)
        (S := sp) (FS := FS) (fr := t_g (g_in g) j) (us := OUR (g_in g)) (junk := junk)
        (vb := le4 (Z_to_bv 64 (-1))).
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - unfold rg in Hr2. exact Hr2.
      - unfold APPMEM_END, AF.SLOT_STACK in *; lia.
      - unfold APPMEM_END, AF.SLOT_STACK in *; lia.
      - unfold APPMEM_END, AF.SLOT_STACK in *; lia.
      - unfold APPMEM_END, AF.SLOT_STACK in *; lia.
      - unfold APPMEM_END, AF.SLOT_STACK in *; lia.
      - unfold APPMEM_END, AF.SLOT_STACK in *; lia.
      - exact Hspm.
      - unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, HIGHMEM_BEG in *. lia.
      - exact Hstk2w.
      - exact (t_g_length (g_in g) j).
      - intros H50. destruct (Hrec H50) as (Hphi & _ & _ & _ & _).
        split; [lia|]. split; [unfold FN_STACK, AF.SLOT_STACK, APPMEM_END in *; lia|].
        split; [exact (Hbphi2m H50)|].
        left. unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, FN_STACK, AF.SLOT_STACK in *. lia.
      - unfold AC.GT in HGTfr. lia.
      - Z.div_mod_to_equations. lia.
      - lia.
      - exact Ho2.
      - destruct Hfrwin as [Hc|Hc]; unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, AF.SLOT_STACK in *;
          [left | right]; lia.
      - intros H50. apply (ivl_dj (fr + 448) (fr + 448 + 36) phi (phi + 50)); [lia | lia|].
        intros x H1 H2. exact (Hphfr x ltac:(lia) ltac:(lia)).
      - left. lia.
      - exact (OUR_length (g_in g)).
      - intros _. split; [lia|]. split; [exact Hour2|].
        destruct Hfrwin as [Hc|Hc]; unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, AF.SLOT_STACK in *;
          [left | right]; lia.
      - unfold AC.GT in HGTfr. lia.
      - Z.div_mod_to_equations. lia.
      - lia.
      - exact Hv2.
      - destruct Hfrwin as [Hc|Hc]; unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, AF.SLOT_STACK in *;
          [left | right]; lia.
      - right. lia.
      - (* the event cell and the 50 bytes at Phi: Phi is a heap byte, so it is below the frame or above it *)
        assert (Hnf : ~ (fr <= phi < fr + 3136)) by (intros Hc; exact (Hphfr phi ltac:(lia) Hc)).
        destruct (Z_lt_ge_dec phi fr) as [Hlt|Hge]; [right; lia|].
        left. destruct (Z_lt_ge_dec phi (fr + 3136)) as [Hc|Hc]; [exfalso; apply Hnf; lia | lia].
      - left. lia.
      - exact HroM2.
      - exact (RT_cells _ _ _ RT2).
      - exact (RT_shadow_rw _ _ _ RT2).
      - unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K in *. lia.
      - exact HappE.
      - exact Aw2.
      - intros H50. split; [exact (Aphi2 H50)|]. split; [exact Au2|]. split; apply Hfrapp; lia.
      - exact Ao2.
      - apply Hfrapp. lia.
      - right. unfold AC.GT in HGTfr. cbv delta [BW.CF SM.CF]. lia.
      - exact Av2.
      - right. unfold RT_HI, AC.GT in *. lia.
      - exact Abc2.
      - exact (real_cell_of m2 BW.REAL_BCMP BW.BCMP Hreal2 ltac:(vm_compute; reflexivity)).
      - exact (real_cell_of m2 BW.REAL_MEMCMP MC.MEMCMP Hreal2 ltac:(vm_compute; reflexivity)).
      - exact Hcf1.
      - exact HC254.
      - exact HC255.
      - change (Sem.reg_get regs 4) with (getr regs 4).
        rewrite Hr4, unsigned_lit by (unfold AC.as_tp, AC.ASYMS, RT_TP; cbn; lia).
        rewrite Haspz in HFP2. exact HFP2.
      - change (Sem.reg_get regs 4) with (getr regs 4).
        rewrite Hr4, unsigned_lit by (unfold AC.as_tp, AC.ASYMS, RT_TP; cbn; lia).
        rewrite Haspz in HTLS2. exact HTLS2.
      - unfold AC.GT in HGTfr. lia.
      - unfold AC.GT in HGTfr. lia. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 &
                Ems3 & MU2 & WM2 & HRO3 & ST3 & HRo3 & HRv3 & AC3 & SW3 & AW3 & HFP3 & HTLS3). subst ms'.
    assert (MUa : munch ([(S3 + 56, S3 + 67); (fr + 528, fr + 532)] ++
                         [(fr + 448, fr + 448 + 36); (fr + 528, fr + 528 + 4); (sp - K30, sp)] ++
                         fp_w [1%nat] FS ++ [(shadow_addr (sp - K30), shadow_addr sp)]) mem m3).
    { apply (munch_trans _ mem m2 m3).
      - apply (munch_weaken [(S3 + 56, S3 + 67); (fr + 528, fr + 532)]); [|exact MU1].
        intros x Hx. exact (proj1 (outside_app _ _ x Hx)).
      - apply (munch_weaken ([(fr + 448, fr + 448 + 36); (fr + 528, fr + 528 + 4); (sp - K30, sp)] ++
                 fp_w [1%nat] FS ++ [(shadow_addr (sp - K30), shadow_addr sp)])); [|exact MU2].
        intros x Hx. exact (proj2 (outside_app _ _ x Hx)). }
    assert (WMa : wmono rsegs mem m3) by exact (wmono_trans rsegs mem m2 m3 WM1 WM2).
    assert (HfsOK3 : AC.a_fs_ok m3 FS).
    { refine (f30_fs_ok m2 m3 FS _ _ _ _ _ _ HfsOK2 MU2 _ HFP3).
      intros x Hx H1 H2. apply outside_In. intros lo hi Hin.
      rewrite fpw1_eq in Hin. cbn [In app] in Hin.
      assert (Hap : app_mem x) by (apply HFSapp; unfold AC.FS_SIZE; lia).
      destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as <- <-;
        first [ exact H1 | exact H2
              | (destruct (Hfrb (fr + 448) ltac:(lia)) as (_ & [Hc|Hc]); unfold AC.FS_SIZE in *; lia)
              | (destruct (Hfrb (fr + 528) ltac:(lia)) as (_ & [Hc|Hc]); unfold AC.FS_SIZE in *; lia)
              | (unfold AC.FS_SIZE in *; lia)
              | (intros Hc; exact (app_not_shadow x Hap (HFSsh x Hc)))
              | (intros Hc; exact (app_not_shadow x Hap (HWsh x Hc))) ]. }
    assert (Hshout3 : forall y, app_mem y -> fr <= y < fr + 3136 ->
              outside ([(fr + 448, fr + 448 + 36); (fr + 528, fr + 528 + 4); (sp - K30, sp)] ++
                       fp_w [1%nat] FS ++ [(shadow_addr (sp - K30), shadow_addr sp)]) (shadow_addr y)).
    { intros y Hy Hyf.
      assert (Hy0 : 0 <= y) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hy; lia).
      pose proof (shadow_of_app y Hy) as Hsy.
      apply outside_In. intros lo hi Hin. rewrite fpw1_eq in Hin. cbn [In app] in Hin.
      destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as <- <-.
      - intros Hc. exact (app_not_shadow (shadow_addr y) (Hfrapp (shadow_addr y) ltac:(lia)) Hsy).
      - intros Hc. exact (app_not_shadow (shadow_addr y) (Hfrapp (shadow_addr y) ltac:(lia)) Hsy).
      - intros Hc. exact (app_not_shadow (shadow_addr y) (Happw (shadow_addr y) ltac:(lia)) Hsy).
      - intros Hc.
        exact (app_not_shadow (shadow_addr y) (HFSapp (shadow_addr y) ltac:(unfold AC.FS_SIZE; lia)) Hsy).
      - intros Hc.
        exact (app_not_shadow (shadow_addr y) (HFSapp (shadow_addr y) ltac:(unfold AC.FS_SIZE; lia)) Hsy).
      - intros Hc.
        exact (app_not_shadow (shadow_addr y) (HFSapp (shadow_addr y) ltac:(unfold AC.FS_SIZE; lia)) Hsy).
      - intros Hc.
        destruct (Hfrb (fr + 448) ltac:(lia)) as (_ & [Hr1|Hr1]);
          (pose proof (sh_dj_out (FS + 1085440) (FS + 2134016) y ltac:(lia) ltac:(lia) Hy0
                         ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)
                         ltac:(right; unfold AC.FS_SIZE in *; lia)); lia).
      - intros Hc.
        pose proof (sh_dj_out (sp - K30) sp y ltac:(unfold HIGHMEM_BEG in *; lia)
                      ltac:(unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K; lia) Hy0
                      ltac:(unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K; Z.div_mod_to_equations; lia)
                      ltac:(Z.div_mod_to_equations; lia)
                      ltac:(destruct Hfrwin as [Hd|Hd];
                            unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, AF.SLOT_STACK in *; lia)). lia. }
    assert (Ao3 : addressable m3 (fr + 448) 36).
    { apply (addr_keep _ m2 m3 _ 36 Ao2 MU2). intros i Hi.
      exact (Hshout3 (fr + 448 + i) (Hfrapp (fr + 448 + i) ltac:(lia)) ltac:(lia)). }
    assert (Av3 : addressable m3 (fr + 528) 4).
    { apply (addr_keep _ m2 m3 _ 4 Av2 MU2). intros i Hi.
      exact (Hshout3 (fr + 528 + i) (Hfrapp (fr + 528 + i) ltac:(lia)) ltac:(lia)). }
    assert (Au3 : addressable m3 (fr + 2624) 6).
    { apply (addr_keep _ m2 m3 _ 6 Au2 MU2). intros i Hi.
      exact (Hshout3 (fr + 2624 + i) (Hfrapp (fr + 2624 + i) ltac:(lia)) ltac:(lia)). }
    apply evt_done.
    do 3 eexists. split; [reflexivity|].
    split; [reflexivity|].
    do 14 (split; [reflexivity|]).
    split.
    { eapply munch_weaken; [|exact MUa]. intros x Hx.
      first [ exact Hx
            | (replace (fr + 448 + 36) with (fr + 484) in Hx by lia;
               replace (fr + 528 + 4) with (fr + 532) in Hx by lia; exact Hx) ]. }
    split; [exact WMa|]. split; [exact HRO3|]. split; [exact SW3|].
    split; [exact ST3|]. split; [exact HfsOK3|].
    split; [exact HRo3|].
    split; [eexists; exact HRv3|].
    split.
    { intros e He.
      change (t_cls (g_in g) j) with (classify (flen g j) (t_g (g_in g) j) (OUR (g_in g))) in He.
      rewrite He in HRv3. cbn [PCB.reac_ctrl_classify_box_frame_ev] in HRv3.
      destruct HRv3 as ((_ & Hb) & _). cbn [cells_bytes cbytes app] in Hb. rewrite app_nil_r in Hb.
      exact Hb. }
    split; [exact Ao3|]. split; [exact Av3|]. split; [exact Au3 | exact AW3].
  - (* the exit: the heap invariant rebuilt, then F31's entry cut *)
    intros R0 pc' mem3 regs' md'
      (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er21 & Er22 & Er23 & Er24 & Er25 & Er26 & Er10 &
       MU & WM & HRO3 & SW3 & ST3 & HfsOK3 & HBo3 & (vb3 & HBv3) & Hu32 & Ao3 & Av3 & Au3 & AW3) Hreg Hmat.
    subst pc'.
    assert (HFSGT : AC.GT <= FS) by (unfold AC.GT, SM.ASAN_GT in *; lia).
    assert (F2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (F3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (F4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (F8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (F9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (F18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (F19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (F21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (F22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (F23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
    assert (F24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (F25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
    assert (F26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (F10 : getr regs' 10 = Z_to_bv 64 (cl_r (t_cls (g_in g) j))) by (rewrite Hreg; exact Er10).
    assert (Easp' : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite F2; reflexivity).
    assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
      ~ AC.a_store_ok (hb1 phi (AC.a_size (flen g j)) ++ g_H g) (STKLO mem md) q -> ~ (FS <= q < FS + AC.FS_SIZE) ->
      ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) ->
      mem3 (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
    { intros q Hq Hns Hnf Hnsh. apply MU. rewrite unsigned_lit by lia.
      apply outside_In. intros lo hi Hin. rewrite fpw1_eq in Hin. cbn [In app] in Hin.
      destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]; injection E as <- <-; intros Hc.
      - destruct (HSh q ltac:(lia)) as (_ & Eq & Hb).
        destruct (Hfrb (fr + 8 * (q - S3)) ltac:(lia)) as (_ & [Hr1|Hr1]).
        + apply Hns. unfold AC.a_store_ok. right; right; right. exists (fr + 8 * (q - S3)).
          split; [symmetry; exact Eq | right; left; lia].
        + apply Hnsh. exists (fr + 8 * (q - S3)). split; [unfold AC.FS_SIZE in *; lia | symmetry; exact Eq].
      - destruct (Hfrb q ltac:(lia)) as (_ & [Hr1|Hr1]);
          [apply Hns; unfold AC.a_store_ok; right; left; exact Hr1
          | apply Hnf; unfold AC.FS_SIZE in *; lia].
      - destruct (Hfrb q ltac:(lia)) as (_ & [Hr1|Hr1]);
          [apply Hns; unfold AC.a_store_ok; right; left; exact Hr1
          | apply Hnf; unfold AC.FS_SIZE in *; lia].
      - destruct (Hfrb q ltac:(lia)) as (_ & [Hr1|Hr1]);
          [apply Hns; unfold AC.a_store_ok; right; left; exact Hr1
          | apply Hnf; unfold AC.FS_SIZE in *; lia].
      - apply Hns. unfold AC.a_store_ok. right; left.
        unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, FN_STACK, AF.SLOT_STACK in *.
        split; [lia | unfold APPMEM_END in *; lia].
      - apply Hnf. unfold AC.FS_SIZE in *. lia.
      - apply Hnf. unfold AC.FS_SIZE in *. lia.
      - apply Hnf. unfold AC.FS_SIZE in *. lia.
      - apply Hnsh. exists (FS + 1085440 + 8 * (q - shadow_addr (FS + 1085440))).
        unfold shadow_addr in Hc |- *. unfold AC.FS_SIZE. Z.div_mod_to_equations. lia.
      - apply Hns. unfold AC.a_store_ok. right; right; right.
        exists (sp - K30 + 8 * (q - shadow_addr (sp - K30))).
        unfold shadow_addr in Hc |- *. unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K in *.
        split; [Z.div_mod_to_equations; lia|].
        right; left. unfold FN_STACK, AF.SLOT_STACK in Hlow. Z.div_mod_to_equations. lia. }
    destruct (AC.a_laws_fs_store _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem mem3 md FS HAH HwTP HFSr
                Hagree (fun q _ Hw => WM _ Hw) HfsOK3) as (HAH3 & HOWN3 & HSTK3 & HSTKHI3).
    assert (Hrtdj : rt_disjoint ([(S3 + 56, S3 + 67); (fr + 528, fr + 532)] ++
                      [(fr + 448, fr + 448 + 36); (fr + 528, fr + 528 + 4); (sp - K30, sp)] ++
                      fp_w [1%nat] FS ++ [(shadow_addr (sp - K30), shadow_addr sp)])).
    { pose proof (in_shadow_bnd _ (HFSsh (shadow_addr (FS + 1085440))
                    ltac:(unfold shadow_addr; Z.div_mod_to_equations; lia))) as Hb1.
      pose proof (in_shadow_bnd _ (HWsh (shadow_addr (sp - K30))
                    ltac:(unfold shadow_addr, K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K;
                          Z.div_mod_to_equations; lia))) as Hb3.
      rewrite fpw1_eq.
      unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
        RT_AGLOB, RT_AGLOB_LEN.
      unfold LOWMEM_END, HIGHMEM_BEG, AC.GT, AC.FS_SIZE in *. cbn [disjoint_from app].
      repeat split; first [left; lia | right; lia | exact I]. }
    assert (Hshp3 : forall a, in_shadow a -> exists b, mrd rsegs mem3 (wa a) = Some b)
      by (intros a Ha; exact (proj2 (SW3 a Ha))).
    assert (Hsh380 : exists sh3, bytes_at rsegs mem3 S3 sh3 /\ length sh3 = 392%nat).
    { apply ba_present; [unfold LOWMEM_END in *; lia | unfold HIGHMEM_BEG in *; lia|].
      intros i Hi. apply Hshp3. apply HSh. lia. }
    assert (HWsh3 : forall y, app_mem y -> ~ (fr + 448 <= y < fr + 536) ->
              ~ (FS + 1085440 <= y < FS + 2134016) -> ~ (sp - K30 <= y < sp) ->
              outside ([(S3 + 56, S3 + 67); (fr + 528, fr + 532)] ++
                       [(fr + 448, fr + 448 + 36); (fr + 528, fr + 528 + 4); (sp - K30, sp)] ++
                       fp_w [1%nat] FS ++ [(shadow_addr (sp - K30), shadow_addr sp)]) (shadow_addr y)).
    { intros y Hy Hn Hnf Hnw.
      assert (Hy0 : 0 <= y) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hy; lia).
      apply HWsh2; [exact (shadow_of_app y Hy)| | |].
      - exact (Hshout y 56 67 Hy0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      - intros Hc.
        pose proof (sh_dj_out (FS + 1085440) (FS + 2134016) y ltac:(lia) ltac:(lia) Hy0
                      ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)
                      ltac:(lia)). lia.
      - intros Hc.
        pose proof (sh_dj_out (sp - K30) sp y ltac:(unfold HIGHMEM_BEG in *; lia)
                      ltac:(unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K; lia) Hy0
                      ltac:(unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K; Z.div_mod_to_equations; lia)
                      ltac:(Z.div_mod_to_equations; lia) ltac:(lia)). lia. }
    assert (HAG3 : forall a, in_globals AF.frame_AG a -> addressable mem3 a 1).
    { intros a Hin. pose proof (ag_bound a Hin) as Hab.
      apply (addr_keep _ mem mem3 a 1 (HAG a Hin) MU). intros i Hi.
      destruct (HAG a Hin) as (_ & _ & _ & Hb).
      apply HWsh3; [exact (proj1 (Hb i Hi)) | | |]; unfold AC.GT, SM.ASAN_GT, HIGHMEM_BEG in *; lia. }
    assert (Hfrout : forall x, fr <= x < fr + 3136 -> ~ (fr + 448 <= x < fr + 484) ->
              ~ (fr + 528 <= x < fr + 532) ->
              outside ([(S3 + 56, S3 + 67); (fr + 528, fr + 532)] ++
                       [(fr + 448, fr + 448 + 36); (fr + 528, fr + 528 + 4); (sp - K30, sp)] ++
                       fp_w [1%nat] FS ++ [(shadow_addr (sp - K30), shadow_addr sp)]) x).
    { intros x Hx H1 H2. apply HWout;
        [ intros Hs; exact (app_not_shadow x (Hfrapp x Hx) Hs) | exact H1 | exact H2
        | destruct Hfrwin as [Hc|Hc]; unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, AF.SLOT_STACK in *; lia
        | destruct (Hfrb x Hx) as (_ & [Hc|Hc]); unfold AC.FS_SIZE in *; lia
        | destruct (Hfrb x Hx) as (_ & [Hc|Hc]); unfold AC.FS_SIZE in *; lia
        | destruct (Hfrb x Hx) as (_ & [Hc|Hc]); unfold AC.FS_SIZE in *; lia ]. }
    assert (Hfrpres : forall x, fr <= x < fr + 3136 ->
              outside ([(S3 + 56, S3 + 67); (fr + 528, fr + 532)] ++
                       [(fr + 448, fr + 448 + 36); (fr + 528, fr + 528 + 4); (sp - K30, sp)] ++
                       fp_w [1%nat] FS ++ [(shadow_addr (sp - K30), shadow_addr sp)]) x \/
              exists b, mrd rsegs mem3 (wa x) = Some b).
    { intros x Hx.
      destruct (Z_le_gt_dec (fr + 448) x) as [H1|H1]; [destruct (Z_lt_ge_dec x (fr + 484)) as [H2|H2]|].
      - right. destruct HBo3 as ((_ & Hb) & _). cbn [cells_bytes cbytes app] in Hb.
        rewrite app_nil_r in Hb.
        replace x with (fr + 448 + (x - (fr + 448))) by lia.
        apply (ba_some mem3 (fr + 448) _ _ Hb). rewrite tB_length. cbn [Z.of_nat]. lia.
      - destruct (Z_le_gt_dec (fr + 528) x) as [H3|H3]; [destruct (Z_lt_ge_dec x (fr + 532)) as [H4|H4]|].
        + right. destruct HBv3 as ((Hwf & Hb) & _). cbn [cells_bytes cbytes app] in Hb.
          rewrite app_nil_r in Hb.
          assert (Hl : length vb3 = 4%nat) by (cbn [cells_wf cell_wf] in Hwf; tauto).
          replace x with (fr + 528 + (x - (fr + 528))) by lia.
          apply (ba_some mem3 (fr + 528) _ _ Hb). rewrite Hl. cbn [Z.of_nat]. lia.
        + left. apply Hfrout; [exact Hx | lia | lia].
        + left. apply Hfrout; [exact Hx | lia | lia].
      - left. apply Hfrout; [exact Hx | lia | lia]. }
    assert (Hstk3S : stk rsegs mem3 (g_S g - AF.SLOT_STACK) (g_S g)).
    { apply (fl_stk _ mem mem3 _ _ Hwin MU WM). intros x Hx.
      destruct (Z_le_gt_dec fr x) as [H1|H1]; [destruct (Z_lt_ge_dec x (fr + 3136)) as [H2|H2]|].
      - apply Hfrpres. lia.
      - destruct (Z_le_gt_dec (sp - K30) x) as [H5|H5]; [destruct (Z_lt_ge_dec x sp) as [H6|H6]|].
        + right. destruct ST3 as (_ & _ & HS). exact (proj2 (HS x ltac:(lia))).
        + left. apply HWout;
            [ intros Hs; exact (app_not_shadow x ltac:(unfold app_mem; right;
                unfold AF.SLOT_STACK, APPMEM_END in *; lia) Hs)
            | lia | lia | lia | unfold AC.FS_SIZE in *; lia | unfold AC.FS_SIZE in *; lia
            | unfold AC.FS_SIZE in *; lia ].
        + left. apply HWout;
            [ intros Hs; exact (app_not_shadow x ltac:(unfold app_mem; right;
                unfold AF.SLOT_STACK, APPMEM_END in *; lia) Hs)
            | lia | lia | lia | unfold AC.FS_SIZE in *; lia | unfold AC.FS_SIZE in *; lia
            | unfold AC.FS_SIZE in *; lia ].
      - destruct (Z_le_gt_dec (sp - K30) x) as [H5|H5]; [destruct (Z_lt_ge_dec x sp) as [H6|H6]|].
        + right. destruct ST3 as (_ & _ & HS). exact (proj2 (HS x ltac:(lia))).
        + left. apply HWout;
            [ intros Hs; exact (app_not_shadow x ltac:(unfold app_mem; right;
                unfold AF.SLOT_STACK, APPMEM_END in *; lia) Hs)
            | lia | lia | lia | unfold AC.FS_SIZE in *; lia | unfold AC.FS_SIZE in *; lia
            | unfold AC.FS_SIZE in *; lia ].
        + left. apply HWout;
            [ intros Hs; exact (app_not_shadow x ltac:(unfold app_mem; right;
                unfold AF.SLOT_STACK, APPMEM_END in *; lia) Hs)
            | lia | lia | lia | unfold AC.FS_SIZE in *; lia | unfold AC.FS_SIZE in *; lia
            | unfold AC.FS_SIZE in *; lia ]. }
    assert (HFRA3 : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem3 md).
    { apply (f30_fra_run g fr _ regs regs' mem mem3 md _ HFRA MU WM HRO3 Hrtdj HAH3 HSTK3 Hshp3 Hsh380);
        rewrite ?HbvA.
      - intros x Hx. apply HWout;
          [ intros Hs; pose proof (in_shadow_bnd x Hs); unfold LOWMEM_END in *; lia
          | unfold AC.GT in *; lia | unfold AC.GT in *; lia
          | unfold HIGHMEM_BEG in *; lia
          | unfold AC.GT in *; lia | unfold AC.GT in *; lia | unfold AC.GT in *; lia ].
      - intros x Hx. apply Hfrout; [lia | lia | lia].
      - intros x Hx. apply HWout;
          [ intros Hs; pose proof (in_shadow_bnd x Hs); unfold HIGHMEM_BEG in *; lia
          | lia | lia | lia | unfold AC.FS_SIZE in *; lia | unfold AC.FS_SIZE in *; lia
          | unfold AC.FS_SIZE in *; lia ].
      - intros x Hx. apply HWout;
          [ intros Hs; pose proof (in_shadow_bnd x Hs); unfold HIGHMEM_BEG in *; lia
          | lia | lia | lia | unfold AC.FS_SIZE in *; lia | unfold AC.FS_SIZE in *; lia
          | unfold AC.FS_SIZE in *; lia ].
      - intros x Hx. apply HWout;
          [ intros Hs; pose proof (in_shadow_bnd x Hs); unfold HIGHMEM_BEG in *; lia
          | lia | lia | lia | unfold AC.FS_SIZE in *; lia | unfold AC.FS_SIZE in *; lia
          | unfold AC.FS_SIZE in *; lia ].
      - intros x Hx. apply HWout;
          [ intros Hs; pose proof (in_shadow_bnd x Hs); unfold HIGHMEM_BEG in *; lia
          | lia | lia | lia | unfold AC.FS_SIZE in *; lia | unfold AC.FS_SIZE in *; lia
          | unfold AC.FS_SIZE in *; lia ].
      - intros x Hx. right. destruct Hstk3S as (_ & _ & HS). destruct (HS x Hx) as (_ & b & Hb).
        exists b. rewrite <- mb_mrd. exact Hb.
      - exact HAG3.
      - intros a H1 H2.
        destruct (Z_le_gt_dec (sp - K30) a) as [Ha1|Ha1]; [destruct (Z_lt_ge_dec a sp) as [Ha2|Ha2]|].
        + exact (addr_sub mem3 (sp - K30) K30 a 1 AW3 ltac:(lia) ltac:(lia) ltac:(lia)).
        + apply (addr_keep _ mem mem3 a 1 (HWAd a H1 H2) MU). intros i Hi.
          apply HWsh3;
            [ unfold app_mem; right; unfold AF.SLOT_STACK, HIGHMEM_BEG, APPMEM_END in *; lia
            | intros Hc; apply H2; lia | unfold AF.SLOT_STACK, AC.FS_SIZE in *; lia | lia ].
        + apply (addr_keep _ mem mem3 a 1 (HWAd a H1 H2) MU). intros i Hi.
          apply HWsh3;
            [ unfold app_mem; right; unfold AF.SLOT_STACK, HIGHMEM_BEG, APPMEM_END in *; lia
            | intros Hc; apply H2; lia | unfold AF.SLOT_STACK, AC.FS_SIZE in *; lia | lia ].
      - intros Hrec0. apply (f30_fsrec_keep _ mem mem3 md _ fr FS Hrec0 HAH HwTP HFSr MU).
        intros x Hx Hxlo Hxb Hx1 Hx2 Hx3. apply HWout;
          [ intros Hs; exact (app_not_shadow x Hx Hs) | intros Hc; apply Hxb; lia | intros Hc; apply Hxb; lia
          | unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, FN_STACK, AF.SLOT_STACK in *; lia
          | exact Hx1 | exact Hx2 | exact Hx3 ].
      - exact F2.
      - exact F3.
      - exact F4.
      - exact F8.
      - exact F9.
      - exact F19.
      - exact F26. }
    assert (HFRA3' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem3 md')
      by (apply (sl_fra_move B APIf ra g fr _ regs' regs' mem3 md md' HFRA3); try reflexivity; exact Hmat).
    (* ENT: the run writes no entry block, image byte, stack byte at or above S, nor a shadow byte of these *)
    assert (HENT3 : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem3 md).
    { apply (ent_munch APIf g _ mem mem3 md _ HENT HAH (proj1 (fr_munch_ul _ _ _) MU));
        [| exact HSTK3 | exact HSTKHI3 | intros a Hia Hio; exact (proj2 (HOWN3 a) Hio)].
      intros x Hk. apply (proj2 (fr_outside_lib _ _)).
      destruct Hk as [Hblkk | [Hik | [Habk | [(b & Hor & ->) | Hblks]]]].
      - destruct Hblkk as (q & k & i & Hinq & Hni & Hi & ->).
        assert (Hinq' : In (q, k) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
          by (apply in_or_app; right; exact Hinq).
        destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md q k HAH Hinq') as (_ & _ & Hqlo & _ & Hqall).
        destruct (Hqall (q + i) ltac:(lia)) as (Hap & _ & _ & _ & Hnfs).
        assert (Hnfr : ~ (fr <= q + i < fr + 3136)).
        { intros Hc. exact (fra_blk B APIf ra g fr _ regs mem md q k (q + i) HFRA Hinq' ltac:(lia) Hc). }
        assert (HnFS : ~ (FS <= q + i < FS + AC.FS_SIZE)).
        { intros Hc. exact (Hnfs (a_fs_in AC.ASYMS mem FS (q + i) HwTP HFSr Hc)). }
        apply HWout;
          [ intros Hs; exact (app_not_shadow _ Hap Hs) | intros Hc; apply Hnfr; lia | intros Hc; apply Hnfr; lia
          | unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, FN_STACK, AF.SLOT_STACK in *; lia
          | intros Hc; apply HnFS; unfold AC.FS_SIZE; lia | intros Hc; apply HnFS; unfold AC.FS_SIZE; lia
          | intros Hc; apply HnFS; unfold AC.FS_SIZE; lia ].
      - pose proof (img_below_GT x Hik) as Hxg. apply HWout;
          [ intros Hs; pose proof (in_shadow_bnd x Hs); unfold LOWMEM_END, AC.GT in *; lia
          | unfold AC.GT in *; lia | unfold AC.GT in *; lia
          | unfold HIGHMEM_BEG, AC.GT in *; lia
          | unfold AC.GT in *; lia | unfold AC.GT in *; lia | unfold AC.GT in *; lia ].
      - apply HWout;
          [ intros Hs; pose proof (in_shadow_bnd x Hs); unfold HIGHMEM_BEG in *; lia
          | lia | lia | lia | unfold AF.SLOT_STACK, AC.FS_SIZE in *; lia | unfold AF.SLOT_STACK, AC.FS_SIZE in *; lia
          | unfold AF.SLOT_STACK, AC.FS_SIZE in *; lia ].
      - destruct Hor as [Hib | Hrb].
        + pose proof (img_below_GT b Hib) as Hbg.
          apply HWsh3;
            [ unfold app_mem, LOWMEM_END, AC.GT in *; left; lia | unfold AC.GT in *; lia
            | unfold AC.GT in *; lia | unfold HIGHMEM_BEG, AC.GT in *; lia ].
        + apply HWsh3;
            [ unfold app_mem; right; unfold HIGHMEM_BEG, APPMEM_END in *; lia | lia
            | unfold AF.SLOT_STACK, AC.FS_SIZE in *; lia | lia ].
      - (* cf5ad0d7203: ent_kept's fifth part, the shadow of an entry block the target does not keep *)
        destruct Hblks as (q & k & i & Hinq & Hni & Hi & ->).
        assert (Hinq' : In (q, k) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
          by (apply in_or_app; right; exact Hinq).
        destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md q k HAH Hinq') as (_ & _ & Hqlo & _ & Hqall).
        destruct (Hqall (q + i) ltac:(lia)) as (Hap & _ & _ & _ & Hnfs).
        assert (Hnfr : ~ (fr <= q + i < fr + 3136)).
        { intros Hc. exact (fra_blk B APIf ra g fr _ regs mem md q k (q + i) HFRA Hinq' ltac:(lia) Hc). }
        assert (HnFS : ~ (FS <= q + i < FS + AC.FS_SIZE)).
        { intros Hc. exact (Hnfs (a_fs_in AC.ASYMS mem FS (q + i) HwTP HFSr Hc)). }
        apply HWsh3;
          [ exact Hap | intros Hc; apply Hnfr; lia | intros Hc; apply HnFS; unfold AC.FS_SIZE; lia
          | unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, FN_STACK, AF.SLOT_STACK in *; lia ]. }
    assert (HENT3' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem3 md')
      by exact (ent_mat APIf g _ mem3 md md' HENT3 Hmat).
    (* what the run misses, for the transports of the cut bundles *)
    set (WT := [(S3 + 56, S3 + 67); (fr + 528, fr + 532)] ++
               [(fr + 448, fr + 448 + 36); (fr + 528, fr + 528 + 4); (sp - K30, sp)] ++
               fp_w [1%nat] FS ++ [(shadow_addr (sp - K30), shadow_addr sp)]) in *.
    assert (Hphiout : forall x, phi <= x < phi + AC.a_size (flen g j) -> outside WT x).
    { intros x Hx. apply HWout;
        [ intros Hs; exact (app_not_shadow x (Hphapp x Hx) Hs)
        | intros Hc; exact (Hphfr x Hx ltac:(lia))
        | intros Hc; exact (Hphfr x Hx ltac:(lia))
        | unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, FN_STACK, AF.SLOT_STACK in *; lia
        | intros Hc; exact (Hphfs x Hx ltac:(unfold AC.FS_SIZE in *; lia))
        | intros Hc; exact (Hphfs x Hx ltac:(unfold AC.FS_SIZE in *; lia))
        | intros Hc; exact (Hphfs x Hx ltac:(unfold AC.FS_SIZE in *; lia)) ]. }
    assert (HWA_ : forall x, A <= x < A + 416 -> outside WT x).
    { intros x Hx. apply HWout;
        [ intros Hs; pose proof (in_shadow_bnd x Hs); unfold HIGHMEM_BEG in *; lia
        | lia | lia | lia | unfold AF.SLOT_STACK, AC.FS_SIZE in *; lia | unfold AF.SLOT_STACK, AC.FS_SIZE in *; lia
        | unfold AF.SLOT_STACK, AC.FS_SIZE in *; lia ]. }
    assert (Hfrsh : forall y, fr <= y < fr + 3136 -> ~ (fr + 448 <= y < fr + 536) -> outside WT (shadow_addr y)).
    { intros y Hy Hn. apply HWsh3; [apply Hfrapp; lia | exact Hn | |].
      - intros Hc. destruct (Hfrb y Hy) as (_ & [Hd|Hd]); unfold AC.FS_SIZE in *; lia.
      - intros Hc. destruct Hfrwin as [Hd|Hd]; lia. }
    assert (HWS : forall i, 0 <= i < 6 -> outside WT (shadow_addr (fr + 2624 + i)))
      by (intros i Hi; apply Hfrsh; [lia | intros Hc; lia]).
    assert (HWS17 : forall i, 0 <= i < 17 -> outside WT (shadow_addr (fr + 2691 + i)))
      by (intros i Hi; apply Hfrsh; [lia | intros Hc; lia]).
    assert (HWR : forall i, 0 <= i < 152 -> outside WT (shadow_addr (fr + 2688 + i)))
      by (intros i Hi; apply Hfrsh; [lia | intros Hc; lia]).
    assert (HWP : forall x, g_p g <= x < g_p g + g_n g -> outside WT x /\ outside WT (shadow_addr x)).
    { intros x Hx.
      assert (Hinq' : In (g_p g, g_n g) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
        by (apply in_or_app; right; apply HinP; lia).
      destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md _ _ HAH Hinq') as (_ & _ & Hqlo & _ & Hqall).
      destruct (Hqall x ltac:(lia)) as (Hap & _ & _ & _ & Hnfs).
      assert (Hnfr : ~ (fr <= x < fr + 3136)).
      { intros Hc. exact (fra_blk B APIf ra g fr _ regs mem md _ _ x HFRA Hinq' ltac:(lia) Hc). }
      assert (HnFS : ~ (FS <= x < FS + AC.FS_SIZE)).
      { intros Hc. exact (Hnfs (a_fs_in AC.ASYMS mem FS x HwTP HFSr Hc)). }
      split.
      - apply HWout;
          [ intros Hs; exact (app_not_shadow _ Hap Hs) | intros Hc; apply Hnfr; lia | intros Hc; apply Hnfr; lia
          | unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, FN_STACK, AF.SLOT_STACK in *; lia
          | intros Hc; apply HnFS; unfold AC.FS_SIZE; lia | intros Hc; apply HnFS; unfold AC.FS_SIZE; lia
          | intros Hc; apply HnFS; unfold AC.FS_SIZE; lia ].
      - apply HWsh3;
          [ exact Hap | intros Hc; apply Hnfr; lia | intros Hc; apply HnFS; unfold AC.FS_SIZE; lia
          | unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, FN_STACK, AF.SLOT_STACK in *; lia ]. }
    assert (HWB : 50 <= flen g j -> forall x, phi <= x < phi + flen g j -> outside WT x)
      by (intros H50 x Hx; apply Hphiout; lia).
    assert (HA416' : 416 <= A) by (unfold HIGHMEM_BEG in *; lia).
    assert (HAtop : A + 416 <= 2 ^ 64) by lia.
    (* the exit cut *)
    rewrite <- SEGS. apply Hexit.
    exists phi, regs', mem3, md', fr. split; [reflexivity|]. split; [exact HFRA3'|]. split; [exact HENT3'|].
    split; [exact Hgn|]. split; [exact Hj|].
    split.
    { split; [exact Hphi0|]. apply (addr_keep _ mem mem3 phi _ Hphad MU).
      intros i Hi.
      apply HWsh3; [apply Hphapp; lia | | |].
      - intros Hc. exact (Hphfr (phi + i) ltac:(lia) ltac:(lia)).
      - intros Hc. exact (Hphfs (phi + i) ltac:(lia) ltac:(unfold AC.FS_SIZE in *; lia)).
      - unfold K30, REAC_CTRL_CLASSIFY_BOX_FRAME_K, FN_STACK, AF.SLOT_STACK in *; lia. }
    split; [exact (flsi_keep g j fr regs regs' mem mem3 WT A HFLSI MU WM F9 Hr9 HA416' HAtop HWA_ Hfrpres HWS HWS17
                     HWP HWR)|].
    split; [apply (lk_keep g fr j regs regs' mem mem3 WT HLK MU F21); intros x Hx; apply Hfrout; lia|].
    split; [exact (fls_keep g j phi fr regs regs' mem mem3 WT A HFLS MU WM F9 F18 F22 F23 F24 F25 Hr9 HA416' HAtop
                     HWA_ Hfrpres HWS HWS17 HWP HWB HWR)|].
    split; [exact F10|].
    split.
    { destruct HBo3 as ((_ & Hb) & _). cbn [cells_bytes cbytes app] in Hb. rewrite app_nil_r in Hb. exact Hb. }
    split; [exact (addr_sub mem3 (fr + 448) 36 (fr + 452) 6 Ao3 ltac:(lia) ltac:(lia) ltac:(lia))|].
    split; [exact Hu32|].
    apply (lt_keep g fr j regs regs' mem mem3 WT A HLT MU F9 Hr9 HA416' HAtop HWA_);
      intros x Hx; [apply Hfrout; lia | split; [apply Hfrout; lia | apply Hfrsh; [lia | intros Hc; lia]]].
Qed.

End S.
(* b8refit: applied map b8refit-v190.tsv sha256=7153b913f625df27 kinds=frame,pc,slot. Do not apply it again. *)
