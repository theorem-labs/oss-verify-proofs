(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names changed; 2169 of its 2293 lines of code are new or changed and 887 lines of the source are left out. *)
(* Segment F30 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): the range 0x82abc-0x82af4
   (slot-plan-asan-ubsan section 2 row F30, call CLS@0x82af4, twin C01), the image-B twin of image A's (v1.8)
   0x826b0-0x826e8.
     0x82abc sb zero,56(s3); 57(s3); 58(s3); 59(s3)   s3 = S(fr): the shadow bytes of fr+448 .. fr+479 are 0
     0x82acc li a0,4; sb a0,60(s3)                    the shadow byte of fr+480 .. fr+487 is 4 (4 usable bytes)
     0x82ad4 sb a0,66(s3)                             the shadow byte of fr+528 .. fr+535 is 4
     0x82ad8 ld a4,192(s1)                            [A+192] = fr+528 = v, the classify event word
     0x82adc li a0,-1; sw a0,0(a4)                    v = -1 (the C `ev = (enum)-1`)
     0x82ae4 mv a0,s2; mv a1,s4                       a0 = Phi, a1 = len
     0x82aec ld a2,264(s1); ld a3,216(s1)             [A+264] = fr+2624 = our[], [A+216] = fr+448 = o
     0x82af4 jal reac_ctrl_classify_box_frame         return point 0x82af8 (the F31 entry)
   The six shadow stores mark the 36 output bytes [fr+448, fr+484) and the 4 event bytes [fr+528, fr+532) usable,
   which is what the callee's instrumented checks of its two out-parameters need. The range has no instrumented
   check of its own and no branch to 0x82fa0 or 0x82fa4.

   The callee is composed on its lib/B contract (reac_ctrl_classify_box_frame_c.v, a Section Hypothesis). It writes
   its own stack window [sp - 8864, sp) and that window's shadow, the class-1 bytes of the side stack for frames
   (fp_w [1]), the 36 bytes at o and the 4 bytes at v. FRA moves across the six stores by Tac_slot.sl_fr_meta and
   across the call by the local f30_fra2 (the heap invariant by Contract.a_laws_fs_store, whose a_fs_ok side comes
   from the contract's own fp post for class 1 and from the untouched classes); ENT moves by Tac_slot.ent_store
   across the stores and by Tac_slot.ent_munch across the call.
   Push 5c keeps mem_inv out of FRA and out of the cuts; the stores' run lemma and the callee contract take it, so
   both run on the normalized memory (MemNorm.normalize, which has mem_inv) and MemNorm.evt_normalize carries each
   run back to the cut's memory, which has ro_agree (f30s_evt_ro, f30_cl_ro).

   Entry cut the official Inv_B82abc_at (FCUTP: LK, FTK, IFS g fr (S j), the block spill [A+312]; FCUTP's FTURN
   carries the Phi bytes and their length); exit cut the official Inv_B82af8_at. What the old local X30 bundle
   carried beyond that is derived here: the 50 frame bytes t_g from the Phi bytes (t_g is their first 50 when
   len >= 50), the frame's placement against Phi and Phi off the side stack from FRA's live block (Phi, a_size len),
   and the callee's side-stack package (fp / tls) from FRA by Tac_fsfree.fra_fp after the six stores. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse RcClassify RcClassifyLib RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_stack_malloc_c bcmp_wrap_c memcmp_c
  reac_ctrl_parse_c reac_ctrl_classify_box_frame_c reac_ctrl_classify_box_frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro.
Import ListNotations.
(* lib.Prog's RcParse chain loads lib/Reusable/YK11.v, so the short name YK11 would resolve to that copy; this
   file's registers, mkst and FPState must be image B's, as SlotInv's and Tac_slot's are. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module RP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.
Module RC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcClassify.
Module ASM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_stack_malloc_c.
Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_c.
Module MC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.memcmp_c.
Module RPC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_parse_c.
Module CL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_classify_box_frame_c.
Module CLP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_classify_box_frame.
Module BZB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.BzBridge.
Module CLU := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.reac_ctrl_classify_box_frame_c.
(* Several modules of the tree are named Frame; the one the slot's helpers (Tac_slot, Tac_fs, RcAsanFPLib) use is
   lib/Lib/Frame.v, so pin the short name to it. *)
Module Frame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module RIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.

Local Definition K30 : Z := CL.REAC_CTRL_CLASSIFY_BOX_FRAME_K.
Local Definition zb0 : byte := Z_to_bv 8 0.
Local Definition zb4 : byte := Z_to_bv 8 4.

(* ---- Pure helpers. *)

(* A one-byte store of a register writes its low byte. *)
Lemma f30_le1_byte : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. unfold le1. cbn [Z_to_le_bytes]. reflexivity. Qed.

(* The 50 bytes of a frame's record (SlotModel.t_g = fr50 of its body). *)
Lemma f30_t_g_length : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. unfold t_g. apply fr50_length. Qed.

(* bytes_at sub-range. *)
Lemma f30_ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn jj (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

(* The classify output record (the parse's 36-byte struct). *)
Lemma f30_B_length : forall inp j, length (t_B inp j) = 36%nat.
Proof. intros inp j. apply RP.ctrlparse_length. Qed.

(* A spilled word at s1 + off read at the FRA spill base A (the existential base of `spill` is A). *)
Lemma f30_spill : forall regs m off v A, spill regs m off v -> rg regs 9 A ->
  0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 -> q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA H0 H1 Hoff.
  unfold rg in HA, HA'. rewrite HA in HA'.
  pose proof Hq as (Hq0 & Hq1 & _). rewrite length_le8 in Hq1.
  assert (E : A' = A).
  { apply (f_equal bv_unsigned) in HA'. rewrite !unsigned_lit_wrap in HA'.
    rewrite (Z.mod_small A) in HA' by lia. Z.div_mod_to_equations. lia. }
  subst A'. exact Hq.
Qed.

(* ---- Model facts of the turn's frame: Phi's byte list has length len_j, and with len_j >= 50 the 50 record
   bytes t_g are its first 50 bytes. *)
Lemma f30_inb_nonneg : forall inp c, 0 <= inb inp c.
Proof. intros inp c. unfold inb, RIM.bz. apply (proj1 (bv_unsigned_in_range _ _)). Qed.

Lemma f30_fc_range : forall inp j, 0 <= fc inp j <= nlen inp.
Proof.
  intros inp j. induction j as [|j IH]; cbn [fc].
  - unfold c0, nlen. lia.
  - pose proof (f30_inb_nonneg inp (fc inp j)) as I1. pose proof (f30_inb_nonneg inp (fc inp j + 1)) as I2.
    unfold f_next, f_body, f_len, f_h, f_L, f_left, nlen in *.
    destruct (2 <=? Z.of_nat (length inp) - fc inp j); lia.
Qed.

Lemma f30_phi_len : forall inp j, Z.of_nat (length (t_phi inp j)) = t_len inp j.
Proof.
  intros inp j. pose proof (f30_fc_range inp j) as Hc.
  pose proof (f30_inb_nonneg inp (fc inp j)) as I1. pose proof (f30_inb_nonneg inp (fc inp j + 1)) as I2.
  unfold t_phi, t_len, f_phi, f_len, f_body, f_h, f_L, f_left, nlen in *.
  rewrite length_firstn, length_skipn.
  destruct (2 <=? Z.of_nat (length inp) - fc inp j); lia.
Qed.

Lemma f30_tg : forall inp j, 50 <= t_len inp j -> t_g inp j = firstn 50 (t_phi inp j).
Proof.
  intros inp j H. pose proof (f30_phi_len inp j) as HL.
  unfold t_g, fr50. rewrite firstn_app. replace (50 - length (t_phi inp j))%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. reflexivity.
Qed.

(* A byte outside a run's write set keeps its value. *)
Lemma f30_mbyte_munch : forall W m m' x, Frame.munch W m m' -> 0 <= x < 2 ^ 64 -> Frame.outside W x ->
  mbyte rsegs m' x = mbyte rsegs m x.
Proof.
  intros W m m' x MU Hx Ho. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
  rewrite MState.unsigned_lit by exact Hx. exact Ho.
Qed.

(* bytes_at moves to a memory that agrees with the old one on the bytes' own range. *)
Lemma f30_ba_eq : forall m m' a bs, bytes_at rsegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte rsegs m' x = mbyte rsegs m x) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) HK. split; [lia|]. split; [lia|].
  intros i Hi.
  assert (E : mrd rsegs m' (wa (a + Z.of_nat i)) = mrd rsegs m (wa (a + Z.of_nat i)))
    by exact (HK (a + Z.of_nat i) ltac:(lia)).
  exact (eq_trans E (H i Hi)).
Qed.

(* IFS moves to a memory that keeps the two frame records and the local `first`, [fr + 2688, fr + 2920), and in
   which `first`'s 40 bytes are addressable (Tac_ro.ifs_keep; the records are 38 and 72 bytes, Tac_ro.tr_ID_length /
   tr_FG_length). *)
Lemma f30_IFS_tr : forall g fr j regs regs' m m',
  IFS g fr j regs m ->
  (forall x, fr + 2688 <= x < fr + 2920 -> mbyte rsegs m' x = mbyte rsegs m x) ->
  addressable m' (fr + 2880) 40 ->
  IFS g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' H HK Hfst.
  apply (Tac_ro.ifs_keep g fr j regs regs' m m' H); [| | | exact Hfst].
  - intros HID. apply (f30_ba_eq _ _ _ _ HID). rewrite Tac_ro.tr_ID_length. intros x Hx. apply HK. lia.
  - intros HFG. apply (f30_ba_eq _ _ _ _ HFG). rewrite Tac_ro.tr_FG_length. intros x Hx. apply HK. lia.
  - intros a bs Ha Hl Hb. apply (f30_ba_eq _ _ _ _ Hb). intros x Hx. apply HK. lia.
Qed.

(* n bytes that are all present form a list. *)
Lemma f30_ba_present : forall m n a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> exists b, mrd rsegs m (wa (a + Z.of_nat i)) = Some b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = n.
Proof.
  intros m n. induction n as [|n IH]; intros a Ha Hn H.
  - exists []. split; [|reflexivity]. split; [exact Ha|]. split; [cbn [length Z.of_nat]; lia|].
    intros i Hi. cbn [length] in Hi. lia.
  - destruct (H 0%nat ltac:(lia)) as (b0 & Hb0).
    assert (Hrest : forall i, (i < n)%nat -> exists b, mrd rsegs m (wa (a + 1 + Z.of_nat i)) = Some b).
    { intros i Hi. destruct (H (S i) ltac:(lia)) as (b & Hb). exists b.
      replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. exact Hb. }
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) Hrest) as (bs & (Ha' & Hl' & Hb') & Hlen).
    exists (b0 :: bs). split; [|cbn [length]; lia].
    split; [exact Ha|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i].
    + cbn [nth_error]. cbn [Z.of_nat] in Hb0 |- *. rewrite Z.add_0_r in Hb0 |- *. exact Hb0.
    + cbn [nth_error]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia.
      apply Hb'. cbn [length] in Hi. lia.
Qed.

(* A present byte of a list read at its address. *)
Lemma f30_ba_some : forall m a bs i, bytes_at rsegs m a bs -> 0 <= i < Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa (a + i)) = Some b.
Proof.
  intros m a bs i (_ & _ & H) Hi.
  specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia. rewrite H.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Lemma f30_sh_off : forall fr i k, 0 <= fr -> fr mod 8 = 0 -> 8 * k <= i < 8 * k + 8 ->
  shadow_addr (fr + i) = shadow_addr fr + k.
Proof. unfold shadow_addr. intros fr i k H0 H8 Hi. Z.div_mod_to_equations. lia. Qed.

Lemma f30_in_shadow_bnd : forall x, in_shadow x -> LOWMEM_END <= x < HIGHMEM_BEG.
Proof. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG. intros; lia. Qed.

(* addressable survives writes apart from the shadow bytes of its range. *)
Lemma f30_addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) MU HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (shadow_of_app (p + i) Hap) as Hs. pose proof (in_shadow_range _ Hs) as Hbd.
  unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. apply HW. exact Hi.
Qed.

(* KNT (SlotInv, adopt 11: the kind-name table's 112 bytes at KNC.KIND_NAME = 0x9f580, image data below GT, and their
   addressability) survives writes apart from the table's bytes and their shadow bytes. *)
Lemma f30_knt_keep : forall W m m', KNT m -> munch W m m' ->
  (forall x, KNC.KIND_NAME <= x < KNC.KIND_NAME + 112 -> outside W x /\ outside W (shadow_addr x)) -> KNT m'.
Proof.
  intros W m m' (Hb & Had) MU HW.
  assert (HL : length KNC.kind_name_bytes = 112%nat) by reflexivity.
  split.
  - apply (fl_bytes W m m' KNC.KIND_NAME KNC.kind_name_bytes Hb MU).
    rewrite HL. intros x Hx. refine (proj1 (HW x _)). lia.
  - apply (f30_addr_keep W m m' _ 112 Had MU). intros i Hi. refine (proj2 (HW _ _)). lia.
Qed.

(* An addressable range built byte by byte from the shadow bytes the stores wrote. *)
Lemma f30_addr_of : forall m p n,
  0 <= p -> p + n <= APPMEM_END -> 0 <= n ->
  (forall i, 0 <= i < n -> app_mem (p + i)) ->
  (forall i, 0 <= i < n -> exists b, mrd rsegs m (wa (shadow_addr (p + i))) = Some b /\
     shadow_ok (p + i) (bv_signed b)) ->
  addressable m p n.
Proof.
  intros m p n H0 H1 H2 Hap H. split; [exact H0|]. split; [exact H2|]. split; [exact H1|].
  intros i Hi. split; [exact (Hap i Hi) | exact (H i Hi)].
Qed.

(* The one-byte cell at a shadow address, as a signed value. *)
Lemma f30_cell_byte : forall m a (b : byte), bytes_at rsegs m a [b] -> mrd rsegs m (wa a) = Some b.
Proof.
  intros m a b (_ & _ & H). pose proof (H 0%nat ltac:(cbn; lia)) as HH.
  rewrite Z.add_0_r in HH. exact HH.
Qed.

(* A C1 / CB 1 cell read as a byte. *)
Lemma f30_rw1 : forall m a (b : byte), rw_cells rsegs m a [C1 b] -> bytes_at rsegs m a [b].
Proof.
  intros m a b [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

Lemma f30_rw4 : forall m a (w : word), rw_cells rsegs m a [C4 w] -> rw_cells rsegs m a [CB 4 (le4 w)].
Proof.
  intros m a w [[_ H] HW]. split; [split|].
  - cbn [cells_wf cell_wf]. split; [apply length_le4 | exact I].
  - cbn [cells_bytes cbytes] in H |- *. exact H.
  - cbn [cells_size csize] in HW |- *. exact HW.
Qed.

(* The image segments all end below the high application memory, so no high app address is in a segment. *)
Lemma f30_seg_high : forall z, HIGHMEM_BEG <= z -> find_segment rsegs z 1 = None.
Proof.
  intros z Hz. destruct (find_segment rsegs z 1) as [s|] eqn:E; [|reflexivity].
  exfalso. destruct (kb_find_segment rsegs z 1 s E) as (Hin & _ & Hhi).
  assert (Hall : forallb (fun s0 => Z.leb (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) HIGHMEM_BEG) rsegs = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall s Hin). apply Z.leb_le in Hall. lia.
Qed.

Lemma f30_rom_high : forall x, HIGHMEM_BEG <= x -> x < 2 ^ 64 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.seg_rom rsegs (wa x) = None.
Proof.
  intros x H1 H2. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.seg_rom, memory_read.
  destruct (find_segment rsegs (bv_unsigned (wa x)) (Z.of_N 1)) as [s|] eqn:E; [|reflexivity].
  exfalso. change (Z.of_N 1) with 1 in E. unfold HIGHMEM_BEG in H1.
  rewrite (wa_unsigned x) in E by lia.
  rewrite (f30_seg_high x H1) in E. discriminate E.
Qed.

(* Above the image a readable byte is a byte of the memory map itself. *)
Lemma f30_raw_of_mrd : forall m x b, HIGHMEM_BEG <= x -> x < 2 ^ 64 ->
  mrd rsegs m (wa x) = Some b -> m (wa x) = Some b.
Proof.
  intros m x b H1 H2 H. unfold mrd in H. destruct (m (wa x)) as [b'|] eqn:E; [exact H|].
  rewrite (f30_rom_high x H1 H2) in H. discriminate H.
Qed.

(* The registered globals (FrameAPI.frame_AG) lie in [0x21140, 0xa0708), below the image top GT. *)
Lemma f30_ag_bound : forall a, in_globals AF.frame_AG a -> 0x21140 <= a < 0xa0708.
Proof.
  intros a (lo & len & Hil & Hr). unfold AF.frame_AG in Hil. cbn [In] in Hil.
  repeat (destruct Hil as [E | Hil]; [injection E as <- <-; lia |]). destruct Hil.
Qed.

(* The shadow of the whole application memory lies in [LOWMEM_END, HIGHMEM_BEG), so no application byte is in the
   shadow of an application range. *)
Lemma f30_sh_band : forall x0 x1 a, 0 <= x0 -> x1 < APPMEM_END ->
  shadow_addr x0 <= a < shadow_addr x1 -> LOWMEM_END <= a < HIGHMEM_BEG.
Proof.
  intros x0 x1 a H0 H1 Ha. unfold shadow_addr, ASAN_K in Ha.
  assert (Hlo : 0 <= x0 / 8) by (apply Z.div_pos; lia).
  assert (Hhi : x1 / 8 <= 0x100000000000).
  { apply (Z.le_trans _ ((APPMEM_END - 1) / 8)); [apply Z.div_le_mono; unfold APPMEM_END in *; lia|].
    vm_compute. discriminate. }
  unfold LOWMEM_END, HIGHMEM_BEG. lia.
Qed.

Lemma f30_sh_mono : forall x y, x <= y -> shadow_addr x <= shadow_addr y.
Proof. intros x y H. unfold shadow_addr. assert (x / 8 <= y / 8) by (apply Z.div_le_mono; lia). lia. Qed.


(* Every address at or above the shadow offset is the shadow byte of a granule. *)
Lemma f30_shadow_of : forall a, ASAN_K <= a -> a = shadow_addr (8 * (a - ASAN_K)).
Proof.
  intros a H. unfold shadow_addr. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.
(* Shadow addresses order their granules: a shadow byte inside the shadow of [a, b) belongs to a granule of
   [a - 7, b). *)
Lemma f30_sh_inv : forall a b y, shadow_addr a <= shadow_addr y < shadow_addr b -> a - 7 <= y < b.
Proof.
  intros a b y (H1 & H2). unfold shadow_addr in *. split; Z.div_mod_to_equations; lia.
Qed.

(* A frame range of writable, present bytes is a cell block. *)
Lemma f30_cells_of_stk : forall m lo hi a n,
  stk rsegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  exists bs, rw_cells rsegs m a [CB n bs].
Proof.
  intros m lo hi a n HST Hlo Hhi Ha0 Ha1.
  assert (Hpres : forall i, (i < n)%nat -> exists b, mrd rsegs m (wa (a + Z.of_nat i)) = Some b).
  { intros i Hi. destruct HST as (_ & _ & H). destruct (H (a + Z.of_nat i) ltac:(lia)) as (_ & b & Hb).
    exists b. exact Hb. }
  destruct (f30_ba_present m n a Ha0 Ha1 Hpres) as (bs & Hbs & Hlen).
  exists bs. split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact Hlen | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hbs.
  - cbn [cells_size csize]. rewrite Nat.add_0_r.
    split; [exact Ha0|]. split; [lia|].
    intros i Hi. destruct HST as (_ & _ & H). destruct (H (a + i) ltac:(lia)) as (Hv & _). exact Hv.
Qed.

(* ---- The run from 0x82abc to the callee's entry 0x837c4. *)
Lemma f30s_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A S3 V O U PHI LEN : Z) (c56 c57 c58 c59 c60 c66 : byte) (vb : list byte),
    s1v = Z_to_bv 64 A -> s3v = Z_to_bv 64 S3 -> s2v = Z_to_bv 64 PHI -> s4v = Z_to_bv 64 LEN ->
    0 <= A /\ A + 272 <= 2 ^ 64 -> 0 <= S3 /\ S3 + 67 <= 2 ^ 64 -> 0 <= V /\ V + 4 <= 2 ^ 64 ->
    0 <= O < 2 ^ 64 -> 0 <= U < 2 ^ 64 -> 0 <= PHI < 2 ^ 64 -> 0 <= LEN < 2 ^ 64 ->
    (S3 + 67 <= V \/ V + 4 <= S3) -> (S3 + 67 <= A + 192 \/ A + 272 <= S3) ->
    (V + 4 <= A + 192 \/ A + 272 <= V) ->
    rw_cells rsegs m (S3 + 56) [C1 c56] -> rw_cells rsegs m (S3 + 57) [C1 c57] ->
    rw_cells rsegs m (S3 + 58) [C1 c58] -> rw_cells rsegs m (S3 + 59) [C1 c59] ->
    rw_cells rsegs m (S3 + 60) [C1 c60] -> rw_cells rsegs m (S3 + 66) [C1 c66] ->
    rw_cells rsegs m V [CB 4 vb] -> length vb = 4%nat ->
    ro_cells rsegs m (A + 192) [C8 (Z_to_bv 64 V)] ->
    ro_cells rsegs m (A + 216) [C8 (Z_to_bv 64 O)] ->
    ro_cells rsegs m (A + 264) [C8 (Z_to_bv 64 U)] ->
    mem_inv rsegs m ->
    LE.evt rsegs
      (fun ms' => exists m',
         ms' = MS (mkR (Z_to_bv 64 0x82af8) sp gp tp t0 t1 t2 s0 s1v
                       (Z_to_bv 64 PHI) (Z_to_bv 64 LEN) (Z_to_bv 64 U) (Z_to_bv 64 O) (Z_to_bv 64 V)
                       a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x837c4) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 56, S3 + 61); (S3 + 66, S3 + 67); (V, V + 4)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         (exists vb', rw_cells rsegs m' V [CB 4 vb'] /\ length vb' = 4%nat) /\
         (exists b, mrd rsegs m' (wa (S3 + 56)) = Some b /\ bv_signed b = 0) /\
         (exists b, mrd rsegs m' (wa (S3 + 57)) = Some b /\ bv_signed b = 0) /\
         (exists b, mrd rsegs m' (wa (S3 + 58)) = Some b /\ bv_signed b = 0) /\
         (exists b, mrd rsegs m' (wa (S3 + 59)) = Some b /\ bv_signed b = 0) /\
         (exists b, mrd rsegs m' (wa (S3 + 60)) = Some b /\ bv_signed b = 4) /\
         (exists b, mrd rsegs m' (wa (S3 + 66)) = Some b /\ bv_signed b = 4))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82abc) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A S3 V O U PHI LEN c56 c57 c58 c59 c60 c66 vb -> -> -> ->
    [HA0 HA1] [HS0 HS1] [HV0 HV1] HO HU HPHI HLEN Hd1 Hd2 Hd3
    H56 H57 H58 H59 H60 H66 HV Hvb H192 H216 H264 HMI.
  pose proof (munch_refl [(S3 + 56, S3 + 61); (S3 + 66, S3 + 67); (V, V + 4)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite f30_le1_byte. mem_after_store.
  step. rewrite f30_le1_byte. mem_after_store.
  step. rewrite f30_le1_byte. mem_after_store.
  step. rewrite f30_le1_byte. mem_after_store.
  step.
  step. rewrite f30_le1_byte. mem_after_store.
  step. rewrite f30_le1_byte. mem_after_store.
  step. step. step.
  step. step. step. step. step.
  match goal with |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) => apply evt_done; exists mm end.
  split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  repeat match goal with
  | H : rw_cells rsegs ?mm ?a [C4 ?w] |- _ => apply f30_rw4 in H
  end.
  split.
  { match goal with H : rw_cells rsegs ?mm V [CB 4 ?bs] |- _ => exists bs; split; [exact H|] end.
    apply length_le4. }
  repeat match goal with
  | H : rw_cells rsegs ?mm ?a [C1 ?b] |- _ => apply f30_rw1 in H; apply f30_cell_byte in H
  end.
  repeat (split; [match goal with H : mrd rsegs _ (wa _) = Some _ |- _ =>
                    eexists; split; [exact H | vm_compute; reflexivity] end |]);
  match goal with H : mrd rsegs _ (wa _) = Some _ |- _ =>
    eexists; split; [exact H | vm_compute; reflexivity] end.
Qed.

(* ---- Normalized-memory transfer. Push 5c keeps mem_inv out of FRA and out of the cuts: a cut carries ro_agree
   alone. The stores' run lemma f30s_evt and the callee contract take mem_inv, so each runs on `normalize rsegs m`
   (mem_inv_normalize) and MemNorm.evt_normalize carries the run back to m, leaving `mem_rel` and `ro_same` to move
   the facts across. No image segment reaches the image top AC.GT, so no byte at or above it is read-only; every
   byte the two runs write (the frame, the frame's shadow, the side stack, the callee's window and its shadow) is
   at or above it. (Seg/F13.v and Seg/Tac_ro.v carry the same moves for their own premises.) *)
Lemma f30_segs_below_GT : BZB.seg_tops_below rsegs AC.GT = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f30_ro_hi : forall a, AC.GT <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha.
  assert (Hu : bv_unsigned (wa a) = a) by (rewrite wa_unsigned by (unfold AC.GT in Ha; lia); reflexivity).
  unfold ro_addr.
  destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [s|] eqn:E; [|reflexivity].
  exfalso.
  destruct (BZB.find_segment_below rsegs AC.GT (bv_unsigned (wa a)) 1 s f30_segs_below_GT E ltac:(lia))
    as [L|L]; [rewrite Hu in L; unfold AC.GT in *; lia | lia].
Qed.

Lemma f30_rwc_norm : forall m a cs, ro_agree rsegs m -> rw_cells rsegs m a cs ->
  AC.GT <= a -> a + Z.of_nat (cells_size cs) <= 2 ^ 64 -> rw_cells rsegs (normalize rsegs m) a cs.
Proof.
  intros m a cs HR ((Hwf & Hb) & Hw) H1 H2. split; [split; [exact Hwf|]|].
  - apply bytes_at_normalize; assumption.
  - eapply wr_at_norm; [apply mem_rel_normalize; exact HR | exact Hw |].
    intros i Hi. apply f30_ro_hi. lia.
Qed.

Lemma f30_roc_norm : forall m a cs, ro_agree rsegs m -> ro_cells rsegs m a cs ->
  ro_cells rsegs (normalize rsegs m) a cs.
Proof.
  intros m a cs HR (Hwf & Hb). split; [exact Hwf|]. apply bytes_at_normalize; assumption.
Qed.

Lemma f30_rwc_back : forall m m0 a cs, mem_rel rsegs m m0 -> rw_cells rsegs m0 a cs -> rw_cells rsegs m a cs.
Proof.
  intros m m0 a cs HR ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
  - exact (proj2 (bytes_at_rel rsegs m m0 a _ HR) Hb).
  - exact (wr_at_rel rsegs m m0 a _ HR Hw).
Qed.

Lemma f30_stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi REL (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as (Hv & b & Hb).
  pose proof (ro_false_of_wview rsegs m m0 (wa a) REL Hv) as RO. split.
  - rewrite <- (wview_rel_rw rsegs m m0 _ REL RO). exact Hv.
  - exists b. rewrite (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

(* Above the image top, the stack facts hold on both memories alike. *)
Lemma f30_stk_iff : forall m m0 lo hi, mem_rel rsegs m m0 -> AC.GT <= lo -> hi <= 2 ^ 64 ->
  (stk rsegs m lo hi <-> stk rsegs m0 lo hi).
Proof.
  intros m m0 lo hi REL H1 H2. split; [|exact (f30_stk_back m m0 lo hi REL)].
  intros (S1 & S2 & H). split; [exact S1|]. split; [exact S2|]. intros a Ha.
  destruct (H a Ha) as (Hv & b & Hb). pose proof (f30_ro_hi a ltac:(lia)) as RO. split.
  - rewrite (wview_rel_rw rsegs m m0 _ REL RO). exact Hv.
  - exists b. rewrite <- (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma f30_addr_back : forall m m0 p n, mem_rel rsegs m m0 -> addressable m0 p n -> addressable m p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite (mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Lemma f30_acells_back : forall m m0, mem_rel rsegs m m0 -> asan_cells m0 -> asan_cells m.
Proof.
  intros m m0 R H. unfold asan_cells in H |- *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs => exact (proj2 (bytes_at_rel rsegs m m0 a bs R) ltac:(assumption)) end.
Qed.

Lemma f30_shrw_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 HR H a Ha.
  assert (RO : ro_addr rsegs (wa a) = false).
  { apply f30_ro_hi. pose proof Ha as Ha'.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha'.
    unfold AC.GT. lia. }
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (wview_rel_rw rsegs m m0 _ HR RO). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 _ HR). exact Hb.
Qed.

(* The thread cells, the side stack's state (fp) and the callee's thread-cell premise are byte facts (and the side
   stack's stk above AC.GT), so they hold on both memories alike. *)
Lemma f30_tlsc_iff : forall m m0 TP DT TS C T DB k, mem_rel rsegs m m0 ->
  (ASM.asan_tls_cells m TP DT TS C T DB k <-> ASM.asan_tls_cells m0 TP DT TS C T DB k).
Proof.
  intros m m0 TP DT TS C T DB k HR.
  assert (E : forall a bs, bytes_at rsegs m a bs <-> bytes_at rsegs m0 a bs)
    by (intros a bs; exact (bytes_at_rel rsegs m m0 a bs HR)).
  unfold ASM.asan_tls_cells. setoid_rewrite E. reflexivity.
Qed.

Lemma f30_tls_iff : forall m m0 TP FS lo hi, mem_rel rsegs m m0 ->
  (CL.reac_ctrl_classify_box_frame_tls m TP FS lo hi <-> CL.reac_ctrl_classify_box_frame_tls m0 TP FS lo hi).
Proof.
  intros m m0 TP FS lo hi HR. unfold CL.reac_ctrl_classify_box_frame_tls.
  split; intros H DT TS C T DB k Hc; apply H; apply (f30_tlsc_iff m m0 TP DT TS C T DB k HR); exact Hc.
Qed.

Lemma f30_fp_iff : forall cs m m0 TP FS lo hi W D, mem_rel rsegs m m0 ->
  (fp cs m TP FS lo hi W D <-> fp cs m0 TP FS lo hi W D).
Proof.
  intros cs m m0 TP FS lo hi W D HR.
  assert (E : forall a bs, bytes_at rsegs m a bs <-> bytes_at rsegs m0 a bs)
    by (intros a bs; exact (bytes_at_rel rsegs m m0 a bs HR)).
  assert (Ec : forall c, fp_cls m FS c <-> fp_cls m0 FS c).
  { intros c. unfold fp_cls. setoid_rewrite E. reflexivity. }
  assert (Ep : ASM.fs_place m FS <-> ASM.fs_place m0 FS).
  { unfold ASM.fs_place.
    split; intros (P1 & P2 & P3 & P4 & P5); (split; [exact P1|]); (split; [exact P2|]); (split; [exact P3|]);
      (split; [exact P4|]);
      (assert (Ht : FS + ASM.FS_SIZE <= 2 ^ 64)
         by (pose proof (P4 (FS + ASM.FS_SIZE - 1) ltac:(unfold ASM.FS_SIZE; lia)) as Ha;
             unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha; unfold ASM.FS_SIZE in *; lia));
      (assert (Hg : AC.GT <= FS) by (unfold ASM.ASAN_GT, AC.GT in *; lia)).
    - exact (proj1 (f30_stk_iff m m0 FS (FS + ASM.FS_SIZE) HR Hg Ht) P5).
    - exact (proj2 (f30_stk_iff m m0 FS (FS + ASM.FS_SIZE) HR Hg Ht) P5). }
  unfold fp. split; intros (DT & TS & C & T & DB & k & H1 & H2 & H3 & H4 & H5 & H6 & H7);
    exists DT, TS, C, T, DB, k.
  - split; [exact (proj1 (f30_tlsc_iff m m0 TP DT TS C T DB k HR) H1)|].
    split; [exact (proj1 (E _ _) H2)|]. split; [exact (proj1 Ep H3)|].
    split; [exact (proj1 (E _ _) H4)|]. split; [exact (proj1 (E _ _) H5)|].
    split; [|exact H7].
    rewrite Forall_forall in H6 |- *. intros c Hc. exact (proj1 (Ec c) (H6 c Hc)).
  - split; [exact (proj2 (f30_tlsc_iff m m0 TP DT TS C T DB k HR) H1)|].
    split; [exact (proj2 (E _ _) H2)|]. split; [exact (proj2 Ep H3)|].
    split; [exact (proj2 (E _ _) H4)|]. split; [exact (proj2 (E _ _) H5)|].
    split; [|exact H7].
    rewrite Forall_forall in H6 |- *. intros c Hc. exact (proj2 (Ec c) (H6 c Hc)).
Qed.

(* addressable from its one-byte pieces, and a piece of an addressable range. *)
Lemma f30_addr_join : forall m p n, 0 <= p -> 0 <= n -> p + n <= APPMEM_END ->
  (forall i, 0 <= i < n -> addressable m (p + i) 1) -> addressable m p n.
Proof.
  intros m p n H0 H1 H2 H. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (_ & _ & _ & Ha). destruct (Ha 0 ltac:(lia)) as (Hap & Hb).
  rewrite Z.add_0_r in Hap, Hb. split; [exact Hap | exact Hb].
Qed.

Lemma f30_addr_sub : forall m p n q k, addressable m p n -> p <= q -> q + k <= p + n -> 0 <= k ->
  addressable m q k.
Proof.
  intros m p n q k (H0 & H1 & H2 & H) Hq Hk Hk0. split; [lia|]. split; [exact Hk0|]. split; [lia|].
  intros i Hi. replace (q + i) with (p + (q - p + i)) by lia. apply H. lia.
Qed.

(* Below an 8-aligned bound, the shadow byte is below the bound's. *)
Lemma f30_sh_lt : forall a b, 0 <= a -> b mod 8 = 0 -> a < b -> shadow_addr a < shadow_addr b.
Proof. unfold shadow_addr. intros a b H0 H8 H. Z.div_mod_to_equations. lia. Qed.

(* f30s_evt on the cut's own memory: ro_agree in place of mem_inv (the run is taken on the normalized memory and
   MemNorm.evt_normalize carries it back). *)
Lemma f30s_evt_ro :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A S3 V O U PHI LEN : Z) (c56 c57 c58 c59 c60 c66 : byte) (vb : list byte),
    s1v = Z_to_bv 64 A -> s3v = Z_to_bv 64 S3 -> s2v = Z_to_bv 64 PHI -> s4v = Z_to_bv 64 LEN ->
    0 <= A /\ A + 272 <= 2 ^ 64 -> 0 <= S3 /\ S3 + 67 <= 2 ^ 64 -> 0 <= V /\ V + 4 <= 2 ^ 64 ->
    0 <= O < 2 ^ 64 -> 0 <= U < 2 ^ 64 -> 0 <= PHI < 2 ^ 64 -> 0 <= LEN < 2 ^ 64 ->
    (S3 + 67 <= V \/ V + 4 <= S3) -> (S3 + 67 <= A + 192 \/ A + 272 <= S3) ->
    (V + 4 <= A + 192 \/ A + 272 <= V) ->
    rw_cells rsegs m (S3 + 56) [C1 c56] -> rw_cells rsegs m (S3 + 57) [C1 c57] ->
    rw_cells rsegs m (S3 + 58) [C1 c58] -> rw_cells rsegs m (S3 + 59) [C1 c59] ->
    rw_cells rsegs m (S3 + 60) [C1 c60] -> rw_cells rsegs m (S3 + 66) [C1 c66] ->
    rw_cells rsegs m V [CB 4 vb] -> length vb = 4%nat ->
    ro_cells rsegs m (A + 192) [C8 (Z_to_bv 64 V)] ->
    ro_cells rsegs m (A + 216) [C8 (Z_to_bv 64 O)] ->
    ro_cells rsegs m (A + 264) [C8 (Z_to_bv 64 U)] ->
    ro_agree rsegs m -> LOWMEM_END <= S3 -> AC.GT <= V ->
    LE.evt rsegs
      (fun ms' => exists m',
         ms' = MS (mkR (Z_to_bv 64 0x82af8) sp gp tp t0 t1 t2 s0 s1v
                       (Z_to_bv 64 PHI) (Z_to_bv 64 LEN) (Z_to_bv 64 U) (Z_to_bv 64 O) (Z_to_bv 64 V)
                       a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x837c4) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 56, S3 + 61); (S3 + 66, S3 + 67); (V, V + 4)] m m' /\
         wmono rsegs m m' /\ ro_agree rsegs m' /\
         (exists vb', rw_cells rsegs m' V [CB 4 vb'] /\ length vb' = 4%nat) /\
         (exists b, mrd rsegs m' (wa (S3 + 56)) = Some b /\ bv_signed b = 0) /\
         (exists b, mrd rsegs m' (wa (S3 + 57)) = Some b /\ bv_signed b = 0) /\
         (exists b, mrd rsegs m' (wa (S3 + 58)) = Some b /\ bv_signed b = 0) /\
         (exists b, mrd rsegs m' (wa (S3 + 59)) = Some b /\ bv_signed b = 0) /\
         (exists b, mrd rsegs m' (wa (S3 + 60)) = Some b /\ bv_signed b = 4) /\
         (exists b, mrd rsegs m' (wa (S3 + 66)) = Some b /\ bv_signed b = 4))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82abc) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A S3 V O U PHI LEN c56 c57 c58 c59 c60 c66 vb E1 E3 E2 E4
    HA HS HV HO HU HPHI HLEN Hd1 Hd2 Hd3 H56 H57 H58 H59 H60 H66 HVc Hvb H192 H216 H264 HRO HS3 HVg.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (HS3g : AC.GT <= S3) by (unfold LOWMEM_END, AC.GT in *; lia).
  pose proof (f30s_evt ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 Fr fc (normalize rsegs m) A S3 V O U PHI LEN c56 c57 c58 c59 c60 c66 vb E1 E3 E2 E4
    HA HS HV HO HU HPHI HLEN Hd1 Hd2 Hd3
    (f30_rwc_norm m _ _ HRO H56 ltac:(lia) ltac:(cbn; lia)) (f30_rwc_norm m _ _ HRO H57 ltac:(lia) ltac:(cbn; lia))
    (f30_rwc_norm m _ _ HRO H58 ltac:(lia) ltac:(cbn; lia)) (f30_rwc_norm m _ _ HRO H59 ltac:(lia) ltac:(cbn; lia))
    (f30_rwc_norm m _ _ HRO H60 ltac:(lia) ltac:(cbn; lia)) (f30_rwc_norm m _ _ HRO H66 ltac:(lia) ltac:(cbn; lia))
    (f30_rwc_norm m _ _ HRO HVc HVg ltac:(cbn; lia)) Hvb
    (f30_roc_norm m _ _ HRO H192) (f30_roc_norm m _ _ HRO H216) (f30_roc_norm m _ _ HRO H264)
    (mem_inv_normalize rsegs m)) as HC.
  pose proof (evt_normalize rsegs _ _ _ _ _ _ m (seg_rom rsegs) ltac:(vm_compute; reflexivity) HRO HC) as HN.
  eapply LE.evt_mono; [exact HN|].
  intros ms (s0' & (m0' & E & MU & WM & MI' & (vb' & Hv' & Hvl') & B56 & B57 & B58 & B59 & B60 & B66) &
             Hrel & Hros).
  subst s0'.
  destruct ms as [regsX frX pcX svcX rvX fcX memX romX].
  destruct Hrel as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmr).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmr, Hros.
  subst regsX frX pcX svcX rvX fcX romX.
  exists memX. split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) memX m0' REL Hmr Hros MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) memX m0' REL Hmr Hros WM)|].
  split; [exact (ro_agree_of_mem_rel rsegs memX m0' Hmr)|].
  split; [exists vb'; split; [exact (f30_rwc_back memX m0' _ _ Hmr Hv') | exact Hvl']|].
  repeat match goal with
  | H : exists b, mrd rsegs m0' ?a = Some b /\ _ |- _ =>
      let b := fresh "b" in let Hb := fresh "Hb" in let Hs := fresh "Hs" in
      destruct H as (b & Hb & Hs); rewrite <- (mrd_rel rsegs memX m0' a Hmr) in Hb
  end.
  repeat (split; [eexists; split; eassumption|]).
  eexists; split; eassumption.
Qed.

Section F30.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The callee (reac_ctrl_classify_box_frame 0x837c4): it parses the 50 frame bytes into the 36-byte record at o,
   classifies it against our[] at u, writes the event word at v and returns cl_r of the classification. It writes
   only o, v, its stack window [sp - 8864, sp) with that window's shadow, and the class-1 bytes of the side stack
   for frames. *)
Hypothesis HCL : CL.reac_ctrl_classify_box_frame_contract.

Local Notation STKLO mem md := (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md).

(* The allocator laws as this file reads them: through SlotInv's LawFields lemmas (lw_blocks, lw_fs_place, lw_store,
   lw_fs_ok), and a_laws_fs_store, which has none, through f30_fs_store below; no generated law is taken apart by
   position at a use. a_laws_blocks: a live block lies at or above 4096 and ends below stklo, and its bytes are app
   memory off the side stack (lwb_byte's per-byte list taken apart once, here). *)
Lemma f30_blocks : forall H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  4096 <= p /\ p + n <= STKLO mem md /\ (forall a, p <= a < p + n -> app_mem a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md p n HAH Hin.
  pose proof (lw_blocks (APIf rc) H mem md p n HAH Hin) as HB.
  split; [exact (lwb_low _ _ _ _ _ _ HB)|]. split; [exact (lwb_end _ _ _ _ _ _ HB)|].
  intros a Ha. destruct (lwb_byte _ _ _ _ _ _ HB a Ha) as (Hap & _ & _ & _ & Hnfs). split; [exact Hap | exact Hnfs].
Qed.

(* a_laws_fs_store (no LawFields lemma), read by statement: a store outside the allocator's store set, the side
   stack and the side stack's shadow, after which a_fs_ok holds, keeps the heap invariant, the owned set and the two
   stack bounds, given as SlotInv's record lw_sto (the record of a_laws_store's lw_store). *)
Lemma f30_fs_store : forall H mem mem' md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (STKLO mem md) a -> ~ (FS <= a < FS + AC.FS_SIZE) ->
     ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.a_fs_ok mem' FS ->
  lw_sto (APIf rc) H mem mem' md.
Proof.
  intros H mem mem' md FS HAH Hw HFS HC HW Hok.
  decompose [and] (AC.a_laws_fs_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                     H mem mem' md FS HAH Hw HFS HC HW Hok).
  constructor; assumption.
Qed.

(* The callee contract on a memory with ro_agree in place of mem_inv: the call runs on the normalized memory
   (mem_inv_normalize), the premises move there by the mem_rel transfer lemmas, and MemNorm.evt_normalize carries
   the run back; the post's facts come back across mem_rel / ro_same. o and v are at or above AC.GT, so their cells
   are not read-only and keep their writability under normalize. *)
Lemma f30_cl_ro :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n u o v S FS : Z)
         (fr us junk vb : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 u -> a3 = Z_to_bv 64 o -> a4 = Z_to_bv 64 v ->
    sp = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= u < 2^64 -> 0 <= o < 2^64 -> 0 <= v < 2^64 -> S < 2^64 ->
    S mod 16 = 0 ->
    K30 <= S -> stk rsegs m (S - K30) S ->
    length fr = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fr /\ (f + 50 <= S - K30 \/ S <= f)) ->
    o <> 0 -> o mod 4 = 0 -> o + 36 <= 2^64 -> rw_cells rsegs m o [CB 36 junk] ->
    (o + 36 <= S - K30 \/ S <= o) ->
    (50 <= n -> o + 36 <= f \/ f + 50 <= o) -> (o + 36 <= u \/ u + 6 <= o) ->
    length us = 6%nat ->
    (50 <= n -> u + 6 <= 2^64 /\ bytes_at rsegs m u us /\ (u + 6 <= S - K30 \/ S <= u)) ->
    v <> 0 -> v mod 4 = 0 -> v + 4 <= 2^64 -> rw_cells rsegs m v [CB 4 vb] ->
    (v + 4 <= S - K30 \/ S <= v) ->
    (v + 4 <= o \/ o + 36 <= v) -> (v + 4 <= f \/ f + 50 <= v) -> (v + 4 <= u \/ u + 6 <= v) ->
    ro_agree rsegs m -> AC.GT <= o -> AC.GT <= v ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - K30 -> S <= APPMEM_END ->
    addressable m (S - K30) K30 ->
    (50 <= n -> addressable m f 50 /\ addressable m u 6 /\ app_mem (u + 6) /\ app_mem (u + 7)) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= ASM.GOT_CF \/ ASM.CF + 256 <= o) ->
    addressable m v 4 -> (v + 4 <= RT_LO \/ RT_HI <= v) ->
    addressable m RPC.REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m BW.REAL_BCMP (le8 (wa BW.BCMP)) -> bytes_at rsegs m BW.REAL_MEMCMP (le8 (wa MC.MEMCMP)) ->
    bytes_at rsegs m ASM.GOT_CF (le8 (wa ASM.CF)) ->
    bytes_at rsegs m (ASM.CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (ASM.CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - K30) S (CL.reac_ctrl_classify_box_frame_W o v S)
      (CL.reac_ctrl_classify_box_frame_D f n u o v) ->
    CL.reac_ctrl_classify_box_frame_tls m (bv_unsigned tp) FS (S - K30) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra0 sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (RC.cl_r (RC.classify n fr us)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra0) fc None m' (seg_rom rsegs) /\
         Frame.munch ([(o, o + 36); (v, v + 4); (S - K30, S)] ++ fp_w [1%nat] FS ++
                      [(shadow_addr (S - K30), shadow_addr S)]) m m' /\
         Frame.wmono rsegs m m' /\ ro_agree rsegs m' /\
         stk rsegs m' (S - K30) S /\
         rw_cells rsegs m' o [CB 36 (snd (RP.ctrlparse n fr))] /\
         rw_cells rsegs m' v [CB 4 (CLU.reac_ctrl_classify_box_frame_ev (RC.classify n fr us) vb)] /\
         asan_cells m' /\ shadow_rw m' /\
         addressable m' (S - K30) K30 /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - K30) S
           (CL.reac_ctrl_classify_box_frame_W o v S) (CL.reac_ctrl_classify_box_frame_D f n u o v) /\
         CL.reac_ctrl_classify_box_frame_tls m' (bv_unsigned tp) FS (S - K30) S)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CL.REAC_CTRL_CLASSIFY_BOX_FRAME) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m f n u o v S FS fr us junk vb Ea0 Ea1 Ea2 Ea3 Ea4 Esp Hf Hn Hu Ho Hv HS HS16 HKS Hstk Hfrl Hf50
    Ho0 Ho4 Ho36 Hoc Hodj Hof Hou Husl Hu50 Hv0 Hv4 Hv64 Hvc Hvdj Hvo Hvf Hvu HRO Hogt Hvgt HAC HSW
    HShi HSap Had Had50 Hado Hoapp Hocf Hadv Hvrt HadBC HRB HRM HGC HC254 HC255 HFP HTLS.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  pose proof HCL as HC. unfold CL.reac_ctrl_classify_box_frame_contract in HC.
  assert (HK : K30 = 8864) by reflexivity.
  eapply LE.evt_mono.
  { eapply (evt_normalize rsegs); [vm_compute; reflexivity | exact HRO |].
    eapply (HC ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc (normalize rsegs m) f n u o v S FS fr us junk vb).
    - exact Ea0.
    - exact Ea1.
    - exact Ea2.
    - exact Ea3.
    - exact Ea4.
    - exact Esp.
    - exact Hf.
    - exact Hn.
    - exact Hu.
    - exact Ho.
    - exact Hv.
    - exact HS.
    - exact HS16.
    - exact HKS.
    - exact (Tac_ro.stk_rel m (normalize rsegs m) (S - K30) S REL
               ltac:(unfold LOWMEM_END, HIGHMEM_BEG in *; lia) ltac:(unfold APPMEM_END in *; lia) Hstk).
    - exact Hfrl.
    - intros H50. destruct (Hf50 H50) as (P1 & P2 & P3 & P4).
      split; [exact P1|]. split; [exact P2|]. split; [exact (Tac_ro.ba_rel m _ _ _ REL P3) | exact P4].
    - exact Ho0.
    - exact Ho4.
    - exact Ho36.
    - exact (f30_rwc_norm m o _ HRO Hoc Hogt ltac:(cbn; lia)).
    - exact Hodj.
    - exact Hof.
    - exact Hou.
    - exact Husl.
    - intros H50. destruct (Hu50 H50) as (P1 & P2 & P3).
      split; [exact P1|]. split; [exact (Tac_ro.ba_rel m _ _ _ REL P2) | exact P3].
    - exact Hv0.
    - exact Hv4.
    - exact Hv64.
    - exact (f30_rwc_norm m v _ HRO Hvc Hvgt ltac:(cbn; lia)).
    - exact Hvdj.
    - exact Hvo.
    - exact Hvf.
    - exact Hvu.
    - exact (mem_inv_normalize rsegs m).
    - exact (Tac_ro.asan_cells_rel m _ REL HAC).
    - exact (Tac_ro.shadow_rw_rel m _ REL HSW).
    - exact HShi.
    - exact HSap.
    - exact (Tac_ro.addressable_rel m _ _ _ REL Had).
    - intros H50. destruct (Had50 H50) as (P1 & P2 & P3 & P4).
      split; [exact (Tac_ro.addressable_rel m _ _ _ REL P1)|].
      split; [exact (Tac_ro.addressable_rel m _ _ _ REL P2)|]. split; assumption.
    - exact (Tac_ro.addressable_rel m _ _ _ REL Hado).
    - exact Hoapp.
    - exact Hocf.
    - exact (Tac_ro.addressable_rel m _ _ _ REL Hadv).
    - exact Hvrt.
    - exact (Tac_ro.addressable_rel m _ _ _ REL HadBC).
    - exact (Tac_ro.ba_rel m _ _ _ REL HRB).
    - exact (Tac_ro.ba_rel m _ _ _ REL HRM).
    - exact (Tac_ro.ba_rel m _ _ _ REL HGC).
    - exact (Tac_ro.ba_rel m _ _ _ REL HC254).
    - exact (Tac_ro.ba_rel m _ _ _ REL HC255).
    - exact (proj1 (f30_fp_iff _ m _ _ _ _ _ _ _ REL) HFP).
    - exact (proj1 (f30_tls_iff m _ _ _ _ _ REL) HTLS). }
  intros ms (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
              E & MU & WM & MI & ST & HO & HV & AC0 & SW & AW & FP & TL) & Hrel & Hros).
  subst s0'.
  destruct ms as [regsX frX pcX svcX rvX fcX memX romX].
  destruct Hrel as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmr).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmr, Hros.
  subst regsX frX pcX svcX rvX fcX romX.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', memX.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) memX m0' REL Hmr Hros MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) memX m0' REL Hmr Hros WM)|].
  split; [exact (ro_agree_of_mem_rel rsegs memX m0' Hmr)|].
  split; [exact (f30_stk_back memX m0' _ _ Hmr ST)|].
  split; [exact (f30_rwc_back memX m0' _ _ Hmr HO)|].
  split; [exact (f30_rwc_back memX m0' _ _ Hmr HV)|].
  split; [exact (f30_acells_back memX m0' Hmr AC0)|].
  split; [exact (f30_shrw_back memX m0' Hmr SW)|].
  split; [exact (f30_addr_back memX m0' _ _ Hmr AW)|].
  split; [exact (proj2 (f30_fp_iff _ memX m0' _ _ _ _ _ _ Hmr) FP)|].
  exact (proj2 (f30_tls_iff memX m0' _ _ _ _ Hmr) TL).
Qed.

(* Lib-evt -> SR bridge (as Seg/F31.v's sl_run_lib): the one place of this file that uses the lazy-model lemma
   AsanLift.evt_SR_canon_lazy. seg_F30 uses it for its one run 0x82abc -> 0x82af8 (the six stores and the classify
   call). The run reads [s1+192, s1+200), [s1+216, s1+224), [s1+264, s1+272), the 50 bytes at Phi, the 6 bytes at
   fr+2624 and their shadow bytes, the runtime cells of the callee's bcmp wrapper and its side-stack cells; it writes
   the shadow bytes S(fr)+56 .. S(fr)+60 and S(fr)+66, the 36 bytes at fr+448, the 4 bytes at fr+528, the callee's
   window [sp - 8864, sp) with that window's shadow and the class-1 bytes of the side stack (fp_w [1] FS). *)
Lemma f30_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

(* The runtime cells the callee's bcmp wrapper reads, from the FRA runtime invariant (as F31's bcmp_cells). *)
Lemma f30_cells : forall sp mem md, AsanRTInv.RT sp mem md ->
  asan_cells mem /\ shadow_rw mem /\
  bytes_at rsegs mem BW.REAL_BCMP (le8 (wa BW.BCMP)) /\
  bytes_at rsegs mem BW.REAL_MEMCMP (le8 (wa MC.MEMCMP)) /\
  bytes_at rsegs mem ASM.GOT_CF (le8 (wa ASM.CF)) /\
  bytes_at rsegs mem (ASM.CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs mem (ASM.CF + 255) [Z_to_bv 8 1].
Proof.
  intros sp mem md HRT.
  destruct HRT as (HAC0 & HSW0 & _ & HCF0 & _ & HREAL0 & _).
  destruct HCF0 as (HGOTCF & _ & _ & _ & _ & _ & HCF240 & _).
  split; [exact HAC0|]. split; [exact HSW0|].
  split; [apply (real_cell_of mem BW.REAL_BCMP BW.BCMP HREAL0); vm_compute; reflexivity|].
  split; [apply (real_cell_of mem BW.REAL_MEMCMP MC.MEMCMP HREAL0); vm_compute; reflexivity|].
  split; [exact HGOTCF|].
  split.
  { pose proof (f30_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 14 1 HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 14) with (ASM.CF + 254) in Hs by (unfold ASM.CF, RT_CF; lia).
    replace (firstn 1 (skipn 14 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  { pose proof (f30_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 15 1 HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 15) with (ASM.CF + 255) in Hs by (unfold ASM.CF, RT_CF; lia).
    replace (firstn 1 (skipn 15 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
Qed.

(* The frame's place (plan FP.1 / FP.2), as image A's F29 fra_loc: the side stack FS is the word at tp, below the
   real stack; the frame is on the real stack (at or above stklo) or is the class-6 frame inside FS (FRA's side
   arm: FS + 6328320 <= fr), and is application memory at or above the image top GT. *)
Lemma f30_fra_loc : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  exists FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS /\ 0 <= FS < 2 ^ 64 /\
    AC.GT <= FS /\ FS + AC.FS_SIZE <= STKLO mem md /\ (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a) /\
    HIGHMEM_BEG <= STKLO mem md /\
    0 <= fr /\ AC.GT <= fr /\ (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) /\
    ((STKLO mem md <= fr /\ fr + FRAME_BYTES <= APPMEM_END) \/
     (FS + 6328320 <= fr /\ fr + FRAME_BYTES <= FS + AC.FS_SIZE)).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md HFRA.
  pose proof HFRA as HF2.
  destruct HF2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof Hwin as (Hw0 & Hw1 & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (RT_fs_cells _ _ _ HRT) as (_ & _ & _ & _ & (FSw & HFSw & HFok) & _).
  pose proof (bv_unsigned_in_range 64 FSw) as HFSr. change (bv_modulus 64) with (2 ^ 64) in HFSr.
  assert (Hwm : word_mem rsegs mem (AC.as_tp AC.ASYMS) (bv_unsigned FSw)).
  { change (AC.as_tp AC.ASYMS) with RT_TP. exact (bytes_at_le8_word rsegs mem RT_TP FSw HFSw). }
  destruct (lw_fs_place (APIf rc) _ mem md (bv_unsigned FSw) HAH Hwm HFSr) as [HGT HFSlo _ HFSapp].
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hhi.
  pose proof Hhdr1 as (Hfr0 & Hfr8 & _). rewrite length_le8 in Hfr8. change (Z.of_nat 8) with 8 in Hfr8.
  exists (bv_unsigned FSw).
  split; [exact Hwm|]. split; [exact HFSr|].
  split; [exact HGT|]. split; [exact HFSlo|]. split; [exact HFSapp|]. split; [exact Hhi|].
  split; [exact Hfr0|].
  destruct Hloc as [[_ [_ Hreal]] | [_ [Hfsb [Hfs _]]]].
  - pose proof (Hreal fr ltac:(lia)) as R1. pose proof (Hreal (fr + FRAME_BYTES - 1) ltac:(lia)) as R2.
    split; [unfold AC.GT, HIGHMEM_BEG in *; lia|].
    split; [intros a Ha; pose proof (Hreal a Ha); unfold app_mem; right; lia|].
    left. lia.
  - pose proof (Hfsb (bv_unsigned FSw) Hwm HFSr) as HFSfr.
    assert (Hin : forall a, fr <= a < fr + FRAME_BYTES -> bv_unsigned FSw <= a < bv_unsigned FSw + AC.FS_SIZE).
    { intros a Ha. destruct (Hfs a Ha) as (b & Hbr & Hb & Hab).
      assert (Eb : b = bv_unsigned FSw).
      { change (AC.as_tp AC.ASYMS) with RT_TP in Hb.
        pose proof (word_mem_le8 rsegs mem RT_TP b Hb ltac:(lia) ltac:(unfold RT_TP; lia)
                      ltac:(unfold RT_TP; lia)) as H8.
        pose proof (fl_le8_eq [] mem mem RT_TP _ _ H8 HFSw (munch_refl [] mem) (fun _ _ => I)) as E.
        apply (f_equal bv_unsigned) in E. rewrite unsigned_lit in E by lia. exact E. }
      subst b. exact Hab. }
    pose proof (Hin fr ltac:(lia)) as F1. pose proof (Hin (fr + FRAME_BYTES - 1) ltac:(lia)) as F2.
    split; [unfold AC.GT, AC.FS_SIZE in *; lia|].
    split; [intros a Ha; apply HFSapp; apply Hin; exact Ha|].
    right. lia.
Qed.

(* FRA moves across the six stores (the frame's shadow bytes S(fr)+56 .. S(fr)+66 and the event word at fr+528):
   Tac_slot.sl_fr_meta, with the heap invariant from Contract.a_laws_store (real-stack arm: every written byte is
   a frame byte or the shadow byte of a frame granule, both a_store_ok) or Contract.a_laws_fs_store with
   Tac_fs.a_fs_ok_pres (side-stack arm: the frame lies above the FakeStack's metadata). ENT moves by
   Tac_slot.ent_store (every written byte is a frame byte or a byte of the frame's shadow), with its stack bounds
   and ownership half from the same law. *)
Lemma f30_fra1 : forall g fr hb regs mem mem' md,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  Frame.munch [(Sfr fr + 56, Sfr fr + 67); (fr + 528, fr + 532)] mem mem' ->
  Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  (forall a, 0 <= a < 2 ^ 64 -> (exists b, mbyte rsegs mem a = Some b) ->
     (exists b, mbyte rsegs mem' a = Some b)) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  (forall x, fr + 528 <= x < fr + 532 -> exists b, mrd rsegs mem' (wa x) = Some b) ->
  FRA B APIf ra g fr hb regs mem' md /\ ENT APIf g hb mem' md /\
  STKLO mem' md = STKLO mem md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem mem' md HFRA HENT MU WM HroM PM Hshnew Hpres.
  destruct (f30_fra_loc g fr hb regs mem md HFRA) as
    (FS & Hwm & HFSr & HGTFS & HFSlo & HFSapp & Hhi & Hfr0 & HGTfr & Happ & Hloc2).
  pose proof HFRA as HF2.
  destruct HF2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFSsz : AC.FS_SIZE = 11571200) by reflexivity.
  assert (Hfr8 : fr mod 8 = 0) by (clear -Hfrm; Z.div_mod_to_equations; lia).
  assert (Hub : fr + FRAME_BYTES <= APPMEM_END).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Happ; lia).
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha |- *. destruct Ha; lia. }
  (* the shadow bytes the stores touch are the shadow bytes of the frame granules [fr+448, fr+536) *)
  assert (HWsh : forall k, 56 <= k <= 66 -> Sfr fr + k = shadow_addr (fr + 8 * k) /\ in_shadow (Sfr fr + k)).
  { intros k Hk.
    assert (E : shadow_addr (fr + 8 * k) = Sfr fr + k) by (apply (f30_sh_off fr (8 * k) k); lia).
    split; [symmetry; exact E | rewrite <- E; apply shadow_of_app; apply Happ; lia]. }
  (* an application byte outside [fr+528, fr+532) is outside the write set *)
  assert (HWapp : forall a, app_mem a -> ~ (fr + 528 <= a < fr + 532) ->
                    Frame.outside [(Sfr fr + 56, Sfr fr + 67); (fr + 528, fr + 532)] a).
  { intros a Ha Hn. cbn [Frame.outside]. split; [|split; [exact Hn | exact I]].
    intros [H1 H2]. destruct (HWsh (a - Sfr fr) ltac:(lia)) as (_ & Hin).
    replace (Sfr fr + (a - Sfr fr)) with a in Hin by lia. exact (app_not_shadow a Ha Hin). }
  (* a shadow byte outside [S(fr)+56, S(fr)+67) is outside the write set *)
  assert (HWsho : forall a, in_shadow a -> ~ (Sfr fr + 56 <= a < Sfr fr + 67) ->
                    Frame.outside [(Sfr fr + 56, Sfr fr + 67); (fr + 528, fr + 532)] a).
  { intros a Ha Hn. cbn [Frame.outside]. split; [exact Hn|]. split; [|exact I].
    intros [H1 H2]. exact (app_not_shadow a (Happ a ltac:(lia)) Ha). }
  assert (HWM : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  assert (HD : rt_disjoint [(Sfr fr + 56, Sfr fr + 67); (fr + 528, fr + 532)]).
  { assert (HSfr : 0x7fff8000 <= Sfr fr)
      by (unfold Sfr, shadow_addr, ASAN_K; assert (0 <= fr / 8) by (apply Z.div_pos; lia); lia).
    unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
      RT_AGLOB_LEN in *.
    unfold AC.GT in HGTfr. cbn [disjoint_from].
    repeat split; first [left; lia | exact I]. }
  (* AH, stklo / stkhi and the runtime's ownership across the write *)
  assert (HAHS : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
                 STKLO mem' md = STKLO mem md /\
                 AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
                 AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                 (forall a, AC.a_in_img a ->
                    AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a ->
                    AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a)).
  { destruct Hloc2 as [[Hreal _] | [Hfs1 Hfs2]].
    - assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
        ~ AC.a_store_ok (hb ++ g_H g) (STKLO mem md) a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
      { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
        cbn [Frame.outside]. split; [|split; [|exact I]].
        - intros Hc. apply Hns. destruct (HWsh (a - Sfr fr) ltac:(lia)) as (E & _).
          unfold AC.a_store_ok. right; right; right. exists (fr + 8 * (a - Sfr fr)).
          split; [replace (Sfr fr + (a - Sfr fr)) with a in E by lia; exact E|].
          right; left. lia.
        - intros Hc. apply Hns. unfold AC.a_store_ok. right; left. lia. }
      destruct (lw_store (APIf rc) (hb ++ g_H g) mem mem' md HAH HstoreC HWM) as [HAH' Hown HSTK HSTKHI].
      split; [exact HAH'|]. split; [exact HSTK|]. split; [exact HSTKHI|].
      intros a _ Ho. exact (proj2 (Hown a) Ho).
    - assert (Hmeta : forall q, Tac_fs.fs_meta FS q ->
                Frame.outside [(Sfr fr + 56, Sfr fr + 67); (fr + 528, fr + 532)] q).
      { intros q Hq. pose proof (Tac_fs.fs_meta_below FS q Hq) as Hb.
        assert (Hq0 : FS <= q).
        { unfold Tac_fs.fs_meta in Hq.
          destruct Hq as [H | [H | [[c [Hc Hr]] | [c [jj [Hc [Hj Heq]]]]]]].
          - lia. - lia. - unfold AC.a_fs_hint in Hr; lia.
          - subst q. pose proof (Tac_fs.a_fs_flag_range FS c jj Hc Hj). lia. }
        apply HWapp; [apply HFSapp; lia | lia]. }
      assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
        ~ AC.a_store_ok (hb ++ g_H g) (STKLO mem md) a -> ~ (FS <= a < FS + AC.FS_SIZE) ->
        ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
        mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
      { intros a Ha Hns Hnf Hnsh. apply MU. rewrite MState.unsigned_lit by lia.
        cbn [Frame.outside]. split; [|split; [|exact I]].
        - intros Hc. apply Hnsh. destruct (HWsh (a - Sfr fr) ltac:(lia)) as (E & _).
          exists (fr + 8 * (a - Sfr fr)). split; [unfold AC.FS_SIZE in *; lia|].
          replace (Sfr fr + (a - Sfr fr)) with a in E by lia. exact E.
        - intros Hc. apply Hnf. unfold AC.FS_SIZE in *. lia. }
      assert (Hfsok : AC.a_fs_ok mem' FS).
      { refine (Tac_fs.a_fs_ok_pres _ mem mem' FS _ MU HWM PM Hmeta ltac:(lia)
                  ltac:(unfold AC.FS_SIZE, APPMEM_END in *; lia)).
        exact (lw_fs_ok (APIf rc) (hb ++ g_H g) mem md FS HAH Hwm HFSr). }
      destruct (f30_fs_store (hb ++ g_H g) mem mem' md FS HAH Hwm HFSr HstoreC HWM Hfsok)
        as [HAH' Hown HSTK HSTKHI].
      split; [exact HAH'|]. split; [exact HSTK|]. split; [exact HSTKHI|].
      intros a _ Ho. exact (proj2 (Hown a) Ho). }
  destruct HAHS as (HAH' & HSTK & HSTKHI & Hown).
  split.
  2: { split; [|exact HSTK].
       eapply ent_store with (W := [(Sfr fr + 56, Sfr fr + 67); (fr + 528, fr + 532)]) (fr := fr) (regs := regs);
         [exact HENT | exact HFRA | exact MU | | exact HSTK | exact HSTKHI | exact Hown].
       intros x Hx.
       destruct (Z_le_gt_dec (Sfr fr) x) as [L1|L1]; [destruct (Z_lt_ge_dec x (Sfr fr + FRAME_SHADOW)) as [L2|L2]|];
         [right; right; right; lia | |];
         (destruct (Z_le_gt_dec fr x) as [M1|M1]; [destruct (Z_lt_ge_dec x (fr + FRAME_BYTES)) as [M2|M2]|];
          [right; right; left; lia
          | left; cbn [Frame.outside]; split; [lia | split; [lia | exact I]]
          | left; cbn [Frame.outside]; split; [lia | split; [lia | exact I]]]). }
  apply (sl_fr_meta B APIf ra empty FF g fr hb regs regs mem mem' md
           [(Sfr fr + 56, Sfr fr + 67); (fr + 528, fr + 532)] HFRA MU WM HroM HD HAH' HSTK Happ HGTfr Hshnew);
    try reflexivity.
  - intros x Hx0 Hx1 Hx2. cbn [Frame.outside]. split; [lia|]. split; [lia | exact I].
  - intros A' HA' HA'r x Hx.
    assert (EA : A' = A).
    { unfold rg in Hr9. rewrite Hr9 in HA'. apply (f_equal bv_unsigned) in HA'.
      pose proof Hwin as (Hw0 & Hw1 & Hwv).
      rewrite !unsigned_lit in HA' by lia. lia. }
    subst A'. apply HWapp; [|lia].
    pose proof Hwin as (Hw0 & Hw1 & Hwv). unfold app_mem. right.
    unfold AF.SLOT_STACK in *. unfold APPMEM_END, HIGHMEM_BEG in *. lia.
  - intros x Hx. apply HWapp; [|pose proof Hwin as (Hw0 & Hw1 & Hwv);
      unfold AF.SLOT_STACK in *; lia].
    pose proof Hwin as (Hw0 & Hw1 & Hwv). unfold app_mem. right.
    unfold AF.SLOT_STACK, APPMEM_END, HIGHMEM_BEG in *. lia.
  - intros A' HA' HA'r x Hx.
    assert (EA : A' = A).
    { unfold rg in Hr9. rewrite Hr9 in HA'. apply (f_equal bv_unsigned) in HA'.
      pose proof Hwin as (Hw0 & Hw1 & Hwv).
      rewrite !unsigned_lit in HA' by lia. lia. }
    subst A'. apply HWapp; [|lia].
    pose proof Hwin as (Hw0 & Hw1 & Hwv). unfold app_mem. right.
    unfold AF.SLOT_STACK in *. unfold APPMEM_END, HIGHMEM_BEG in *. lia.
  - intros x Hx. pose proof Hwin as (Hw0 & Hw1 & Hwv).
    destruct (Z_le_gt_dec (fr + 528) x) as [M1|M1]; [destruct (Z_lt_ge_dec x (fr + 532)) as [M2|M2]|].
    + right. destruct (Hpres x ltac:(lia)) as (b & Hb). exists b.
      apply (f30_raw_of_mrd mem' x b); [unfold AF.SLOT_STACK in *; lia | lia | exact Hb].
    + left. apply HWapp; [|lia]. unfold app_mem. right.
      unfold AF.SLOT_STACK, APPMEM_END, HIGHMEM_BEG in *. lia.
    + left. apply HWapp; [|lia]. unfold app_mem. right.
      unfold AF.SLOT_STACK, APPMEM_END, HIGHMEM_BEG in *. lia.
  - intros a Hin. refine (f30_addr_keep _ mem mem' a 1 (HAG a Hin) MU _).
    intros i Hi. replace (a + i) with a by lia.
    pose proof (f30_ag_bound a Hin) as Hab.
    assert (Hsa : shadow_addr a < Sfr fr).
    { assert (Ha8 : a / 8 <= 657160 / 8) by (apply Z.div_le_mono; lia).
      assert (Hf8 : 6283264 / 8 <= fr / 8) by (apply Z.div_le_mono; [lia | unfold AC.GT in HGTfr; lia]).
      change (657160 / 8) with 82145 in Ha8. change (6283264 / 8) with 785408 in Hf8.
      unfold Sfr, shadow_addr. lia. }
    cbn [Frame.outside]. split; [lia|]. split; [|exact I].
    intros [H1 H2]. apply (app_not_shadow (shadow_addr a)).
    * apply Happ. lia.
    * apply shadow_of_app. unfold app_mem, LOWMEM_END. left. lia.
Qed.

(* The side stack's base word is unique. *)
Lemma f30_tp_uniq : forall m FS FS', word_mem rsegs m (AC.as_tp AC.ASYMS) FS ->
  word_mem rsegs m (AC.as_tp AC.ASYMS) FS' -> 0 <= FS < 2 ^ 64 -> 0 <= FS' < 2 ^ 64 -> FS = FS'.
Proof.
  intros m FS FS' H1 H2 R1 R2.
  change (AC.as_tp AC.ASYMS) with RT_TP in H1, H2.
  pose proof (word_mem_le8 rsegs m RT_TP FS H1 R1 ltac:(unfold RT_TP; lia) ltac:(unfold RT_TP; lia)) as A1.
  pose proof (word_mem_le8 rsegs m RT_TP FS' H2 R2 ltac:(unfold RT_TP; lia) ltac:(unfold RT_TP; lia)) as A2.
  pose proof (fl_le8_eq [] m m RT_TP _ _ A1 A2 (munch_refl [] m) (fun _ _ => I)) as E.
  apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. exact E.
Qed.

(* The side stack fp names is the one at the tp word. *)
Lemma f30_fp_FS : forall cs m FS FS' lo hi W D,
  fp cs m (AC.as_tp AC.ASYMS) FS' lo hi W D -> word_mem rsegs m (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  lo <= 2 ^ 64 -> FS' = FS.
Proof.
  intros cs m FS FS' lo hi W D (DT & TS & C & T & DB & k & _ & Hb & (Hp0 & _) & _ & _ & _ & Hlo & _) Hwm HFS Hlo2.
  pose proof (bytes_at_le8_word rsegs m _ _ Hb) as Hw.
  assert (HFS' : 0 <= FS' < 2 ^ 64) by (unfold ASM.FS_SIZE in Hlo; lia).
  rewrite unsigned_lit in Hw by lia.
  symmetry. exact (f30_tp_uniq m FS FS' Hwm Hw HFS HFS').
Qed.

(* The class-1 ranges of the side stack, as plain intervals. *)
Lemma f30_fpw1 : forall FS,
  fp_w [1%nat] FS = [(FS + 8, FS + 8 + 8); (FS + 20480, FS + 20480 + 8192);
                     (FS + 1085440, FS + 2134016);
                     (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016))].
Proof.
  intros FS. cbn [fp_w fp_w1 flat_map app].
  assert (Eh : ASM.fs_hint FS 1%nat = FS + 8) by (unfold ASM.fs_hint; cbn [Z.of_nat]; lia).
  assert (Ef : ASM.fs_flag FS 1%nat 0 = FS + 20480).
  { unfold ASM.fs_flag. change (Z.of_nat 1%nat) with 1. change (2 ^ 15) with 32768.
    change (2 ^ (15 - 1)) with 16384. lia. }
  assert (EM : ASM.fs_M 1%nat = 8192).
  { unfold ASM.fs_M. change (Z.of_nat 1%nat) with 1. change (2 ^ (14 - 1)) with 8192. reflexivity. }
  assert (E0 : ASM.fs_frame FS 1%nat 0 = FS + 1085440).
  { unfold ASM.fs_frame, ASM.fs_B. change (Z.of_nat 1%nat) with 1. change (2 ^ 20) with 1048576. lia. }
  assert (E1 : ASM.fs_frame FS 1%nat (ASM.fs_M 1%nat) = FS + 2134016).
  { unfold ASM.fs_frame, ASM.fs_B. rewrite EM. change (Z.of_nat 1%nat) with 1.
    change (2 ^ 20) with 1048576. change (2 ^ 1) with 2. lia. }
  rewrite Eh, Ef, E1, E0, EM. reflexivity.
Qed.

(* FRA moves across the callee's run. Its write set is the two out-parameters (the 36 bytes at o = fr+448 and the
   event word at v = fr+528), its own stack window [sp - K30, sp) with that window's shadow, and the class-1 bytes
   of the side stack for frames. RT comes from AsanRTInv.RT_meta_write (the write set is apart from the runtime's
   own cells and every shadow byte is readable again: the callee's post carries shadow_rw); the heap invariant from
   Contract.a_laws_fs_store (every written byte is a_store_ok, a side-stack byte or the shadow of one), whose
   a_fs_ok side the callee's post carries. The side arm's frame record FSREC (the tp word, the class-6 flag byte
   and the slot's last word) is apart from every written range; the slot window stays addressable outside the frame
   (the callee's window by its post, the rest because its shadow is apart from the callee's). Every other conjunct
   of FRA reads bytes the run did not touch. ENT moves by Tac_slot.ent_munch: no entry block, image byte, byte at
   or above S or shadow byte of those is written. *)
Lemma f30_fra2 : forall g fr hb regs regs' mem mem' md FS,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> FS + 6328320 <= fr ->
  Frame.munch ([(fr + 448, fr + 484); (fr + 528, fr + 532);
                (AC.aspZ regs - K30, AC.aspZ regs)] ++ fp_w [1%nat] FS ++
               [(shadow_addr (AC.aspZ regs - K30), shadow_addr (AC.aspZ regs))]) mem mem' ->
  Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' -> shadow_rw mem' ->
  AC.a_fs_ok mem' FS ->
  stk rsegs mem' (AC.aspZ regs - K30) (AC.aspZ regs) ->
  addressable mem' (AC.aspZ regs - K30) K30 ->
  (forall x, fr + 448 <= x < fr + 484 -> exists b, mrd rsegs mem' (wa x) = Some b) ->
  (forall x, fr + 528 <= x < fr + 532 -> exists b, mrd rsegs mem' (wa x) = Some b) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md /\ ENT APIf g hb mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md FS HFRA HENT Hwm HFSr HFSfr MU WM HroM HSW Hfsok HSTKw HAWc Hpo Hpv
    E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct (f30_fra_loc g fr hb regs mem md HFRA) as
    (FS2 & Hwm2 & HFS2r & HGTFS & HFSlo & HFSapp & Hhi & Hfr0 & HGTfr & Happ & Hloc2).
  assert (EFS : FS2 = FS) by (apply (f30_tp_uniq mem); assumption).
  subst FS2.
  destruct (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hdisj & HfrA & _ & _).
  destruct (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & _).
  pose proof HFRA as HF2.
  destruct HF2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFSsz : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HK : K30 = 8864) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  pose proof Hwin as (Hw0 & Hw1 & Hwv).
  rewrite Haspz in MU, HSTKw, HAWc, Hwlo.
  pose proof (Hdisj K30 ltac:(unfold FN_STACK, AF.SLOT_STACK, K30, CL.REAC_CTRL_CLASSIFY_BOX_FRAME_K; lia))
    as Hfrsp. rewrite Haspz in Hfrsp.
  assert (Hub : fr + FRAME_BYTES <= APPMEM_END).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Happ; lia).
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha |- *. destruct Ha; lia. }
  assert (Hsphi : HIGHMEM_BEG <= sp - K30) by (unfold AF.SLOT_STACK, K30,
    CL.REAC_CTRL_CLASSIFY_BOX_FRAME_K in *; lia).
  assert (Hspapp : forall a, sp - K30 <= a < sp -> app_mem a)
    by (intros a Ha; unfold app_mem; right; unfold APPMEM_END in *; lia).
  rewrite (f30_fpw1 FS) in MU. cbn [app] in MU.
  set (Wc := [(fr + 448, fr + 484); (fr + 528, fr + 532); (sp - K30, sp);
              (FS + 8, FS + 8 + 8); (FS + 20480, FS + 20480 + 8192); (FS + 1085440, FS + 2134016);
              (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016));
              (shadow_addr (sp - K30), shadow_addr sp)]) in MU.
  (* an application byte away from the four application ranges of the write set is outside it *)
  assert (HWout : forall a, app_mem a -> ~ (fr + 448 <= a < fr + 484) -> ~ (fr + 528 <= a < fr + 532) ->
                    ~ (sp - K30 <= a < sp) -> (a < FS + 8 \/ FS + 2134016 <= a) -> Frame.outside Wc a).
  { intros a Ha H1 H2 H3 H4. subst Wc. cbn [Frame.outside].
    assert (HnotSh : forall x0 x1, 0 <= x0 -> x1 < APPMEM_END -> ~ (shadow_addr x0 <= a < shadow_addr x1)).
    { intros x0 x1 Hx0 Hx1 Hc. pose proof (f30_sh_band x0 x1 a Hx0 Hx1 Hc) as Hb.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
    assert (HFSa : FS + 2134016 < APPMEM_END).
    { assert (Hx : app_mem (FS + 2134016)) by (apply HFSapp; unfold AC.FS_SIZE in *; lia).
      unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hx. lia. }
    repeat split; try exact I; try lia.
    - apply HnotSh; lia.
    - apply (HnotSh (sp - K30) sp); unfold APPMEM_END in *; lia. }
  (* a shadow byte away from the two shadow ranges of the write set is outside it *)
  assert (HWsho : forall a, in_shadow a ->
                    ~ (shadow_addr (FS + 1085440) <= a < shadow_addr (FS + 2134016)) ->
                    ~ (shadow_addr (sp - K30) <= a < shadow_addr sp) -> Frame.outside Wc a).
  { intros a Ha H1 H2. subst Wc. cbn [Frame.outside].
    repeat split; try exact I; try lia;
      try (intros Hc; apply (app_not_shadow a); [|exact Ha]).
    - apply Happ; lia.
    - apply Happ; lia.
    - apply Hspapp; lia.
    - apply HFSapp; unfold AC.FS_SIZE in *; lia.
    - apply HFSapp; unfold AC.FS_SIZE in *; lia.
    - apply HFSapp; unfold AC.FS_SIZE in *; lia. }
  (* everything below the image top is untouched *)
  assert (HWlow : forall x, 0 <= x < AC.GT -> Frame.outside Wc x).
  { intros x Hx. apply HWout.
    - unfold app_mem, LOWMEM_END, AC.GT in *. left. lia.
    - unfold AC.GT in *. lia.
    - unfold AC.GT in *. lia.
    - unfold AC.GT in *. lia.
    - left. unfold AC.GT in *. lia. }
  (* a side-stack byte away from the class-1 ranges and from the two out-parameters is outside it *)
  assert (HWfs : forall x, FS <= x < FS + AC.FS_SIZE ->
                   ~ (FS + 8 <= x < FS + 16) -> ~ (FS + 20480 <= x < FS + 28672) ->
                   ~ (FS + 1085440 <= x < FS + 2134016) ->
                   ~ (fr + 448 <= x < fr + 484) -> ~ (fr + 528 <= x < fr + 532) -> Frame.outside Wc x).
  { intros x Hx H1 H2 H3 H4 H5. subst Wc. cbn [Frame.outside].
    assert (Hax : app_mem x) by (apply HFSapp; exact Hx).
    assert (HnotSh : forall x0 x1, 0 <= x0 -> x1 < APPMEM_END -> ~ (shadow_addr x0 <= x < shadow_addr x1)).
    { intros x0 x1 Hx0 Hx1 Hc. pose proof (f30_sh_band x0 x1 x Hx0 Hx1 Hc) as Hb.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
    assert (HFSa : FS + 2134016 < APPMEM_END).
    { assert (Hx2 : app_mem (FS + 2134016)) by (apply HFSapp; unfold AC.FS_SIZE in *; lia).
      unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hx2. lia. }
    split; [exact H4|]. split; [exact H5|].
    split; [rewrite HFSsz in *; rewrite HFN in Hwlo; lia|].
    split; [lia|]. split; [lia|]. split; [exact H3|].
    split; [apply (HnotSh (FS + 1085440) (FS + 2134016)); lia|].
    split; [apply (HnotSh (sp - K30) sp); unfold APPMEM_END in *; lia | exact I]. }
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by (unfold AC.GT in *; lia).
      apply HWlow. unfold AC.GT. lia. }
    unfold mbyte. rewrite Hm. reflexivity. }
  assert (HWM : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  assert (HD : rt_disjoint Wc).
  { assert (HSsp : LOWMEM_END <= shadow_addr (sp - K30))
      by (unfold shadow_addr, ASAN_K, LOWMEM_END; assert (0 <= (sp - K30) / 8) by (apply Z.div_pos; lia); lia).
    assert (HSfs : LOWMEM_END <= shadow_addr (FS + 1085440))
      by (unfold shadow_addr, ASAN_K, LOWMEM_END; assert (0 <= (FS + 1085440) / 8) by (apply Z.div_pos; lia); lia).
    subst Wc. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
      RT_AGLOB_LEN in *.
    unfold AC.GT, LOWMEM_END, HIGHMEM_BEG in *. cbn [disjoint_from].
    repeat split; first [left; lia | exact I]. }
  (* the heap invariant, the stack bounds and the runtime's ownership *)
  assert (HAHS : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
                 AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
                 AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                 AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
                 AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                 (forall a, AC.a_in_img a ->
                    AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a ->
                    AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a)).
  { assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      ~ (FS <= a < FS + AC.FS_SIZE) ->
      ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns Hnf Hnsh. apply MU. rewrite MState.unsigned_lit by lia.
      assert (Hfrok : forall x, fr <= x < fr + FRAME_BYTES -> AC.a_store_ok (hb ++ g_H g)
                        (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) x \/ FS <= x < FS + AC.FS_SIZE).
      { intros x Hx. destruct Hloc2 as [[Hreal _] | [_ Hfs2]].
        - left. unfold AC.a_store_ok. right; left. unfold APPMEM_END in *. lia.
        - right. unfold AC.FS_SIZE in *. lia. }
      subst Wc. cbn [Frame.outside].
      split; [intros Hc; destruct (Hfrok a ltac:(lia)) as [Hok|Hin];
                [exact (Hns Hok) | exact (Hnf Hin)]|].
      split; [intros Hc; destruct (Hfrok a ltac:(lia)) as [Hok|Hin];
                [exact (Hns Hok) | exact (Hnf Hin)]|].
      split; [intros Hc; apply Hns; unfold AC.a_store_ok; right; left; unfold APPMEM_END in *; lia|].
      split; [intros Hc; apply Hnf; unfold AC.FS_SIZE in *; lia|].
      split; [intros Hc; apply Hnf; unfold AC.FS_SIZE in *; lia|].
      split; [intros Hc; apply Hnf; unfold AC.FS_SIZE in *; lia|].
      split.
      { intros Hc. apply Hnsh. exists (8 * (a - ASAN_K)).
        assert (Hb1 : 8 * ((FS + 1085440) / 8) <= 8 * (a - ASAN_K)).
        { unfold shadow_addr in Hc. lia. }
        assert (Hb2 : 8 * (a - ASAN_K) < 8 * ((FS + 2134016) / 8) + 8).
        { unfold shadow_addr in Hc. lia. }
        assert (Hd1 : (FS + 1085440) - 7 <= 8 * ((FS + 1085440) / 8))
          by (clear -HFSr; Z.div_mod_to_equations; lia).
        assert (Hd2 : 8 * ((FS + 2134016) / 8) <= FS + 2134016)
          by (clear -HFSr; Z.div_mod_to_equations; lia).
        split; [unfold AC.FS_SIZE in *; lia|].
        apply f30_shadow_of. unfold shadow_addr, ASAN_K in *.
        assert (0 <= (FS + 1085440) / 8) by (apply Z.div_pos; lia). lia. }
      split; [|exact I].
      { intros Hc. apply Hns. unfold AC.a_store_ok. right; right; right.
        exists (8 * (a - ASAN_K)).
        assert (Hb1 : 8 * ((sp - K30) / 8) <= 8 * (a - ASAN_K)) by (unfold shadow_addr in Hc; lia).
        assert (Hb2 : 8 * (a - ASAN_K) < 8 * (sp / 8) + 8) by (unfold shadow_addr in Hc; lia).
        assert (Hd1 : (sp - K30) - 7 <= 8 * ((sp - K30) / 8))
          by (clear -Hsphi; unfold HIGHMEM_BEG in Hsphi; Z.div_mod_to_equations; lia).
        assert (Hd2 : 8 * (sp / 8) <= sp) by (clear -Hsphi; unfold HIGHMEM_BEG in Hsphi;
          unfold K30, CL.REAC_CTRL_CLASSIFY_BOX_FRAME_K in Hsphi; Z.div_mod_to_equations; lia).
        split.
        - apply f30_shadow_of. unfold shadow_addr, ASAN_K in *.
          assert (0 <= (sp - K30) / 8) by (apply Z.div_pos; unfold HIGHMEM_BEG in Hsphi; lia). lia.
        - right; left. unfold APPMEM_END, K30, CL.REAC_CTRL_CLASSIFY_BOX_FRAME_K in *. lia. } }
    destruct (f30_fs_store (hb ++ g_H g) mem mem' md FS HAH Hwm HFSr HstoreC HWM Hfsok)
      as [HAH' Hown HSTK HSTKHI].
    split; [exact HAH'|]. split; [exact HSTK|]. split; [exact HSTKHI|].
    intros a _ Ho. exact (proj2 (Hown a) Ho). }
  destruct HAHS as (HAH' & HSTK & HSTKHI & Hown).
  (* the frame's own 392 shadow bytes are untouched *)
  assert (HshOut : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> Frame.outside Wc x).
  { intros x Hx.
    assert (Hin : in_shadow x).
    { assert (E : shadow_addr (fr + 8 * (x - Sfr fr)) = Sfr fr + (x - Sfr fr))
        by (apply (f30_sh_off fr (8 * (x - Sfr fr)) (x - Sfr fr));
            [lia | clear -Hfrm; Z.div_mod_to_equations; lia | lia]).
      replace x with (shadow_addr (fr + 8 * (x - Sfr fr))) by (rewrite E; lia).
      apply shadow_of_app. apply Happ. lia. }
    apply HWsho; [exact Hin | |].
    - pose proof (f30_sh_mono (FS + 2134016) fr ltac:(lia)) as Hm1. unfold Sfr in *. lia.
    - destruct Hloc2 as [[Hreal _] | [_ Hfs2]].
      + assert (Esp : shadow_addr sp = Sfr fr).
        { destruct Hloc as [[_ [Hspfr _]] | [_ [_ [Hfs3 _]]]]; [unfold Sfr; rewrite Hspfr; reflexivity|].
          exfalso. pose proof (Hfs3 fr ltac:(lia)) as Hc.
          destruct Hc as (b & Hbr & Hb & Hab).
          assert (b = FS) by (apply (f30_tp_uniq mem); assumption). subst b.
          unfold AC.FS_SIZE in *. lia. }
        rewrite Esp. lia.
      + assert (Hm2 : Sfr fr + FRAME_SHADOW <= shadow_addr (sp - K30)).
        { assert (E392 : shadow_addr (fr + FRAME_BYTES) = Sfr fr + FRAME_SHADOW)
            by (apply (f30_sh_off fr FRAME_BYTES FRAME_SHADOW);
                [lia | clear -Hfrm; Z.div_mod_to_equations; lia | lia]).
          pose proof (f30_sh_mono (fr + FRAME_BYTES) (sp - K30) ltac:(lia)) as Hm3. lia. }
        lia. }
  split.
  2: { (* ENT: no entry block, image byte, byte at or above S, or shadow byte of those is written (ent_kept's five
          cases; the fifth is the shadow of an entry block byte) *)
       eapply ent_munch with (W := Wc); [exact HENT | exact HAH | exact MU | | exact HSTK | exact HSTKHI | exact Hown].
       intros x Hk. destruct Hk as [Hblkk | [Hik | [Habk | [(b & Hor & ->) | Hblks]]]].
       - destruct Hblkk as (q & k & i & Hin & Hni & Hi & ->).
         assert (Hin' : In (q, k) (hb ++ g_H g)) by (apply in_or_app; right; exact Hin).
         destruct (f30_blocks (hb ++ g_H g) mem md q k HAH Hin') as (_ & Hend & Hall).
         destruct (Hall (q + i) ltac:(lia)) as (Happq & Hnfs).
         assert (HnFS : ~ (FS <= q + i < FS + AC.FS_SIZE))
           by (intros Hc; apply Hnfs; exists FS; split; [lia | split; [exact Hwm | exact Hc]]).
         assert (Hnfr : ~ (fr <= q + i < fr + FRAME_BYTES)).
         { intros Hc. destruct Hloc2 as [[Hreal _] | [Hfs1 Hfs2]]; [lia | apply HnFS; lia]. }
         apply HWout; [exact Happq | lia | lia | rewrite HFN in Hwlo; lia | lia].
       - pose proof (img_below_GT x Hik) as Hxg. apply HWlow. exact Hxg.
       - apply HWout; [unfold app_mem; right; unfold HIGHMEM_BEG, APPMEM_END in *; lia | lia | lia | lia | right; lia].
       - assert (Hb0 : 0 <= b /\ (b < AC.GT \/ g_S g <= b))
           by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) | ]; lia).
         assert (Happb : app_mem b).
         { destruct Hor as [Hi|Hr];
             [pose proof (img_below_GT b Hi) as X; unfold AC.GT, app_mem, LOWMEM_END in *; left; lia
             |unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; right; lia]. }
         apply HWsho; [exact (shadow_of_app b Happb) | |].
         + intros Hc. pose proof (f30_sh_inv (FS + 1085440) (FS + 2134016) b Hc) as Hbb.
           unfold AC.GT in *. lia.
         + intros Hc. pose proof (f30_sh_inv (sp - K30) sp b Hc) as Hbb.
           unfold AC.GT, HIGHMEM_BEG in *. lia.
       - (* the shadow byte of an entry block byte: the block is app memory below stklo (below the callee's
            window) and off the side stack, so its shadow is off the two shadow ranges of the write set *)
         destruct Hblks as (q & k & i & Hin & Hni & Hi & ->).
         assert (Hin' : In (q, k) (hb ++ g_H g)) by (apply in_or_app; right; exact Hin).
         destruct (f30_blocks (hb ++ g_H g) mem md q k HAH Hin') as (_ & Hend & Hall).
         destruct (Hall (q + i) ltac:(lia)) as (Happq & Hnfs).
         assert (HnFS : ~ (FS <= q + i < FS + AC.FS_SIZE))
           by (intros Hc; apply Hnfs; exists FS; split; [lia | split; [exact Hwm | exact Hc]]).
         apply HWsho; [exact (shadow_of_app (q + i) Happq) | |].
         + intros Hc. pose proof (f30_sh_inv (FS + 1085440) (FS + 2134016) (q + i) Hc) as Hb. apply HnFS. lia.
         + intros Hc. pose proof (f30_sh_inv (sp - K30) sp (q + i) Hc) as Hb. rewrite HFN in Hwlo. lia. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md Wc HRT MU WM HD
                   (fun a Ha => proj2 (HSW a Ha)))|].
  split; [exact HAH'|].
  split; [exact HroM|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo; [lia | rewrite Hthr in Hx; cbn in Hx; lia].
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo; [lia | rewrite Hlock in Hx; cbn in Hx; lia].
    - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia]. }
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
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA448|].
  split; [exact HS4|].
  split; [exact HAPP|].
  (* the spill of the frame base and of the selector, in [A, A + 448) above sp *)
  assert (HAout : forall x, A <= x < A + 448 -> Frame.outside Wc x).
  { intros x Hx. apply HWout.
    - unfold app_mem. right. unfold APPMEM_END, HIGHMEM_BEG in *. lia.
    - lia. - lia. - lia.
    - right. unfold AC.FS_SIZE in *. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. apply HAout. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. apply HAout. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr40 | exact MU |].
    rewrite length_le8. intros x Hx. apply HAout. lia. }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0' [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0'|]. split; [|split].
      + intros FS' Hw HFS'r. apply (Hfsb FS'); [| exact HFS'r].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + intros a Ha. destruct (Hfs a Ha) as (FSb & HFSbr & Hw & Hlo & Hhi2).
        exists FSb. split; [exact HFSbr|]. split; [|split; [exact Hlo | exact Hhi2]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + (* the frame record: the tp word (low image), the class-6 flag byte FS + 36352 + j and the slot's last
           word fr + 4088, both inside FS and apart from the class-1 ranges and the out-parameters *)
        destruct Hrec as (FSr & jr & Htpr & HFSrr & Hjr & Hfrr & Hflag & Htail).
        assert (EFSr : FSr = FS) by (apply (f30_tp_uniq mem); assumption). subst FSr.
        assert (HB6 : ASM.fs_B 6 = 4096) by reflexivity.
        assert (HM6 : ASM.fs_M 6 = 256) by reflexivity.
        assert (Hfl : ASM.fs_flag FS 6 jr = FS + 36352 + jr) by (unfold ASM.fs_flag; cbn; lia).
        assert (Hfrv : fr = FS + 6328320 + jr * 4096)
          by (rewrite Hfrr; unfold ASM.fs_frame, ASM.fs_B; cbn; lia).
        exists FS, jr.
        split.
        { intros k Hk. rewrite KBlo.
          - exact (Htpr k Hk).
          - unfold AC.as_tp, AC.ASYMS. cbn. lia.
          - unfold AC.as_tp, AC.ASYMS. cbn. lia. }
        split; [exact HFSrr|]. split; [exact Hjr|]. split; [exact Hfrr|].
        rewrite HM6 in Hjr.
        split.
        { eapply fl_bytes; [exact Hflag | exact MU |]. cbn [length]. intros x Hx.
          apply HWfs; lia. }
        { eapply fl_bytes; [exact Htail | exact MU |]. rewrite length_le8. intros x Hx.
          rewrite HB6 in Hx. apply HWfs; lia. } }
  (* the frame header words, below the two written frame ranges *)
  assert (Hhdrout : forall x, fr <= x < fr + 24 -> Frame.outside Wc x).
  { intros x Hx. apply HWout.
    - apply Happ. lia.
    - lia. - lia.
    - destruct Hloc as [[_ [Hspfr _]] | _]; [lia | lia].
    - right. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply Hhdrout. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply Hhdrout. lia. }
  split.
  { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
    eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen, Z2Nat.id by lia. intros x Hx. apply HshOut. lia. }
  split.
  { eapply (Frame.stk_transport rsegs Wc mem mem' (g_S g - AF.SLOT_STACK) (g_S g));
      [exact Hwin | exact MU | exact WM |].
    intros x Hx.
    assert (Hxhi : HIGHMEM_BEG <= x) by (unfold AF.SLOT_STACK in *; lia).
    destruct (Z_le_gt_dec (sp - K30) x) as [M1|M1]; [destruct (Z_lt_ge_dec x sp) as [M2|M2]|].
    - right. destruct HSTKw as (_ & _ & HW2). destruct (HW2 x ltac:(lia)) as (_ & b & Hb).
      exists b. apply (f30_raw_of_mrd mem' x b); [lia | lia | exact Hb].
    - destruct (Z_le_gt_dec (fr + 448) x) as [N1|N1]; [destruct (Z_lt_ge_dec x (fr + 484)) as [N2|N2]|].
      + right. destruct (Hpo x ltac:(lia)) as (b & Hb). exists b.
        apply (f30_raw_of_mrd mem' x b); [lia | lia | exact Hb].
      + destruct (Z_le_gt_dec (fr + 528) x) as [P1|P1]; [destruct (Z_lt_ge_dec x (fr + 532)) as [P2|P2]|].
        * right. destruct (Hpv x ltac:(lia)) as (b & Hb). exists b.
          apply (f30_raw_of_mrd mem' x b); [lia | lia | exact Hb].
        * left. apply HWout; [unfold app_mem; right; unfold APPMEM_END in *; lia | lia | lia | lia |
                              right; unfold AC.FS_SIZE in *; lia].
        * left. apply HWout; [unfold app_mem; right; unfold APPMEM_END in *; lia | lia | lia | lia |
                              right; unfold AC.FS_SIZE in *; lia].
      + left. apply HWout; [unfold app_mem; right; unfold APPMEM_END in *; lia | lia | lia | lia |
                            right; unfold AC.FS_SIZE in *; lia].
    - destruct (Z_le_gt_dec (fr + 448) x) as [N1|N1]; [destruct (Z_lt_ge_dec x (fr + 484)) as [N2|N2]|].
      + right. destruct (Hpo x ltac:(lia)) as (b & Hb). exists b.
        apply (f30_raw_of_mrd mem' x b); [lia | lia | exact Hb].
      + destruct (Z_le_gt_dec (fr + 528) x) as [P1|P1]; [destruct (Z_lt_ge_dec x (fr + 532)) as [P2|P2]|].
        * right. destruct (Hpv x ltac:(lia)) as (b & Hb). exists b.
          apply (f30_raw_of_mrd mem' x b); [lia | lia | exact Hb].
        * left. apply HWout; [unfold app_mem; right; unfold APPMEM_END in *; lia | lia | lia | lia |
                              right; unfold AC.FS_SIZE in *; lia].
        * left. apply HWout; [unfold app_mem; right; unfold APPMEM_END in *; lia | lia | lia | lia |
                              right; unfold AC.FS_SIZE in *; lia].
      + left. apply HWout; [unfold app_mem; right; unfold APPMEM_END in *; lia | lia | lia | lia |
                            right; unfold AC.FS_SIZE in *; lia]. }
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx.
    apply HWout.
    - unfold app_mem. right. unfold APPMEM_END, HIGHMEM_BEG in *. lia.
    - lia.
    - lia.
    - lia.
    - right. unfold AC.FS_SIZE in *. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split.
  { intros a Hin. refine (f30_addr_keep _ mem mem' a 1 (HAG a Hin) MU _).
    intros i Hi. replace (a + i) with a by lia.
    pose proof (f30_ag_bound a Hin) as Hab.
    assert (Hsa : shadow_addr a < shadow_addr (FS + 1085440)).
    { assert (Ha8 : a / 8 <= 657160 / 8) by (apply Z.div_le_mono; lia).
      assert (Hf8 : 7368704 / 8 <= (FS + 1085440) / 8)
        by (apply Z.div_le_mono; [lia | unfold AC.GT in HGTFS; lia]).
      change (657160 / 8) with 82145 in Ha8. change (7368704 / 8) with 921088 in Hf8.
      unfold shadow_addr. lia. }
    assert (Hsb : shadow_addr a < shadow_addr (sp - K30)).
    { assert (Ha8 : a / 8 <= 657160 / 8) by (apply Z.div_le_mono; lia).
      assert (Hf8 : 7368704 / 8 <= (sp - K30) / 8)
        by (apply Z.div_le_mono; [lia | unfold HIGHMEM_BEG in Hsphi; unfold K30,
              CL.REAC_CTRL_CLASSIFY_BOX_FRAME_K; lia]).
      change (657160 / 8) with 82145 in Ha8. change (7368704 / 8) with 921088 in Hf8.
      unfold shadow_addr. lia. }
    apply HWsho; [|lia|lia].
    apply shadow_of_app. unfold app_mem, LOWMEM_END. left. lia. }
  split.
  { (* the slot window outside the frame: the callee's window by its post; the rest keeps its shadow byte *)
    intros a Ha1 Ha2.
    assert (Hspk : (sp - K30) mod 8 = 0) by (clear -Hspm HK; rewrite HK; Z.div_mod_to_equations; lia).
    destruct (Z_le_gt_dec (sp - K30) a) as [L1|L1]; [destruct (Z_lt_ge_dec a sp) as [L2|L2]|].
    - exact (f30_addr_sub mem' (sp - K30) K30 a 1 HAWc L1 ltac:(lia) ltac:(lia)).
    - refine (f30_addr_keep _ mem mem' a 1 (HWA a Ha1 Ha2) MU _).
      intros i Hi. replace (a + i) with a by lia.
      apply HWsho.
      + apply shadow_of_app. unfold app_mem. right. unfold AF.SLOT_STACK, APPMEM_END, HIGHMEM_BEG in *. lia.
      + pose proof (f30_sh_mono (FS + 2134016) a ltac:(lia)) as Hm. lia.
      + pose proof (f30_sh_mono sp a ltac:(lia)) as Hm. lia.
    - refine (f30_addr_keep _ mem mem' a 1 (HWA a Ha1 Ha2) MU _).
      intros i Hi. replace (a + i) with a by lia.
      apply HWsho.
      + apply shadow_of_app. unfold app_mem. right. unfold AF.SLOT_STACK, APPMEM_END, HIGHMEM_BEG in *. lia.
      + pose proof (f30_sh_mono (FS + 2134016) a ltac:(lia)) as Hm. lia.
      + pose proof (f30_sh_lt a (sp - K30) ltac:(lia) Hspk ltac:(lia)) as Hm. lia. }
  split; [exact HSHI1|]. split; [exact HSHI2|]. split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|].
  (* the input block: a live block of g_H g, so app memory below stklo (below the callee's window), off the frame
     and off FS; neither its bytes nor their shadow bytes are written *)
  apply (fra_in_keep_sh g mem mem' Wc Hinb Hinblk MU).
  intros x Hx.
  destruct (Hinblk ltac:(lia)) as (Hin & _).
  assert (Hin' : In (g_p g, g_n g) (hb ++ g_H g)) by (apply in_or_app; right; exact Hin).
  destruct (f30_blocks (hb ++ g_H g) mem md (g_p g) (g_n g) HAH Hin') as (_ & Hend & Hall).
  destruct (Hall x Hx) as (Happx & Hnfs).
  assert (HnFS : ~ (FS <= x < FS + AC.FS_SIZE))
    by (intros Hc; apply Hnfs; exists FS; split; [lia | split; [exact Hwm | exact Hc]]).
  assert (Hnfr : ~ (fr <= x < fr + FRAME_BYTES)).
  { intros Hc. destruct Hloc2 as [[Hreal _] | [Hfs1 Hfs2]]; [lia | apply HnFS; lia]. }
  rewrite HFN in Hwlo.
  split.
  - apply HWout; [exact Happx | lia | lia | lia | lia].
  - apply HWsho; [apply shadow_of_app; exact Happx | |].
    + intros Hc. pose proof (f30_sh_inv (FS + 1085440) (FS + 2134016) x Hc) as Hb. apply HnFS. lia.
    + intros Hc. pose proof (f30_sh_inv (sp - K30) sp x Hc) as Hb. lia.
Qed.

(* A readable, writable byte as a one-byte cell. *)
Lemma f30_rw1_of : forall m a, 0 <= a -> a + 1 <= 2 ^ 64 ->
  wview rsegs m (wa a) <> None -> (exists b, mrd rsegs m (wa a) = Some b) ->
  exists b, rw_cells rsegs m a [C1 b].
Proof.
  intros m a H0 H1 Hw (b & Hb). exists b. split; [split|].
  - cbn [cells_wf cell_wf]. split; exact I.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    split; [exact H0|]. split; [cbn [length Z.of_nat]; lia|].
    intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia].
    cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. exact Hb.
  - cbn [cells_size csize Nat.add]. split; [exact H0|]. split; [cbn [Z.of_nat]; lia|].
    intros i Hi. replace (a + i) with a by lia. exact Hw.
Qed.

(* A spilled word as a read-only cell. *)
Lemma f30_ro8 : forall m a v, q64 m a v -> ro_cells rsegs m a [C8 (Z_to_bv 64 v)].
Proof.
  intros m a v H. split; [cbn [cells_wf cell_wf]; split; exact I|].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H.
Qed.

(* A byte of a live heap block is not a frame byte (the blocks lie below stklo and off the side stack). *)
Lemma f30_blk_apart : forall g fr hb regs mem md p n a, FRA B APIf ra g fr hb regs mem md ->
  In (p, n) (hb ++ g_H g) -> p <= a < p + n -> fr <= a < fr + FRAME_BYTES -> False.
Proof.
  intros g fr hb regs mem md p n a HFRA Hin Ha Hfa.
  pose proof HFRA as HF2.
  destruct HF2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfrA & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  destruct (f30_blocks _ mem md p n HAH Hin) as (_ & Hend & Hall).
  destruct (Hall a Ha) as (_ & Hnfs).
  destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
  - pose proof (Hreal a Hfa). lia.
  - exact (Hnfs (Hfs a Hfa)).
Qed.

(* The shadow byte of y is the frame's k-th shadow byte only for the granule [fr + 8k, fr + 8k + 8). *)
Lemma f30_sh_back : forall fr y k, 0 <= fr -> fr mod 8 = 0 -> 0 <= y -> shadow_addr y = Sfr fr + k ->
  fr + 8 * k <= y < fr + 8 * k + 8.
Proof. unfold Sfr, shadow_addr. intros fr y k H0 H8 Hy E. Z.div_mod_to_equations. lia. Qed.

(* The hint word and the flag bytes of a class other than 1 are apart from the class-1 ones. *)
Lemma f30_cls_apart : forall FS c jj, (c <= 10)%nat -> c <> 1%nat -> 0 <= jj < AC.a_fs_M c ->
  (AC.a_fs_hint FS c + 8 <= FS + 8 \/ FS + 16 <= AC.a_fs_hint FS c) /\
  (AC.a_fs_flag FS c jj < FS + 20480 \/ FS + 28672 <= AC.a_fs_flag FS c jj).
Proof.
  intros FS c jj Hc Hc1 Hj. unfold AC.a_fs_M in Hj. split.
  - destruct (Nat.eq_dec c 0) as [->|N].
    + left. unfold AC.a_fs_hint. cbn [Z.of_nat]. lia.
    + right. unfold AC.a_fs_hint. assert (Hc2 : 2 <= Z.of_nat c) by lia. lia.
  - destruct (Nat.eq_dec c 0) as [->|N].
    + left. unfold AC.a_fs_flag. cbn [Z.of_nat] in Hj |- *.
      change (2 ^ (15 - 0)) with 32768. change (2 ^ (14 - 0)) with 16384 in Hj. lia.
    + right. unfold AC.a_fs_flag. assert (Hc2 : 2 <= Z.of_nat c) by lia.
      assert (Hp1 : 2 ^ (15 - Z.of_nat c) <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia).
      assert (Hp2 : 0 <= 2 ^ (15 - Z.of_nat c)) by (apply Z.pow_nonneg; lia).
      change (2 ^ 15) with 32768. change (2 ^ 13) with 8192 in Hp1. lia.
Qed.

(* The side stack's state at the callee's return: the class-1 hint word and flag bytes come from the callee's own
   fp post, the header word and the other classes' from the bytes the run did not touch. *)
Lemma f30_fsok2 : forall m m' FS W,
  AC.a_fs_ok m FS -> Frame.munch W m m' ->
  (forall c, (c <= 10)%nat -> c <> 1%nat -> forall q, AC.a_fs_hint FS c <= q < AC.a_fs_hint FS c + 8 ->
     Frame.outside W q) ->
  (forall c jj, (c <= 10)%nat -> c <> 1%nat -> 0 <= jj < AC.a_fs_M c -> Frame.outside W (AC.a_fs_flag FS c jj)) ->
  stk rsegs m' FS (FS + AC.FS_SIZE) ->
  bytes_at rsegs m' (FS + 88) (le8 (Z_to_bv 64 20)) -> bytes_at rsegs m' (FS + 96) [Z_to_bv 8 0] ->
  fp_cls m' FS 1%nat ->
  0 <= FS -> FS + AC.FS_SIZE <= 2 ^ 64 ->
  AC.a_fs_ok m' FS.
Proof.
  intros m m' FS W Hok MU Hhint Hflag HST H88 H96 Hcls HFS0 HFS1.
  assert (HFSsz : AC.FS_SIZE = 11571200) by reflexivity.
  destruct Hok as (P1 & P2 & P3 & P4 & P5).
  destruct HST as (_ & _ & HSTv).
  assert (Hkeep : forall q, Frame.outside W q -> 0 <= q < 2 ^ 64 -> mbyte rsegs m' q = mbyte rsegs m q).
  { intros q Ho Hq. unfold mbyte. rewrite MU; [reflexivity|].
    rewrite MState.unsigned_lit by lia. exact Ho. }
  split.
  { intros a Ha. destruct (HSTv a Ha) as (Hv & b & Hb). split; [exact Hv | exists b; exact Hb]. }
  split.
  { pose proof (bytes_at_le8_word rsegs m' (FS + 88) (Z_to_bv 64 20) H88) as Hw.
    rewrite unsigned_lit in Hw by lia. exact Hw. }
  split.
  { destruct H96 as (_ & _ & Hb). pose proof (Hb 0%nat ltac:(cbn; lia)) as HH.
    cbn [nth_error] in HH. rewrite Z.add_0_r in HH. unfold mbyte. exact HH. }
  split.
  { intros c Hc. destruct (Nat.eq_dec c 1) as [->|N].
    - destruct Hcls as (_ & h & flags & Hh & _ & _ & _). exists (bv_unsigned h).
      replace (AC.a_fs_hint FS 1%nat) with (ASM.fs_hint FS 1%nat)
        by (unfold AC.a_fs_hint, ASM.fs_hint; reflexivity).
      exact (bytes_at_le8_word rsegs m' _ h Hh).
    - destruct (P4 c Hc) as (h & Hh). exists h.
      intros k Hk. rewrite Hkeep.
      + exact (Hh k Hk).
      + apply (Hhint c Hc N). lia.
      + unfold AC.a_fs_hint in *. assert (Z.of_nat c <= 10) by lia. lia. }
  { intros c jj Hc Hj. destruct (Nat.eq_dec c 1) as [->|N].
    - destruct Hcls as (_ & h & flags & _ & Hf & Hfl & Hfb).
      assert (Ejj : AC.a_fs_flag FS 1%nat jj = ASM.fs_flag FS 1%nat 0 + jj)
        by (unfold AC.a_fs_flag, ASM.fs_flag; lia).
      assert (Hlen : Z.of_nat (length flags) = AC.a_fs_M 1%nat)
        by (rewrite Hfl; unfold ASM.fs_M, AC.a_fs_M; reflexivity).
      destruct Hf as (_ & _ & Hfb2).
      pose proof (Hfb2 (Z.to_nat jj) ltac:(lia)) as HH.
      rewrite Z2Nat.id in HH by lia.
      destruct (nth_error flags (Z.to_nat jj)) as [b|] eqn:En;
        [|exfalso; apply nth_error_None in En; lia].
      rewrite Forall_forall in Hfb.
      pose proof (Hfb b (nth_error_In _ _ En)) as Hb01.
      rewrite Ejj. destruct Hb01 as [-> | ->]; [left | right]; exact HH.

    - rewrite Hkeep.
      + exact (P5 c jj Hc Hj).
      + exact (Hflag c jj Hc N Hj).
      + unfold AC.a_fs_flag in *. assert (Hc10 : Z.of_nat c <= 10) by lia.
        assert (Hp1 : 2 ^ (15 - Z.of_nat c) <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
        assert (Hp2 : 0 < 2 ^ (15 - Z.of_nat c)) by (apply Z.pow_pos_nonneg; lia).
        unfold AC.a_fs_M in Hj.
        assert (Hp3 : 2 ^ (14 - Z.of_nat c) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia).
        change (2 ^ 15) with 32768 in *. change (2 ^ 14) with 16384 in *. lia. }
Qed.

(* S_F30 (forms-asan-ubsan-v190.md), on the official cuts. *)
Lemma seg_F30 : forall j : nat, Hat B APIf ra (Inv_B82af8_at B APIf ra) j ->
  Hat B APIf ra (Inv_B82abc_at B APIf ra) j.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & Hr18 & Hr20 & HFT & HLK &
                    HFTK & HIFS & Hs312).
  subst c. rewrite SEGS.
  pose proof HFT as (Hs224 & Hs232 & Hphib & _).
  pose proof HFTK as (Hs184 & Hr22 & Hr24 & Hs272 & Hr25).
  pose proof HLK as (Hj255 & Hs240 & HOUR & HFLI).
  pose proof HFLI as (_ & _ & _ & _ & _ & _ & _ & Hs144 & Hs152 & _ & Hs160 & _ & Hs192 & _ & Hs216 & _ & _ & _ &
                      Hs264 & _ & _ & _ & HadU & Hfstk & (HadR & HadF & HadFi) & HKNT & _ & _).
  (* the Phi length and the 50 record bytes, from the Phi bytes *)
  pose proof (f30_phi_len (g_in g) j) as HphiL.
  assert (Hplen : Z.of_nat (length (t_phi (g_in g) j)) <= flen g j) by (unfold flen; lia).
  assert (Hflen0 : 0 <= flen g j) by (unfold flen; lia).
  assert (Hg50 : 50 <= flen g j -> bytes_at rsegs mem phi (t_g (g_in g) j)).
  { intros H50. unfold flen in H50. rewrite (f30_tg (g_in g) j H50).
    pose proof (f30_ba_sub mem phi (t_phi (g_in g) j) 0 50 Hphib ltac:(lia)) as H.
    cbn [skipn] in H. change (phi + Z.of_nat 0) with (phi + 0) in H. rewrite Z.add_0_r in H. exact H. }
  pose proof HHB as (Hphi0 & Hphiad).
  pose proof HFRA as HF2.
  destruct HF2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  clear Hspill Hsel Hfr40 Hhdr1 Hhdr2 Hsaved Herrno HSHI1 HSHI2 HSHI3 Hhb Hlive Hgimg Hsn.
  destruct (f30_fra_loc g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as
    (FS & Hwmtp & HFSr & HGTFS & HFSlo & HFSapp & Hhi & Hfr0 & HGTfr & Happ & Hloc2).
  destruct (fra_frame B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (Hdisj & HfrA & _ & Hfrw).
  destruct (fra_win B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (Hwlo & Hwstk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof Hwin as (Hw0 & Hw1 & Hwv).
  rewrite Haspz in Hdisj, Hwlo, Hwstk.
  unfold K30, CL.REAC_CTRL_CLASSIFY_BOX_FRAME_K in *.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HFSsz : AC.FS_SIZE = 11571200) by reflexivity.
  assert (Hfr8 : fr mod 8 = 0) by (clear -Hfrm; Z.div_mod_to_equations; lia).
  assert (Hub : fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Ha.
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha |- *. destruct Ha; lia. }
  pose proof (Hdisj 8864 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as Hfrsp.
  assert (HAhi : HIGHMEM_BEG <= A) by (unfold FN_STACK, AF.SLOT_STACK in *; lia).
  assert (Hsphi : HIGHMEM_BEG <= sp - 8864) by (unfold FN_STACK, AF.SLOT_STACK in *; lia).
  (* the class-6 band (FRA's side arm; on the real arm the frame is at or above stklo, above the whole side
     stack) and the callee's window addressable (FRA's slot window outside the frame, apart from it by
     fra_frame) *)
  assert (HFSfr : FS + 6328320 <= fr) by (destruct Hloc2 as [[H1 _] | [H1 _]]; lia).
  assert (HadW : addressable mem (sp - 8864) 8864).
  { apply f30_addr_join; [lia | lia | lia |].
    intros i Hi. apply HWA; [lia | destruct Hfrsp; lia]. }
  assert (HSfrlo : LOWMEM_END <= Sfr fr)
    by (unfold Sfr, shadow_addr, ASAN_K, LOWMEM_END; assert (0 <= fr / 8) by (apply Z.div_pos; lia); lia).
  assert (HSfrhi : Sfr fr + FRAME_SHADOW <= 2 ^ 64).
  { unfold Sfr, shadow_addr, ASAN_K. unfold APPMEM_END in Hub.
    assert (H8 : fr / 8 <= 140737488355328 / 8) by (apply Z.div_le_mono; lia).
    change (140737488355328 / 8) with 17592186044416 in H8. lia. }
  assert (HdSV : Sfr fr + FRAME_SHADOW <= fr + 528 \/ fr + 532 <= Sfr fr).
  { pose proof (Happ fr ltac:(lia)) as Hfa0. unfold app_mem in Hfa0.
    pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Ha2. unfold app_mem in Ha2.
    destruct Hfa0 as [Hlo|Hhi2].
    - right. unfold Sfr, shadow_addr, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *.
      assert (0 <= fr / 8) by (apply Z.div_pos; lia). destruct Ha2; lia.
    - left. unfold Sfr, shadow_addr, ASAN_K. unfold HIGHMEM_BEG in Hhi2.
      Z.div_mod_to_equations. lia. }
  assert (HdSA : Sfr fr + 67 <= A + 192).
  { pose proof (Happ fr ltac:(lia)) as Hfa0. unfold app_mem in Hfa0. destruct Hfa0 as [Hlo|Hhi2].
    - unfold Sfr, shadow_addr, ASAN_K, LOWMEM_END, HIGHMEM_BEG in *.
      assert (fr / 8 <= fr) by (apply Z.div_le_upper_bound; lia). lia.
    - unfold Sfr, shadow_addr, ASAN_K. unfold HIGHMEM_BEG in *. Z.div_mod_to_equations. lia. }
  (* Phi's block (Phi, a_size len), a live block of the cut (a_size len >= 1): apart from the frame and from the
     side stack *)
  assert (HInb : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
    by (apply in_or_app; left; unfold hb1; left; reflexivity).
  destruct (f30_blocks _ mem md phi (AC.a_size (flen g j)) HAH HInb) as (Hphi4096 & Hphistk & Hphiall).
  pose proof (AC.a_laws_block_size _ _ _ _ _ LAWS _ mem md phi (AC.a_size (flen g j)) HAH HInb) as Hlen0.
  assert (Hasz : AC.a_size (flen g j) = Z.max (flen g j) 1) by reflexivity.
  assert (Hphiapp : forall i, 0 <= i < AC.a_size (flen g j) -> app_mem (phi + i)).
  { intros i Hi. destruct Hphiad as (_ & _ & _ & HA2). destruct (HA2 i Hi) as (Hap & _). exact Hap. }
  assert (Hphifr : forall i, 0 <= i < AC.a_size (flen g j) -> ~ (fr <= phi + i < fr + FRAME_BYTES)).
  { intros i Hi Hc.
    exact (f30_blk_apart g fr (hb1 phi (AC.a_size (flen g j))) regs mem md phi (AC.a_size (flen g j)) (phi + i)
             HFRA HInb ltac:(lia) Hc). }
  assert (HPHIAP : fr + FRAME_BYTES <= phi \/ phi + AC.a_size (flen g j) <= fr).
  { destruct (Z_le_gt_dec (fr + FRAME_BYTES) phi) as [L1|L1]; [left; exact L1|].
    destruct (Z_le_gt_dec (phi + AC.a_size (flen g j)) fr) as [L2|L2]; [right; exact L2|].
    exfalso. apply (Hphifr (Z.max 0 (fr - phi))); lia. }
  assert (HphiFS : forall i, 0 <= i < AC.a_size (flen g j) -> ~ (FS <= phi + i < FS + AC.FS_SIZE)).
  { intros i Hi Hc.
    assert (Hfs : AC.a_in_fs AC.ASYMS mem (phi + i))
      by (exists FS; split; [lia | split; [exact Hwmtp | exact Hc]]).
    destruct (Hphiall (phi + i) ltac:(lia)) as (_ & Hn). exact (Hn Hfs). }
  assert (Hphish : forall i, 0 <= i < AC.a_size (flen g j) ->
            ~ (Sfr fr + 56 <= shadow_addr (phi + i) < Sfr fr + 67)).
  { intros i Hi Hc.
    pose proof (f30_sh_back fr (phi + i) (shadow_addr (phi + i) - Sfr fr) Hfr0 Hfr8 ltac:(lia) ltac:(lia)) as Hb.
    exact (Hphifr i Hi ltac:(lia)). }
  (* the cells the run reads and writes *)
  assert (HSW0 : shadow_rw mem) by exact (RT_shadow_rw _ _ _ HRT).
  assert (Hshk : forall k, 56 <= k <= 66 -> in_shadow (Sfr fr + k)).
  { intros k Hk.
    assert (E : shadow_addr (fr + 8 * k) = Sfr fr + k) by (apply (f30_sh_off fr (8 * k) k); lia).
    rewrite <- E. apply shadow_of_app. apply Happ. lia. }
  assert (Hcell : forall k, 56 <= k <= 66 -> exists b, rw_cells rsegs mem (Sfr fr + k) [C1 b]).
  { intros k Hk. pose proof (Hshk k Hk) as Hin. destruct (HSW0 (Sfr fr + k) Hin) as (Hv & Hr).
    exact (f30_rw1_of mem (Sfr fr + k) ltac:(unfold LOWMEM_END in *; lia)
             ltac:(unfold LOWMEM_END in *; lia) Hv Hr). }
  destruct (Hcell 56 ltac:(lia)) as (c56 & Hc56). destruct (Hcell 57 ltac:(lia)) as (c57 & Hc57).
  destruct (Hcell 58 ltac:(lia)) as (c58 & Hc58). destruct (Hcell 59 ltac:(lia)) as (c59 & Hc59).
  destruct (Hcell 60 ltac:(lia)) as (c60 & Hc60). destruct (Hcell 66 ltac:(lia)) as (c66 & Hc66).
  destruct (f30_cells_of_stk mem fr (fr + FRAME_BYTES) (fr + 528) 4%nat Hfstk ltac:(lia) ltac:(cbn; lia)
              ltac:(lia) ltac:(cbn; lia)) as (vb0 & Hvb0).
  assert (Hvl0 : length vb0 = 4%nat)
    by (destruct Hvb0 as [[Hwf _] _]; cbn [cells_wf cell_wf] in Hwf; tauto).
  assert (HA64 : 0 <= A /\ A + 448 <= 2 ^ 64) by lia.
  assert (Q192 : q64 mem (A + 192) (fr + 528))
    by (apply (f30_spill regs mem 192 _ A Hs192 Hr9); lia).
  assert (Q216 : q64 mem (A + 216) (fr + 448))
    by (apply (f30_spill regs mem 216 _ A Hs216 Hr9); lia).
  assert (Q264 : q64 mem (A + 264) (fr + 2624))
    by (apply (f30_spill regs mem 264 _ A Hs264 Hr9); lia).
  assert (Hlenb : 0 <= flen g j < 2 ^ 64) by lia.
  assert (Hphib64 : 0 <= phi < 2 ^ 64) by lia.
  assert (HdSV67 : Sfr fr + 67 <= fr + 528 \/ fr + 528 + 4 <= Sfr fr) by (destruct HdSV; [left | right]; lia).
  assert (HdSAd : Sfr fr + 67 <= A + 192 \/ A + 272 <= Sfr fr) by (left; exact HdSA).
  assert (HdVA : fr + 528 + 4 <= A + 192 \/ A + 272 <= fr + 528) by (left; lia).
  apply (f30_run_lib regs (Z_to_bv 64 0x82abc) mem md
    (fun R0 pc' m2 =>
       pc' = Z_to_bv 64 0x82af8 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
       getr R0 26 = getr regs 26 /\ getr R0 18 = getr regs 18 /\ getr R0 20 = getr regs 20 /\
       getr R0 25 = getr regs 25 /\ getr R0 22 = getr regs 22 /\ getr R0 24 = getr regs 24 /\
       getr R0 27 = getr regs 27 /\
       getr R0 10 = Z_to_bv 64 (RC.cl_r (t_cls (g_in g) j)) /\
       FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) R0 m2 md /\
       ENT APIf g (hb1 phi (AC.a_size (flen g j))) m2 md /\
       HB m2 phi (flen g j) /\ OURb g fr m2 /\
       (forall off v, 0 <= off <= 440 -> q64 mem (A + off) v -> q64 m2 (A + off) v) /\
       bytes_at rsegs m2 (fr + 448) (t_B (g_in g) j) /\
       addressable m2 (fr + 452) 6 /\ addressable m2 (fr + 2624) 6 /\
       addressable m2 (fr + 2688) 38 /\ addressable m2 (fragb fr) 72 /\ addressable m2 (fr + 2880) 40 /\
       (forall e, t_cls (g_in g) j = Some e -> u32 m2 (fr + 528) e) /\
       bytes_at rsegs m2 phi (t_phi (g_in g) j) /\ stk rsegs m2 fr (fr + FRAME_BYTES) /\ KNT m2 /\
       IFS g fr (S j) regs m2)
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold Regs6ss.mkR_of.
    eapply evt_cut.
    { eapply (f30s_evt_ro (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
                (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
                (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
                (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
                (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30)
                (getr regs 31) fp_regs fp_csr mem A (Sfr fr) (fr + 528) (fr + 448) (fr + 2624) phi
                (flen g j) c56 c57 c58 c59 c60 c66 vb0);
        try exact Hr9; try exact Hr19; try exact Hr18; try exact Hr20; try assumption; try lia;
        try (unfold LOWMEM_END in *; lia); try (apply f30_ro8; assumption).
    }
    intros ms1 (m1 & Em1 & MU1 & WM1 & HroM1 & (vb1 & Hv1 & Hvl1) & Hb56 & Hb57 & Hb58 & Hb59 & Hb60 & Hb66).
    subst ms1.
    replace (fr + 528 + 4) with (fr + 532) in MU1 by lia.
    (* the six written shadow bytes and the untouched rest of the frame's shadow *)
    assert (Hpres1 : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> exists b, mrd rsegs m1 (wa x) = Some b).
    { intros x Hx.
      destruct (Z.eq_dec x (Sfr fr + 56)) as [->|N0]; [destruct Hb56 as (b & Hb & _); exists b; exact Hb|].
      destruct (Z.eq_dec x (Sfr fr + 57)) as [->|N1]; [destruct Hb57 as (b & Hb & _); exists b; exact Hb|].
      destruct (Z.eq_dec x (Sfr fr + 58)) as [->|N2]; [destruct Hb58 as (b & Hb & _); exists b; exact Hb|].
      destruct (Z.eq_dec x (Sfr fr + 59)) as [->|N3]; [destruct Hb59 as (b & Hb & _); exists b; exact Hb|].
      destruct (Z.eq_dec x (Sfr fr + 60)) as [->|N4]; [destruct Hb60 as (b & Hb & _); exists b; exact Hb|].
      destruct (Z.eq_dec x (Sfr fr + 66)) as [->|N5]; [destruct Hb66 as (b & Hb & _); exists b; exact Hb|].
      destruct Hsh as (shl & Hshb & Hshl).
      destruct (f30_ba_some mem (Sfr fr) shl (x - Sfr fr) Hshb ltac:(rewrite Hshl, Z2Nat.id by lia; lia))
        as (b & Hb).
      replace (Sfr fr + (x - Sfr fr)) with x in Hb by lia.
      exists b. unfold mrd in *. rewrite MU1; [exact Hb|].
      rewrite wa_unsigned by (unfold LOWMEM_END in *; lia).
      cbn [Frame.outside]. repeat split; try exact I; try lia. }
    assert (Hsh1 : exists sh, bytes_at rsegs m1 (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW).
    { rewrite FRAME_SHADOW_val. change (Z.to_nat 392) with 392%nat.
      apply (f30_ba_present m1 392%nat (Sfr fr) ltac:(unfold LOWMEM_END in *; lia)
               ltac:(cbn; unfold LOWMEM_END in *; lia)).
      intros i Hi. apply Hpres1. cbn [Z.of_nat] in *. lia. }
    assert (Hpresv : forall x, fr + 528 <= x < fr + 532 -> exists b, mrd rsegs m1 (wa x) = Some b).
    { intros x Hx. destruct Hv1 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
      destruct (f30_ba_some m1 (fr + 528) vb1 (x - (fr + 528)) Hb ltac:(rewrite Hvl1; lia)) as (b & Hb2).
      exists b. replace (fr + 528 + (x - (fr + 528))) with x in Hb2 by lia. exact Hb2. }
    (* an application byte away from the written word is outside the run's writes *)
    assert (HW3app : forall x, app_mem x -> ~ (fr + 528 <= x < fr + 532) ->
              Frame.outside [(Sfr fr + 56, Sfr fr + 61); (Sfr fr + 66, Sfr fr + 67);
                             (fr + 528, fr + 532)] x).
    { intros x Hax Hn. cbn [Frame.outside]. repeat split; try exact I; try exact Hn;
        intros Hc; apply (app_not_shadow x Hax);
        replace x with (Sfr fr + (x - Sfr fr)) by lia; apply Hshk; lia. }
    assert (HW3sh : forall x, in_shadow x -> ~ (Sfr fr + 56 <= x < Sfr fr + 67) ->
              Frame.outside [(Sfr fr + 56, Sfr fr + 61); (Sfr fr + 66, Sfr fr + 67);
                             (fr + 528, fr + 532)] x).
    { intros x Hsx Hn. cbn [Frame.outside]. repeat split; try exact I; try lia.
      intros Hc. exact (app_not_shadow x (Happ x ltac:(lia)) Hsx). }
    assert (MU1' : Frame.munch [(Sfr fr + 56, Sfr fr + 67); (fr + 528, fr + 532)] mem m1).
    { eapply Frame.munch_weaken; [|exact MU1]. intros x Hx. cbn [Frame.outside] in Hx |- *.
      repeat split; try exact I; lia. }
    assert (HPM1 : forall a, 0 <= a < 2 ^ 64 -> (exists b, mbyte rsegs mem a = Some b) ->
                     (exists b, mbyte rsegs m1 a = Some b)).
    { intros a Ha (b & Hb).
      destruct (Z_le_gt_dec (Sfr fr + 56) a) as [L1|L1];
        [destruct (Z_lt_ge_dec a (Sfr fr + 67)) as [L2|L2]|].
      - destruct (Hpres1 a ltac:(lia)) as (b' & Hb'). exists b'. unfold mbyte, mrd, wa in *. exact Hb'.
      - destruct (Z_le_gt_dec (fr + 528) a) as [M1|M1]; [destruct (Z_lt_ge_dec a (fr + 532)) as [M2|M2]|].
        + destruct (Hpresv a ltac:(lia)) as (b' & Hb'). exists b'. unfold mbyte, mrd, wa in *. exact Hb'.
        + exists b. unfold mbyte in *. rewrite MU1'; [exact Hb|].
          rewrite MState.unsigned_lit by lia. cbn [Frame.outside]. repeat split; try exact I; lia.
        + exists b. unfold mbyte in *. rewrite MU1'; [exact Hb|].
          rewrite MState.unsigned_lit by lia. cbn [Frame.outside]. repeat split; try exact I; lia.
      - destruct (Z_le_gt_dec (fr + 528) a) as [M1|M1]; [destruct (Z_lt_ge_dec a (fr + 532)) as [M2|M2]|].
        + destruct (Hpresv a ltac:(lia)) as (b' & Hb'). exists b'. unfold mbyte, mrd, wa in *. exact Hb'.
        + exists b. unfold mbyte in *. rewrite MU1'; [exact Hb|].
          rewrite MState.unsigned_lit by lia. cbn [Frame.outside]. repeat split; try exact I; lia.
        + exists b. unfold mbyte in *. rewrite MU1'; [exact Hb|].
          rewrite MState.unsigned_lit by lia. cbn [Frame.outside]. repeat split; try exact I; lia. }
    clear HdSV HdSV67 HdSAd HdVA HdSA Hs5.
    destruct (f30_fra1 g fr (hb1 phi (AC.a_size (flen g j))) regs mem m1 md HFRA HENT MU1' WM1 HroM1 HPM1 Hsh1
                Hpresv) as (HFRA1 & HENT1 & HSTK1).
    pose proof HFRA1 as HF1b.
    destruct HF1b as (A1 & sp1 & s51 & HRT1 & HAH1 & _ & _ & _ & _ & _ & _ & Haspz1 & _ & _ & _ & Hr9a &
      _ & _ & _ & _ & _ & _ & HAS1 & Hspa1 & _ & HA4481 & HS41 & _ & _ & _ & _ & _ & _ & _ & _ & Hwin1 &
      _ & _ & _ & _ & _ & _ & _ & _ & _).
    assert (EA1 : A1 = A).
    { pose proof Hwin1 as (Hw01 & Hw11 & _).
      unfold rg in Hr9, Hr9a. rewrite Hr9 in Hr9a. apply (f_equal bv_unsigned) in Hr9a.
      rewrite !unsigned_lit in Hr9a by lia. lia. }
    clear HAS1 Hspa1 HA4481 HS41 Hwin1.
    assert (Esp1 : sp1 = sp) by (unfold AC.aspZ in Haspz, Haspz1; lia).
    subst A1 sp1.
    (* what the stores made addressable *)
    assert (HadO1 : addressable m1 (fr + 448) 36).
    { apply f30_addr_of; try lia; [intros i Hi; apply Happ; lia|].
      intros i Hi.
      destruct (Z_lt_ge_dec i 8) as [R0|R0].
      { destruct Hb56 as (b & Hb & Hs). exists b. split; [|left; lia].
        replace (fr + 448 + i) with (fr + (448 + i)) by lia.
        rewrite (f30_sh_off fr (448 + i) 56 ltac:(lia) Hfr8 ltac:(lia)). exact Hb. }
      destruct (Z_lt_ge_dec i 16) as [R1|R1].
      { destruct Hb57 as (b & Hb & Hs). exists b. split; [|left; lia].
        replace (fr + 448 + i) with (fr + (448 + i)) by lia.
        rewrite (f30_sh_off fr (448 + i) 57 ltac:(lia) Hfr8 ltac:(lia)). exact Hb. }
      destruct (Z_lt_ge_dec i 24) as [R2|R2].
      { destruct Hb58 as (b & Hb & Hs). exists b. split; [|left; lia].
        replace (fr + 448 + i) with (fr + (448 + i)) by lia.
        rewrite (f30_sh_off fr (448 + i) 58 ltac:(lia) Hfr8 ltac:(lia)). exact Hb. }
      destruct (Z_lt_ge_dec i 32) as [R3|R3].
      { destruct Hb59 as (b & Hb & Hs). exists b. split; [|left; lia].
        replace (fr + 448 + i) with (fr + (448 + i)) by lia.
        rewrite (f30_sh_off fr (448 + i) 59 ltac:(lia) Hfr8 ltac:(lia)). exact Hb. }
      { destruct Hb60 as (b & Hb & Hs). exists b. split.
        - replace (fr + 448 + i) with (fr + (448 + i)) by lia.
          rewrite (f30_sh_off fr (448 + i) 60 ltac:(lia) Hfr8 ltac:(lia)). exact Hb.
        - right. rewrite Hs. split; [|lia].
          assert (Em : (fr + 448 + i) mod 8 = i - 32) by (clear -Hfr8 R3 Hi; Z.div_mod_to_equations; lia).
          lia. } }
    assert (HadV1 : addressable m1 (fr + 528) 4).
    { apply f30_addr_of; try lia; [intros i Hi; apply Happ; lia|].
      intros i Hi. destruct Hb66 as (b & Hb & Hs). exists b. split.
      - replace (fr + 528 + i) with (fr + (528 + i)) by lia.
        rewrite (f30_sh_off fr (528 + i) 66 ltac:(lia) Hfr8 ltac:(lia)). exact Hb.
      - right. rewrite Hs. split; [|lia].
        assert (Em : (fr + 528 + i) mod 8 = i) by (clear -Hfr8 Hi; Z.div_mod_to_equations; lia). lia. }
    (* the addressable ranges carried across the stores *)
    assert (HadU1 : addressable m1 (fr + 2624) 6).
    { refine (f30_addr_keep _ mem m1 _ 6 HadU MU1 _). intros i Hi.
      apply HW3sh; [apply shadow_of_app; apply Happ; lia|].
      intros Hc.
      pose proof (f30_sh_back fr (fr + 2624 + i) (shadow_addr (fr + 2624 + i) - Sfr fr) Hfr0 Hfr8
                    ltac:(lia) ltac:(lia)) as Hb. lia. }
    assert (HadR1 : addressable m1 (fr + 2688) 38).
    { refine (f30_addr_keep _ mem m1 _ 38 HadR MU1 _). intros i Hi.
      apply HW3sh; [apply shadow_of_app; apply Happ; lia|].
      intros Hc.
      pose proof (f30_sh_back fr (fr + 2688 + i) (shadow_addr (fr + 2688 + i) - Sfr fr) Hfr0 Hfr8
                    ltac:(lia) ltac:(lia)) as Hb. lia. }
    assert (HadF1 : addressable m1 (fragb fr) 72).
    { refine (f30_addr_keep _ mem m1 _ 72 HadF MU1 _). intros i Hi. unfold fragb.
      apply HW3sh; [apply shadow_of_app; apply Happ; lia|].
      intros Hc.
      pose proof (f30_sh_back fr (fr + 2768 + i) (shadow_addr (fr + 2768 + i) - Sfr fr) Hfr0 Hfr8
                    ltac:(lia) ltac:(lia)) as Hb. lia. }
    assert (HadFi1 : addressable m1 (fr + 2880) 40).
    { refine (f30_addr_keep _ mem m1 _ 40 HadFi MU1 _). intros i Hi.
      apply HW3sh; [apply shadow_of_app; apply Happ; lia|].
      intros Hc.
      pose proof (f30_sh_back fr (fr + 2880 + i) (shadow_addr (fr + 2880 + i) - Sfr fr) Hfr0 Hfr8
                    ltac:(lia) ltac:(lia)) as Hb. lia. }
    assert (HadW1 : addressable m1 (sp - 8864) 8864).
    { refine (f30_addr_keep _ mem m1 _ _ HadW MU1 _). intros i Hi.
      apply HW3sh; [apply shadow_of_app; unfold app_mem; right; unfold APPMEM_END in *; lia|].
      intros Hc.
      pose proof (f30_sh_back fr (sp - 8864 + i) (shadow_addr (sp - 8864 + i) - Sfr fr) Hfr0 Hfr8
                    ltac:(lia) ltac:(lia)) as Hb. lia. }
    assert (HadBC : addressable mem RPC.REAC_CTRL_PARSE_BC 6).
    { split; [unfold RPC.REAC_CTRL_PARSE_BC; lia|]. split; [lia|].
      split; [unfold RPC.REAC_CTRL_PARSE_BC, APPMEM_END; lia|].
      intros i Hi.
      assert (Hg : in_globals AF.frame_AG (RPC.REAC_CTRL_PARSE_BC + i)).
      { exists 0x21200, 7. split; [unfold AF.frame_AG; cbn [In]; tauto |
          unfold RPC.REAC_CTRL_PARSE_BC; lia]. }
      destruct (HAG _ Hg) as (_ & _ & _ & HA2). destruct (HA2 0 ltac:(lia)) as (Hap & Hb).
      rewrite Z.add_0_r in Hap, Hb. split; [exact Hap | exact Hb]. }
    assert (HadBC1 : addressable m1 RPC.REAC_CTRL_PARSE_BC 6).
    { refine (f30_addr_keep _ mem m1 _ 6 HadBC MU1 _). intros i Hi.
      apply HW3sh.
      - apply shadow_of_app. unfold app_mem, LOWMEM_END, RPC.REAC_CTRL_PARSE_BC. left. lia.
      - intros Hc.
        pose proof (f30_sh_back fr (RPC.REAC_CTRL_PARSE_BC + i)
                      (shadow_addr (RPC.REAC_CTRL_PARSE_BC + i) - Sfr fr) Hfr0 Hfr8
                      ltac:(unfold RPC.REAC_CTRL_PARSE_BC; lia) ltac:(lia)) as Hb.
        unfold RPC.REAC_CTRL_PARSE_BC, AC.GT in *. lia. }
    assert (Hphiad1 : addressable m1 phi (AC.a_size (flen g j))).
    { refine (f30_addr_keep _ mem m1 _ _ Hphiad MU1 _). intros i Hi.
      apply HW3sh; [apply shadow_of_app; apply Hphiapp; lia | exact (Hphish i Hi)]. }
    (* the byte lists carried across the stores *)
    assert (Hkeepfr : forall a n, bytes_at rsegs mem a n -> (forall i, 0 <= i < Z.of_nat (length n) ->
                        app_mem (a + i) /\ ~ (fr + 528 <= a + i < fr + 532)) -> bytes_at rsegs m1 a n).
    { intros a n Hb Hc. eapply fl_bytes; [exact Hb | exact MU1 |].
      intros x Hx. destruct (Hc (x - a) ltac:(lia)) as (Hap & Hnn).
      replace (a + (x - a)) with x in Hap, Hnn by lia. apply HW3app; assumption. }
    assert (HOUR1 : OURb g fr m1).
    { unfold OURb in *. apply Hkeepfr; [exact HOUR|].
      intros i Hi. rewrite OUR_length in Hi. split; [apply Happ; lia | lia]. }
    assert (Hphib1 : bytes_at rsegs m1 phi (t_phi (g_in g) j)).
    { apply Hkeepfr; [exact Hphib|]. intros i Hi.
      split; [apply Hphiapp; rewrite Hasz; lia|].
      intros Hc. apply (Hphifr i ltac:(rewrite Hasz; lia)). lia. }
    assert (Hg501 : 50 <= flen g j -> bytes_at rsegs m1 phi (t_g (g_in g) j)).
    { intros H50. apply Hkeepfr; [exact (Hg50 H50)|]. intros i Hi.
      rewrite f30_t_g_length in Hi.
      split; [apply Hphiapp; rewrite Hasz; lia|].
      intros Hc. apply (Hphifr i ltac:(rewrite Hasz; lia)). lia. }
    assert (Hfstk1 : stk rsegs m1 fr (fr + FRAME_BYTES)).
    { eapply (CLP.fl_stk _ mem m1 fr (fr + FRAME_BYTES)); [exact Hfstk | exact MU1 | exact WM1 |].
      intros x Hx. destruct (Z_le_gt_dec (fr + 528) x) as [M1|M1];
        [destruct (Z_lt_ge_dec x (fr + 532)) as [M2|M2]|].
      - right. exact (Hpresv x ltac:(lia)).
      - left. apply HW3app; [apply Happ; lia | lia].
      - left. apply HW3app; [apply Happ; lia | lia]. }
    destruct (f30_cells_of_stk m1 fr (fr + FRAME_BYTES) (fr + 448) 36%nat Hfstk1 ltac:(lia) ltac:(cbn; lia)
                ltac:(lia) ltac:(cbn; lia)) as (junk1 & Ho1).
    assert (Hstkw1 : stk rsegs m1 (sp - 8864) sp).
    { destruct (stk_split rsegs mem (sp - FN_STACK) (sp - 8864) sp Hwstk ltac:(unfold FN_STACK; lia))
        as (_ & Hhi2).
      eapply (Frame.stk_transport rsegs _ mem m1 (sp - 8864) sp); [exact Hhi2 | exact MU1 | exact WM1 |].
      intros x Hx. left. apply HW3app; [unfold app_mem; right; unfold APPMEM_END in *; lia | lia]. }
    (* the runtime cells and the side-stack state at the call *)
    destruct (f30_cells sp m1 md HRT1) as (HAC1 & HSW1 & HRB1 & HRM1 & HGC1 & HC2541 & HC2551).
    (* the callee's side-stack package from FRA after the stores (Tac_fsfree.fra_fp): its window is in the slot
       window, its writes o / v in the frame, its data Phi's 50 bytes (inside the live block (Phi, a_size len)) and
       our[] / o / v (in the frame); the side stack it names is the one at the tp word *)
    assert (Hwm1 : word_mem rsegs m1 (AC.as_tp AC.ASYMS) FS).
    { eapply kb_word_munch; [exact Hwmtp | exact MU1 |].
      intros k Hk. split; [unfold AC.as_tp, AC.ASYMS; cbn; lia|].
      apply HW3app; [unfold app_mem, LOWMEM_END, AC.as_tp, AC.ASYMS; cbn; left; lia
                    | unfold AC.as_tp, AC.ASYMS, AC.GT in *; cbn in *; lia]. }
    (* the kind-name table (image data at KNC.KIND_NAME, below GT): the stores write o and the frame's shadow *)
    assert (HKNT1 : KNT m1).
    { apply (f30_knt_keep _ mem m1 HKNT MU1). intros xk Hxk. unfold KNC.KIND_NAME in Hxk. split.
      - apply HW3app; [unfold app_mem, LOWMEM_END; left; lia | clear - Hxk HGTfr; unfold AC.GT in *; lia].
      - apply HW3sh; [apply shadow_of_app; unfold app_mem, LOWMEM_END; left; lia|].
        intros Hc. clear - Hc Hxk HGTfr. unfold Sfr, shadow_addr, AC.GT in *. Z.div_mod_to_equations. lia. }
    destruct (fra_fp B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs m1 md [1%nat] 8864
                (CL.reac_ctrl_classify_box_frame_W (fr + 448) (fr + 528) sp)
                (CL.reac_ctrl_classify_box_frame_D phi (flen g j) (fr + 2624) (fr + 448) (fr + 528)) HFRA1
                ltac:(intros cc Hcc; cbn [In] in Hcc; destruct Hcc as [<- | []]; lia)
                ltac:(lia)
                ltac:(intros w Hw; unfold CL.reac_ctrl_classify_box_frame_W,
                        CL.REAC_CTRL_CLASSIFY_BOX_FRAME_K in Hw; cbn [In] in Hw;
                      destruct Hw as [<- | [<- | [<- | []]]]; cbn [fst snd];
                      [left | right; left | right; left]; lia)
                ltac:(intros d Hd; unfold CL.reac_ctrl_classify_box_frame_D in Hd;
                      destruct (flen g j <? 50) eqn:E50; cbn [app In] in Hd;
                      [destruct Hd as [<- | [<- | []]]; right; left; cbn [fst snd]; lia
                      | apply Z.ltb_ge in E50; destruct Hd as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd];
                        [right; right; split; [lia|]; exists phi, (AC.a_size (flen g j));
                         split; [exact HInb|]; split; [lia|]; rewrite Hasz; lia
                        | right; left; lia | right; left; lia | right; left; lia]]))
      as (FSc & HFPc & HTLSc & _ & _).
    rewrite Haspz in HFPc, HTLSc.
    assert (EFS : FSc = FS) by (apply (f30_fp_FS [1%nat] m1 FS FSc _ _ _ _ HFPc Hwm1 HFSr); lia).
    subst FSc.
    assert (HTLS1 : CL.reac_ctrl_classify_box_frame_tls m1 (AC.as_tp AC.ASYMS) FS (sp - 8864) sp)
      by (unfold CL.reac_ctrl_classify_box_frame_tls; exact HTLSc).
    (* the call (on the normalized memory, f30_cl_ro) *)
    eapply evt_cut.
    { eapply (f30_cl_ro (Z_to_bv 64 0x82af8)) with (f := phi) (n := flen g j) (u := fr + 2624)
        (o := fr + 448) (v := fr + 528) (S := sp) (FS := FS) (fr := t_g (g_in g) j)
        (us := OUR (g_in g)) (junk := junk1) (vb := vb1).
      all: try unfold K30, CL.REAC_CTRL_CLASSIFY_BOX_FRAME_K.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact Hr2.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - exact Hspm.
      - unfold CL.REAC_CTRL_CLASSIFY_BOX_FRAME_K; lia.
      - unfold CL.REAC_CTRL_CLASSIFY_BOX_FRAME_K; exact Hstkw1.
      - apply f30_t_g_length.
      - intros H50. split; [lia|]. split; [lia|]. split; [exact (Hg501 H50)|].
        left. unfold CL.REAC_CTRL_CLASSIFY_BOX_FRAME_K. lia.
      - unfold AC.GT in HGTfr; lia.
      - clear -Hfrm; Z.div_mod_to_equations; lia.
      - lia.
      - exact Ho1.
      - unfold CL.REAC_CTRL_CLASSIFY_BOX_FRAME_K. lia.
      - intros H50. destruct HPHIAP as [HP|HP]; [left; lia | right; lia].
      - left; lia.
      - apply OUR_length.
      - intros H50. split; [lia|]. split; [exact HOUR1|].
        unfold CL.REAC_CTRL_CLASSIFY_BOX_FRAME_K. lia.
      - unfold AC.GT in HGTfr; lia.
      - clear -Hfrm; Z.div_mod_to_equations; lia.
      - lia.
      - exact Hv1.
      - unfold CL.REAC_CTRL_CLASSIFY_BOX_FRAME_K. lia.
      - right; lia.
      - destruct HPHIAP as [HP|HP]; [left; lia | right; lia].
      - left; lia.
      - exact HroM1.
      - unfold AC.GT in HGTfr; lia.
      - unfold AC.GT in HGTfr; lia.
      - exact HAC1.
      - exact HSW1.
      - unfold CL.REAC_CTRL_CLASSIFY_BOX_FRAME_K. lia.
      - unfold APPMEM_END in *. lia.
      - unfold CL.REAC_CTRL_CLASSIFY_BOX_FRAME_K. exact HadW1.
      - intros H50. split; [|split; [exact HadU1 | split; apply Happ; lia]].
        assert (E50 : AC.a_size (flen g j) = flen g j) by (rewrite Hasz; lia).
        rewrite E50 in Hphiad1. destruct Hphiad1 as (P1 & P2 & P3 & P4).
        split; [lia|]. split; [lia|]. split; [lia|]. intros i Hi. apply P4. lia.
      - exact HadO1.
      - apply Happ; lia.
      - right. unfold ASM.CF, AC.GT in *. lia.
      - exact HadV1.
      - right. unfold RT_HI, AC.GT in *. lia.
      - exact HadBC1.
      - exact HRB1.
      - exact HRM1.
      - exact HGC1.
      - exact HC2541.
      - exact HC2551.
      - rewrite Hr4, unsigned_lit by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
        unfold CL.REAC_CTRL_CLASSIFY_BOX_FRAME_K. exact HFPc.
      - rewrite Hr4, unsigned_lit by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
        unfold CL.REAC_CTRL_CLASSIFY_BOX_FRAME_K. exact HTLS1. }
    intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                Em2 & MU2 & WM2 & HroM2 & ST2 & HO2 & HV2 & AC2 & SW2 & AW2 & FP2 & TL2).
    subst ms2.
    match goal with
    | |- context [ret_pc (Z_to_bv 64 ?z)] =>
        replace (ret_pc (Z_to_bv 64 z)) with (Z_to_bv 64 z)
          by (symmetry; apply ret_pc_even; [clear; lia | reflexivity])
    end.
    unfold K30, CL.REAC_CTRL_CLASSIFY_BOX_FRAME_K in MU2, ST2, AW2, FP2, TL2.
    replace (fr + 448 + 36) with (fr + 484) in MU2 by lia.
    replace (fr + 528 + 4) with (fr + 532) in MU2 by lia.
    (* the facts of the entry memory, the call's premises and the stores' cells are spent; keep lia's context
       small (one disjunction left: the frame against the callee's window, Hfrsp) *)
    clear HENT HRT Hro HadW Hdisj HfrA Hfrw Hwstk Hwv HInb Hphi4096 Hphiall Hlen0
      HSW0 Hshk Hcell Hc56 Hc57 Hc58 Hc59 Hc60 Hc66 Hvb0 Hvl0 Hv1 Hb56 Hb57 Hb58 Hb59 Hb60 Hb66 Hpres1 Hsh1
      Hpresv HW3sh MU1' HPM1 HadV1 HadW1 HadBC HadBC1 Hkeepfr Hg501 Ho1 Hstkw1 HAC1 HSW1 HRB1 HRM1 HGC1 HC2541
      HC2551 HTLS1 HTLSc HFPc AC2 TL2 HSTK1 HRT1 HAG HWA Hwin Hr4 Hr8 Hr3 Hr19 Hr26 HAm Hhalt Hg50 HPHIAP
      Hloc Hloc2 HHB Hphiad HAH HadU HadR HadF HadFi HKNT Hphish.
    (* outside the callee's write set: an application byte away from its four application ranges *)
    assert (HFSa : FS + 2134016 < APPMEM_END).
    { pose proof (HFSapp (FS + 2134016) ltac:(unfold AC.FS_SIZE in *; lia)) as Hx.
      unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hx. lia. }
    assert (HW2app : forall x, app_mem x -> ~ (fr + 448 <= x < fr + 484) -> ~ (fr + 528 <= x < fr + 532) ->
              ~ (sp - 8864 <= x < sp) -> (x < FS + 8 \/ FS + 2134016 <= x) ->
              Frame.outside ([(fr + 448, fr + 484); (fr + 528, fr + 532); (sp - 8864, sp)] ++
                 fp_w [1%nat] FS ++ [(shadow_addr (sp - 8864), shadow_addr sp)]) x).
    { intros x Hax H1 H2 H3 H4. rewrite (f30_fpw1 FS). cbn [Frame.outside app].
      assert (HnotSh : forall x0 x1, 0 <= x0 -> x1 < APPMEM_END -> ~ (shadow_addr x0 <= x < shadow_addr x1)).
      { intros x0 x1 Hx0 Hx1 Hc. pose proof (f30_sh_band x0 x1 x Hx0 Hx1 Hc) as Hb.
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
      split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [apply (HnotSh (FS + 1085440) (FS + 2134016)); lia|].
      split; [apply (HnotSh (sp - 8864) sp); unfold APPMEM_END in *; lia | exact I]. }
    assert (HW2sh : forall x, in_shadow x ->
              ~ (shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016)) ->
              ~ (shadow_addr (sp - 8864) <= x < shadow_addr sp) ->
              Frame.outside ([(fr + 448, fr + 484); (fr + 528, fr + 532); (sp - 8864, sp)] ++
                 fp_w [1%nat] FS ++ [(shadow_addr (sp - 8864), shadow_addr sp)]) x).
    { intros x Hsx H1 H2. rewrite (f30_fpw1 FS). cbn [Frame.outside app].
      split; [intros Hc; exact (app_not_shadow x (Happ x ltac:(lia)) Hsx)|].
      split; [intros Hc; exact (app_not_shadow x (Happ x ltac:(lia)) Hsx)|].
      split; [intros Hc; apply (app_not_shadow x); [unfold app_mem; right;
                unfold APPMEM_END in *; lia | exact Hsx]|].
      split; [intros Hc; exact (app_not_shadow x (HFSapp x ltac:(unfold AC.FS_SIZE in *; lia)) Hsx)|].
      split; [intros Hc; exact (app_not_shadow x (HFSapp x ltac:(unfold AC.FS_SIZE in *; lia)) Hsx)|].
      split; [intros Hc; exact (app_not_shadow x (HFSapp x ltac:(unfold AC.FS_SIZE in *; lia)) Hsx)|].
      split; [exact H1|]. split; [exact H2 | exact I]. }
    (* the frame's shadow bytes and the spill area are outside it *)
    assert (HshFr : forall y, fr <= y < fr + FRAME_BYTES -> Sfr fr <= shadow_addr y < Sfr fr + FRAME_SHADOW).
    { intros y Hy. unfold Sfr, shadow_addr. clear -Hy Hfr0 Hfr8 HFBv HFSv. Z.div_mod_to_equations. lia. }
    assert (HshFrOut : forall y, fr <= y < fr + FRAME_BYTES -> Frame.outside
              ([(fr + 448, fr + 484); (fr + 528, fr + 532); (sp - 8864, sp)] ++
               fp_w [1%nat] FS ++ [(shadow_addr (sp - 8864), shadow_addr sp)]) (shadow_addr y)).
    { intros y Hy. pose proof (HshFr y Hy) as Hb.
      apply HW2sh; [apply shadow_of_app; apply Happ; lia | |].
      - intros Hc. pose proof (f30_sh_mono (FS + 2134016) fr ltac:(lia)) as Hm.
        unfold Sfr in Hb. clear -Hb Hc Hm. lia.
      - intros Hc. destruct Hfrsp as [HD|HD].
        + assert (E392 : shadow_addr (fr + FRAME_BYTES) = Sfr fr + FRAME_SHADOW)
            by (apply (f30_sh_off fr FRAME_BYTES FRAME_SHADOW); [lia | exact Hfr8 | lia]).
          pose proof (f30_sh_mono (fr + FRAME_BYTES) (sp - 8864) HD) as Hm.
          unfold Sfr in Hb, E392. clear -Hb Hc Hm E392. lia.
        + pose proof (f30_sh_mono sp fr HD) as Hm.
          unfold Sfr in Hb. clear -Hb Hc Hm. lia. }
    assert (HAout2 : forall x, A <= x < A + 448 -> Frame.outside
              ([(fr + 448, fr + 484); (fr + 528, fr + 532); (sp - 8864, sp)] ++
               fp_w [1%nat] FS ++ [(shadow_addr (sp - 8864), shadow_addr sp)]) x).
    { intros x Hx. apply HW2app.
      - unfold app_mem. right. unfold APPMEM_END, HIGHMEM_BEG in *. lia.
      - lia. - lia. - lia.
      - right. unfold AC.FS_SIZE in *. lia. }
    assert (HAout1 : forall x, A <= x < A + 448 ->
              Frame.outside [(Sfr fr + 56, Sfr fr + 61); (Sfr fr + 66, Sfr fr + 67);
                             (fr + 528, fr + 532)] x).
    { intros x Hx. apply HW3app; [unfold app_mem; right; unfold APPMEM_END, HIGHMEM_BEG in *; lia | lia]. }
    assert (Hq2 : forall off v, 0 <= off <= 440 -> q64 mem (A + off) v -> q64 m2 (A + off) v).
    { intros off v Hoff Hq. unfold q64 in *.
      eapply fl_bytes; [|exact MU2|].
      - eapply fl_bytes; [exact Hq | exact MU1 |].
        rewrite length_le8. intros x Hx. apply HAout1. lia.
      - rewrite length_le8. intros x Hx. apply HAout2. lia. }
    (* the input buffer at the return *)
    assert (Hphiout2 : forall i, 0 <= i < AC.a_size (flen g j) -> Frame.outside
              ([(fr + 448, fr + 484); (fr + 528, fr + 532); (sp - 8864, sp)] ++
               fp_w [1%nat] FS ++ [(shadow_addr (sp - 8864), shadow_addr sp)]) (phi + i)).
    { intros i Hi. apply HW2app.
      - apply Hphiapp; exact Hi.
      - intros Hc. apply (Hphifr i Hi). lia.
      - intros Hc. apply (Hphifr i Hi). lia.
      - rewrite Hasz in Hi. lia.
      - destruct (Z_lt_ge_dec (phi + i) (FS + 8)) as [L|L]; [left; exact L|].
        right. destruct (Z_lt_ge_dec (phi + i) (FS + 2134016)) as [L2|L2]; [|lia].
        exfalso. apply (HphiFS i Hi). lia. }
    assert (Hphishout2 : forall i, 0 <= i < AC.a_size (flen g j) -> Frame.outside
              ([(fr + 448, fr + 484); (fr + 528, fr + 532); (sp - 8864, sp)] ++
               fp_w [1%nat] FS ++ [(shadow_addr (sp - 8864), shadow_addr sp)]) (shadow_addr (phi + i))).
    { intros i Hi. apply HW2sh; [apply shadow_of_app; apply Hphiapp; exact Hi | |].
      - intros Hc. pose proof (f30_sh_inv (FS + 1085440) (FS + 2134016) (phi + i) Hc) as Hb.
        apply (HphiFS i Hi). lia.
      - intros Hc. pose proof (f30_sh_inv (sp - 8864) sp (phi + i) Hc) as Hb.
        rewrite Hasz in Hi. lia. }
    (* the side stack's metadata (below the frames, FS + 36864) is outside the callee's writes unless it is the
       class-1 hint word or a class-1 flag byte *)
    assert (HW2fs : forall x, FS <= x < FS + 36864 ->
              ~ (FS + 8 <= x < FS + 16) -> ~ (FS + 20480 <= x < FS + 28672) ->
              Frame.outside ([(fr + 448, fr + 484); (fr + 528, fr + 532); (sp - 8864, sp)] ++
                 fp_w [1%nat] FS ++ [(shadow_addr (sp - 8864), shadow_addr sp)]) x).
    { intros x Hx H1 H2. rewrite (f30_fpw1 FS). cbn [Frame.outside app].
      assert (Hax : app_mem x) by (apply HFSapp; lia).
      assert (HnotSh : forall x0 x1, 0 <= x0 -> x1 < APPMEM_END -> ~ (shadow_addr x0 <= x < shadow_addr x1)).
      { intros x0 x1 Hx0 Hx1 Hc. pose proof (f30_sh_band x0 x1 x Hx0 Hx1 Hc) as Hb.
        unfold app_mem in Hax. lia. }
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [apply (HnotSh (FS + 1085440) (FS + 2134016)); lia|].
      split; [apply (HnotSh (sp - 8864) sp); lia | exact I]. }
    assert (Hfsok1 : AC.a_fs_ok m1 FS).
    { exact (lw_fs_ok (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) m1 md FS HAH1 Hwm1 HFSr). }
    pose proof FP2 as FP2b.
    destruct FP2b as (DT2 & TS2 & C2 & T2 & DB2 & k2 & HT2 & HTP2 & HP2 & H882 & H962 & HCL2 & HFSlo2 & HAp2 &
                      HWd2 & HDd2).
    assert (Hfsok2 : AC.a_fs_ok m2 FS).
    { eapply (f30_fsok2 m1 m2 FS _ Hfsok1 MU2).
      - intros cc Hcc Hcc1 q Hq.
        destruct (f30_cls_apart FS cc 0 Hcc Hcc1
                    ltac:(split; [lia | unfold AC.a_fs_M; apply Z.pow_pos_nonneg; lia])) as (Hh & _).
        unfold AC.a_fs_hint in Hq, Hh.
        assert (Hc10 : Z.of_nat cc <= 10) by lia.
        apply HW2fs; lia.
      - intros cc jj Hcc Hcc1 Hjj.
        destruct (f30_cls_apart FS cc jj Hcc Hcc1 Hjj) as (_ & Hf).
        pose proof (Tac_fs.a_fs_flag_range FS cc jj Hcc Hjj) as Hrng.
        assert (Hfl0 : FS + 4096 <= AC.a_fs_flag FS cc jj).
        { unfold AC.a_fs_flag. assert (Hp1 : 2 ^ (15 - Z.of_nat cc) <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
          change (2 ^ 15) with 32768 in Hp1 |- *. lia. }
        apply HW2fs; lia.
      - destruct HP2 as (_ & _ & _ & _ & HP2s). unfold ASM.FS_SIZE in HP2s. unfold AC.FS_SIZE. exact HP2s.
      - exact H882.
      - exact H962.
      - rewrite Forall_forall in HCL2. apply HCL2. cbn [In]. tauto.
      - lia.
      - unfold AC.FS_SIZE. lia. }
    assert (Hpo2 : forall x, fr + 448 <= x < fr + 484 -> exists b, mrd rsegs m2 (wa x) = Some b).
    { intros x Hx. destruct HO2 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
      destruct (f30_ba_some m2 (fr + 448) (t_B (g_in g) j) (x - (fr + 448)) Hb
                  ltac:(rewrite f30_B_length; lia)) as (b & Hb2).
      exists b. replace (fr + 448 + (x - (fr + 448))) with x in Hb2 by lia. exact Hb2. }
    assert (Hpv2 : forall x, fr + 528 <= x < fr + 532 -> exists b, mrd rsegs m2 (wa x) = Some b).
    { intros x Hx. destruct HV2 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
      destruct (f30_ba_some m2 (fr + 528)
                  (CLU.reac_ctrl_classify_box_frame_ev (t_cls (g_in g) j) vb1) (x - (fr + 528)) Hb
                  ltac:(unfold CLU.reac_ctrl_classify_box_frame_ev;
                        destruct (t_cls (g_in g) j);
                        [rewrite length_le4 | rewrite Hvl1]; lia)) as (b & Hb2).
      exists b. replace (fr + 528 + (x - (fr + 528))) with x in Hb2 by lia. exact Hb2. }
    (* the facts the next segment reads, at the return *)
    assert (HFE2 : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j)))
              (mkR (Z_to_bv 64 0x82af8) (getr regs 2) (getr regs 3) (getr regs 4) t0' t1' t2'
                 (getr regs 8) (getr regs 9) (Z_to_bv 64 (RC.cl_r (t_cls (g_in g) j)))
                 a1' a2' a3' a4' a5' a6' a7' (getr regs 18) (getr regs 19) (getr regs 20)
                 (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
                 (getr regs 26) (getr regs 27) t3' t4' t5' t6') m2 md /\
              ENT APIf g (hb1 phi (AC.a_size (flen g j))) m2 md).
    { eapply (f30_fra2 g fr (hb1 phi (AC.a_size (flen g j))) _ _ m1 m2 md FS HFRA1 HENT1); try reflexivity.
      - exact Hwm1.
      - exact HFSr.
      - exact HFSfr.
      - rewrite Haspz. exact MU2.
      - exact WM2.
      - exact HroM2.
      - exact SW2.
      - exact Hfsok2.
      - rewrite Haspz. exact ST2.
      - rewrite Haspz. exact AW2.
      - intros x Hx. exact (Hpo2 x Hx).
      - intros x Hx. exact (Hpv2 x Hx). }
    destruct HFE2 as (HFRA2 & HENT2).
    assert (HHB2 : HB m2 phi (flen g j)).
    { split; [exact Hphi0|].
      refine (f30_addr_keep _ m1 m2 phi _ Hphiad1 MU2 _).
      intros i Hi. exact (Hphishout2 i Hi). }
    assert (HOUR2 : OURb g fr m2).
    { unfold OURb in *. eapply fl_bytes; [exact HOUR1 | exact MU2 |].
      rewrite OUR_length. intros x Hx. apply HW2app.
      - apply Happ; lia. - lia. - lia. - lia. - right. lia. }
    assert (HBo2 : bytes_at rsegs m2 (fr + 448) (t_B (g_in g) j)).
    { destruct HO2 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
    assert (HadL2 : addressable m2 (fr + 452) 6).
    { refine (f30_addr_keep _ m1 m2 (fr + 452) 6 _ MU2 _).
      - destruct HadO1 as (P1 & P2 & P3 & P4). split; [lia|]. split; [lia|]. split; [lia|].
        intros i Hi. replace (fr + 452 + i) with (fr + 448 + (4 + i)) by lia. apply P4. lia.
      - intros i Hi. apply HshFrOut. lia. }
    assert (HadU2 : addressable m2 (fr + 2624) 6).
    { refine (f30_addr_keep _ m1 m2 (fr + 2624) 6 HadU1 MU2 _).
      intros i Hi. apply HshFrOut. lia. }
    assert (HadR2 : addressable m2 (fr + 2688) 38).
    { refine (f30_addr_keep _ m1 m2 (fr + 2688) 38 HadR1 MU2 _).
      intros i Hi. apply HshFrOut. lia. }
    assert (HadF2 : addressable m2 (fragb fr) 72).
    { refine (f30_addr_keep _ m1 m2 (fragb fr) 72 HadF1 MU2 _).
      intros i Hi. apply HshFrOut. unfold fragb. lia. }
    assert (HadFi2 : addressable m2 (fr + 2880) 40).
    { refine (f30_addr_keep _ m1 m2 (fr + 2880) 40 HadFi1 MU2 _).
      intros i Hi. apply HshFrOut. lia. }
    assert (Hev2 : forall e, t_cls (g_in g) j = Some e -> u32 m2 (fr + 528) e).
    { intros e He. destruct HV2 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
      unfold CLU.reac_ctrl_classify_box_frame_ev in Hb.
      change (RC.classify (flen g j) (t_g (g_in g) j) (OUR (g_in g))) with (t_cls (g_in g) j) in Hb.
      rewrite He in Hb. unfold u32. exact Hb. }
    assert (Hphib2 : bytes_at rsegs m2 phi (t_phi (g_in g) j)).
    { eapply fl_bytes; [exact Hphib1 | exact MU2 |].
      intros x Hx. pose proof (Hphiout2 (x - phi) ltac:(rewrite Hasz; lia)) as Ho.
      replace (phi + (x - phi)) with x in Ho by lia. exact Ho. }
    assert (Hfstk2 : stk rsegs m2 fr (fr + FRAME_BYTES)).
    { eapply (CLP.fl_stk _ m1 m2 fr (fr + FRAME_BYTES)); [exact Hfstk1 | exact MU2 | exact WM2 |].
      intros x Hx.
      destruct (Z_le_gt_dec (fr + 448) x) as [M1|M1]; [destruct (Z_lt_ge_dec x (fr + 484)) as [M2|M2]|].
      - right. exact (Hpo2 x ltac:(lia)).
      - destruct (Z_le_gt_dec (fr + 528) x) as [N1|N1]; [destruct (Z_lt_ge_dec x (fr + 532)) as [N2|N2]|].
        + right. exact (Hpv2 x ltac:(lia)).
        + left. apply HW2app; [apply Happ; lia | lia | lia | lia | right; lia].
        + left. apply HW2app; [apply Happ; lia | lia | lia | lia | right; lia].
      - destruct (Z_le_gt_dec (fr + 528) x) as [N1|N1]; [destruct (Z_lt_ge_dec x (fr + 532)) as [N2|N2]|].
        + right. exact (Hpv2 x ltac:(lia)).
        + left. apply HW2app; [apply Happ; lia | lia | lia | lia | right; lia].
        + left. apply HW2app; [apply Happ; lia | lia | lia | lia | right; lia]. }
    (* the kind-name table: the callee writes the frame cells o / v, its stack window, the side stack's frame and
       their shadow, all at or above GT *)
    assert (HKNT2 : KNT m2).
    { apply (f30_knt_keep _ m1 m2 HKNT1 MU2). intros xk Hxk. unfold KNC.KIND_NAME in Hxk. split.
      - apply HW2app; [unfold app_mem, LOWMEM_END; left; lia | | | | left];
          clear - Hxk HGTfr HGTFS Hsphi; unfold AC.GT, HIGHMEM_BEG in *; lia.
      - apply HW2sh; [apply shadow_of_app; unfold app_mem, LOWMEM_END; left; lia | |]; intros Hc.
        + clear - Hc Hxk HGTFS. unfold shadow_addr, AC.GT in *. Z.div_mod_to_equations. lia.
        + clear - Hc Hxk Hsphi. unfold shadow_addr, HIGHMEM_BEG in *. Z.div_mod_to_equations. lia. }
    (* the turn's two frame records and the local `first`, [fr + 2688, fr + 2920) (frame bytes off the stores'
       event word and off the callee's writes), and `first`'s 40 addressable bytes *)
    assert (HIFS2 : IFS g fr (S j) regs m2).
    { apply (f30_IFS_tr g fr (S j) regs regs mem m2 HIFS); [|exact HadFi2].
      intros x Hx.
      rewrite (f30_mbyte_munch _ m1 m2 x MU2 ltac:(lia)
                 (HW2app x ltac:(apply Happ; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(right; lia))).
      exact (f30_mbyte_munch _ mem m1 x MU1 ltac:(lia) (HW3app x ltac:(apply Happ; lia) ltac:(lia))). }
    apply evt_done.
    do 3 eexists. split; [reflexivity|].
    split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [exact HFRA2|].
    split; [exact HENT2|].
    split; [exact HHB2|].
    split; [exact HOUR2|].
    split; [exact Hq2|].
    split; [exact HBo2|].
    split; [exact HadL2|].
    split; [exact HadU2|].
    split; [exact HadR2|].
    split; [exact HadF2|].
    split; [exact HadFi2|].
    split; [exact Hev2|].
    split; [exact Hphib2|]. split; [exact Hfstk2|]. split; [exact HKNT2 | exact HIFS2].
  - intros R0 pc' m2 regs' md' (Hpc & E2 & E3 & E4 & E8 & E9 & E19 & E26 & E18 & E20 & E25 & E22 & E24 & E27 &
      E10 & HFRA2 & HENT2 & HHB2 & HOUR2 & Hq2 & HBo2 & HadL2 & HadU2 & HadR2 & HadF2 & HadFi2 & Hev2 & Hphib2 &
      Hfstk2 & HKNT2 & HIFS2) Hreg Hmat.
    subst pc'.
    clear - Hexit SEGS Hreg Hmat E2 E3 E4 E8 E9 E19 E26 E18 E20 E25 E22 E24 E27 E10 HFRA2 HENT2 HHB2 HOUR2 Hq2
      HBo2 HadL2 HadU2 HadR2 HadF2 HadFi2 Hev2 Hphib2 Hfstk2 HKNT2 HIFS2 Hgn Hj HLK HFLI Hr9 Hs144 Hs152 Hs160
      Hs192 Hs216 Hs264 Hs184 Hs312 Hs224 Hs232 Hs272 Hr18 Hr20 Hr25 Hr22 Hr24 Hplen HA64 HFBv HFSv.
    (* a spill of the entry memory is a spill of the return memory (s1 kept, [A, A + 448) not written) *)
    assert (Hsp : forall off v, 0 <= off <= 440 -> spill regs mem off v -> spill regs' m2 off v).
    { intros off v Ho Hs.
      pose proof (f30_spill regs mem off v A Hs Hr9 ltac:(lia) ltac:(lia) Ho) as Hq.
      exists A. split; [unfold rg in *; rewrite Hreg, E9; exact Hr9 | exact (Hq2 off v Ho Hq)]. }
    assert (HIexit : Inv_B82af8_at B APIf ra g j
                       (mkCfg (mkst regs' (Z_to_bv 64 0x82af8) m2 (seg_rom rsegs)) md')).
    { exists phi, regs', m2, md', fr. rewrite SEGS. split; [reflexivity|].
      split.
      { apply (sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) R0 regs' m2 md md' HFRA2);
          [apply Hreg | apply Hreg | apply Hreg | apply Hreg | apply Hreg | apply Hreg | apply Hreg
          | exact Hmat]. }
      split; [eapply ent_mat; [exact HENT2 | exact Hmat]|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB2|].
      split.
      { eapply Tac_ro.lk_keep;
          [exact HLK | | exact HadU2 | exact Hfstk2 | exact HadR2 | exact HadF2 | exact HKNT2 | exact HadFi2
          | exact HOUR2 |].
        - unfold rg in *. rewrite Hreg, E27. exact (proj1 HFLI).
        - intros off v Ho Hs. apply Hsp; [lia | exact Hs]. }
      split.
      { split; [apply Hsp; [lia | exact Hs184]|].
        split; [unfold rg in *; rewrite Hreg, E22; exact Hr22|].
        split; [unfold rg in *; rewrite Hreg, E24; exact Hr24|].
        split; [apply Hsp; [lia | exact Hs272] | unfold rg in *; rewrite Hreg, E25; exact Hr25]. }
      split; [unfold rg; rewrite Hreg; exact E10|].
      split; [apply Hsp; [lia | exact Hs144]|].
      split; [apply Hsp; [lia | exact Hs264]|].
      split; [apply Hsp; [lia | exact Hs216]|].
      split; [exact HBo2|]. split; [exact HadL2|]. split; [exact HadU2|].
      split; [apply Hsp; [lia | exact Hs184]|].
      split; [unfold rg in *; rewrite Hreg, E25; exact Hr25|].
      split; [apply Hsp; [lia | exact Hs192]|].
      split; [exact Hev2|].
      split.
      { split; [unfold rg in *; rewrite Hreg, E18; exact Hr18|].
        split; [unfold rg in *; rewrite Hreg, E24; exact Hr24|].
        split; [unfold rg in *; rewrite Hreg, E20; exact Hr20|].
        split; [apply Hsp; [lia | exact Hs152]|].
        split; [apply Hsp; [lia | exact Hs312]|].
        split; [exact Hphib2|]. split; [exact Hplen|].
        split; [apply Hsp; [lia | exact Hs160]|].
        exact Hfstk2. }
      split.
      { split; [apply Hsp; [lia | exact Hs224]|]. split; [apply Hsp; [lia | exact Hs232]|].
        split; [exact Hphib2 | exact Hplen]. }
      apply (f30_IFS_tr g fr (S j) regs regs' m2 m2 HIFS2 (fun x _ => eq_refl) HadFi2). }
    pose proof (Hexit g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End F30.
