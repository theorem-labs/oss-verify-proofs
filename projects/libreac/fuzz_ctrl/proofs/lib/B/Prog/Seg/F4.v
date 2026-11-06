(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 1665 of its 1776 lines of code are new or changed and 900 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F5.v, with its numbers changed; 216 of its 323 lines of code are new or changed and 1669 lines of the source are left out. *)
(* Segment F4 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan build of libreac v1.9.0, image B), frame-loop turn j:
   0x81fbc (the return point of the first reac_ctrl_parse call 0x81fb8, long frame) to 0x82098 (the head of the
   32-byte block-sum loop, first turn). rule 24: no function proved (a slot segment). The image-B port of image A's
   seg_F4_d64 (lib/A Seg/F4.v, the 0x81d64 block), continued through the loop set-up that image B places before the
   loop head.

     0x81fbc mv   s8,a0          s8 = t_k j (the parse result, Inv_B81fbc_at's a0)
     0x81fc0 li   a0,-13 ; 0x81fc4 bgeu a0,s2,81fcc   UBSan: Phi + 12 does not wrap (Phi + 64 <= 2^64): taken
     0x81fcc addi a0,s2,12 ; srli ; add ; lb ; 0x81fdc bnez a1   the instrumented check of the byte Phi + 12: its
                                 shadow byte is 0 (the granule [Phi + 8, Phi + 16) lies in the addressable block
                                 HB(Phi), len >= 50), so neither the slow path 0x82dc8 nor the error call 0x830b0 runs
     0x81fe0 lbu  a0,0(a0) ; li a1,136 ; 0x81fe8 bne a0,a1,82068   the record byte 12 against 0x88
     byte 12 = 0x88:
       0x81fec li a0,-14 ; bgeu (taken) ; 0x81ff8 addi a0,s2,13 ; the same check of the byte Phi + 13 (shadow 0;
       slow path 0x82e34, error call 0x830d0)
       0x8200c lbu a0,0(a0) ; addi a0,a0,-25 ; seqz a0,a0 ; 0x82018 sd a0,272(s1) ; j 8206c
     byte 12 <> 0x88:
       0x82068 sd zero,272(s1)
     0x8206c li a7,32 ; li a1,0 ; addi t0,s2,18 ; li a0,-18 ; sub a0,a0,s2 ; addi a2,s2,18 ;
     0x82084 sltiu a3,a0,-17 ; neg a3,a3 ; and a3,a3,a0 ; li a4,32 ; mv a0,a2      the loop registers
   v1.9.0 against the patched image: the same instructions 0x70 bytes later, the slow paths and error calls at new
   addresses, the UBSan trap at 0x82fa0 (was 0x82f3c).
   Both arms store [A+272] = b2z (t_8819 j) (t_8819 j = t_big j && byte 12 = 0x88 && byte 13 = 0x19, and t_big j
   holds). The UBSan bound a0 = -18 - Phi is below 2^64 - 17, so a3 = -18 - Phi = -(Phi + 18). The only memory write
   is the spill word [A+272, A+280): FRA and ENT move by F5's c_fra_spill, the frame-loop bundles by c_lk_keep /
   c_fsj_keep / c_fturn_keep / c_rec0_keep / c_fps_keep. Entry and exit are the official Inv_B81fbc_at and
   Inv_B82098_at (217aa9d4cd9). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs F5.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
(* The value functions of the lib/Lib step engine (another loaded PropExec has the same short names). *)
Module LP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.

(* ================= arithmetic of the run ================= *)

Lemma f4_zxb_eq : forall (b : byte) x, x = bv_unsigned b -> zxb b = Z_to_bv 64 x.
Proof. intros b x ->. reflexivity. Qed.

Lemma f4_seqz : forall w : word, LP.v_sltiu w 1 = Z_to_bv 64 (if bv_unsigned w =? 0 then 1 else 0).
Proof.
  intros w. unfold LP.v_sltiu. change (bv_wrap 64 1) with 1%Z.
  pose proof (bv_unsigned_in_range 64 w) as Hr. unfold bv_modulus in Hr.
  replace (bv_unsigned w <? 1) with (bv_unsigned w =? 0)
    by (destruct (Z.eqb_spec (bv_unsigned w) 0); destruct (Z.ltb_spec (bv_unsigned w) 1); lia).
  destruct (bv_unsigned w =? 0); reflexivity.
Qed.

Lemma f4_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

(* `addi a0,a0,-25 ; seqz a0,a0` on a byte value: the 0/1 indicator of (byte = 25) (image A's f4_sub25). *)
Lemma f4_sub25 : forall v, 0 <= v < 256 -> (bv_unsigned (Z_to_bv 64 (v - 25)) =? 0) = (v =? 25).
Proof.
  intros v Hv. rewrite MState.unsigned_lit_wrap.
  destruct (Z.eqb_spec v 25) as [->|Hne].
  - replace (25 - 25) with 0 by lia. reflexivity.
  - apply Z.eqb_neq. destruct (Z_lt_le_dec v 25) as [Hlt|Hge].
    + replace ((v - 25) mod 2 ^ 64) with (v - 25 + 2 ^ 64); [lia|].
      symmetry. rewrite <- (Z.mod_add (v - 25) 1 (2 ^ 64)) by lia.
      rewrite Z.mul_1_l. apply Z.mod_small. lia.
    + rewrite Z.mod_small by lia. lia.
Qed.

Lemma f4_sub25b : forall v, 0 <= v < 256 -> (bv_unsigned (Z_to_bv 64 (v + -25)) =? 0) = (v =? 25).
Proof. intros v Hv. replace (v + -25) with (v - 25) by lia. exact (f4_sub25 v Hv). Qed.

(* `bltu` / `bgeu x,y` with y <= x (unsigned, x read mod 2^64): the less-than is false (F10's f10_ltu_false). *)
Lemma f4_ltu_false : forall x y, 0 <= y < 2 ^ 64 -> y <= x mod 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof.
  intros x y Hy Hxy. unfold bv_ltu. rewrite MState.unsigned_lit_wrap, (MState.unsigned_lit y) by lia.
  apply Z.ltb_ge. lia.
Qed.

(* The UBSan bound of the loop set-up: 0x82014 sltiu a3,a0,-17 with a0 = -18 - Phi below 2^64 - 17. *)
Lemma f4_sltiu17 : forall E i, bv_wrap 64 i = 18446744073709551599 -> E mod 2 ^ 64 < 18446744073709551599 ->
  LP.v_sltiu (Z_to_bv 64 E) i = Z_to_bv 64 1.
Proof.
  intros E i Hi HE. unfold LP.v_sltiu. rewrite MState.unsigned_lit_wrap, Hi.
  replace (E mod 2 ^ 64 <? 18446744073709551599) with true by (symmetry; apply Z.ltb_lt; exact HE).
  reflexivity.
Qed.

(* `and` with the all-ones word (0x82018 neg a3,a3 of the indicator 1) keeps the other operand. *)
Lemma f4_land_ones : forall x, 0 <= x < 2 ^ 64 -> Z.land 18446744073709551615 x = x.
Proof.
  intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma f4_land_ones_w : forall w : word, Z.land 18446744073709551615 (bv_unsigned w) = bv_unsigned w.
Proof.
  intros w. apply f4_land_ones. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in H. lia.
Qed.

(* Two 64-bit literals with the same value mod 2^64 are the same word. *)
Lemma f4_word_eq : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof. intros x y H. apply bv_eq. rewrite !MState.unsigned_lit_wrap. exact H. Qed.

(* The side conditions of the run: linear bounds with mod 2^64 terms. *)
Ltac f4_mlia := rewrite ?MState.unsigned_lit_wrap; change (2 ^ 64) with 18446744073709551616 in *;
  Z.div_mod_to_equations; lia.

(* The shadow byte of Phi + k is 0 when the block (Phi, L) with L >= 50 is addressable and the 8-byte granule of
   Phi + k lies inside [Phi, Phi + 50) (image A's f4_sh_at). *)
Lemma f4_sh_at : forall m phi L k, addressable m phi (AC.a_size L) -> 50 <= L -> 7 <= k <= 42 ->
  bytes_at rsegs m (Z.shiftr (phi + k) 3 + ASAN_K) [Z_to_bv 8 0].
Proof.
  intros m phi L k HA HL Hk.
  pose proof HA as (Hp0 & _ & _ & _).
  pose proof (Z.mod_pos_bound (phi + k) 8 ltac:(lia)) as Hr.
  assert (H8 : addressable m (phi + (k - (phi + k) mod 8)) 8)
    by (apply (addressable_sub m phi (AC.a_size L)); [exact HA | lia | lia | unfold AC.a_size; lia]).
  destruct (meta8 m _ H8) as [[_ RB] _].
  assert (E : Z.shiftr (phi + (k - (phi + k) mod 8)) 3 = Z.shiftr (phi + k) 3).
  { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    pose proof (Z.div_mod (phi + k) 8 ltac:(lia)) as D.
    replace (phi + (k - (phi + k) mod 8)) with ((phi + k) / 8 * 8) by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  rewrite E in RB. exact RB.
Qed.

(* A one-byte carried cell as the read the engine consumes. *)
Lemma f4_rd1 : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b H. pose proof (bytes_at_ov_read rsegs m a [b] 0 1 H ltac:(cbn; lia)) as HH.
  change (Z.of_nat 0) with 0 in HH. rewrite Z.add_0_r in HH. cbn [firstn skipn] in HH. exact HH.
Qed.

(* One byte of a carried byte list as the read the engine consumes. *)
Lemma f4_rd_nth : forall m a (bs : list byte) (k : nat), bytes_at rsegs m a bs -> (k < length bs)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat k)) 1 = Some [nth k bs cp_z].
Proof.
  intros m a bs k H Hk. rewrite (bytes_at_ov_read rsegs m a bs k 1 H ltac:(lia)). f_equal. clear H.
  revert k Hk. induction bs as [|b bs IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in Hk. lia.
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The loop set-up 0x8206c-0x82094 and the landing at 0x82098 (both arms). *)
Local Ltac f4_tail p Hphib :=
  (* 0x8206c li a7,32 ; 0x82070 li a1,0 ; 0x82074 addi t0,s2,18 *)
  step; step; step; rewrite ?(MState.unsigned_lit p) by (clear - Hphib; lia);
  (* 0x82078 li a0,-18 ; 0x8207c sub a0,a0,s2 ; 0x82080 addi a2,s2,18 *)
  step; step; rewrite ?(MState.unsigned_lit p) by (clear - Hphib; lia);
  step; rewrite ?(MState.unsigned_lit p) by (clear - Hphib; lia);
  (* 0x82084 sltiu a3,a0,-17 : 1 (a0 = -(Phi + 18) is below 2^64 - 17) *)
  step;
  rewrite f4_sltiu17; [ | reflexivity | clear - Hphib; f4_mlia ];
  (* 0x82088 neg a3,a3 ; 0x8208c and a3,a3,a0 ; 0x82090 li a4,32 ; 0x82094 mv a0,a2 *)
  step; step; rewrite ?f4_land_ones_w;
  step; step;
  finish.

(* seg_F4 (S_F4) *)
Lemma seg_F4 : forall j : nat,
  Hat B APIf ra (Inv_B82098_at B APIf ra) j -> Hat B APIf ra (Inv_B81fbc_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & Hs2 & Hs4 & HFT &
    HLK & HFC & H22 & HFS & HREC & HFPS & Ha0 & H50).
  subst c. rewrite SEGS.
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5v & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hstkhigh.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  unfold flen in *.
  (* the live block (Phi, a_size len) below stklo *)
  destruct (c_lw_blocks (APIf rc) (hb1 phi (AC.a_size (t_len (g_in g) j)) ++ g_H g) mem md phi
              (AC.a_size (t_len (g_in g) j)) HAH ltac:(apply in_or_app; left; left; reflexivity))
    as (Hp16 & Hp4096 & Hpstk & _ & Hpall).
  assert (Hasz : t_len (g_in g) j <= AC.a_size (t_len (g_in g) j)) by (unfold AC.a_size; lia).
  pose proof HHB as (Hphinz & HAd).
  (* the record bytes and their shadow *)
  pose proof (fturn_g g j phi regs mem HFT H50) as HGb.
  assert (Hglen : length (t_g (g_in g) j) = 50%nat) by exact (c_tg_len (g_in g) j).
  pose proof (f4_sh_at mem phi (t_len (g_in g) j) 12 HAd H50 ltac:(lia)) as Hsh12.
  pose proof (f4_sh_at mem phi (t_len (g_in g) j) 13 HAd H50 ltac:(lia)) as Hsh13.
  pose proof (f4_rd1 mem _ _ Hsh12) as RDs12.
  pose proof (f4_rd1 mem _ _ Hsh13) as RDs13.
  pose proof (f4_rd_nth mem phi (t_g (g_in g) j) 12 HGb ltac:(rewrite Hglen; lia)) as RD12.
  pose proof (f4_rd_nth mem phi (t_g (g_in g) j) 13 HGb ltac:(rewrite Hglen; lia)) as RD13.
  change (Z.of_nat 12) with 12 in RD12. change (Z.of_nat 13) with 13 in RD13.
  assert (Hphib : 0 < phi /\ phi + 64 <= 2 ^ 64) by lia.
  assert (Hv12 : 0 <= cp_v (t_g (g_in g) j) 12 < 256) by apply c_byte_range.
  assert (Hv13 : 0 <= cp_v (t_g (g_in g) j) 13 < 256) by apply c_byte_range.
  assert (Hbig : t_big (g_in g) j = true) by (unfold t_big; apply Z.leb_le; lia).
  (* the spill word [A+272] is byte-backed and writable *)
  assert (HS272 : store_ok rsegs mem (wa (A + 272)) 8 = true).
  { apply (c_store_ok mem mem (A + 272) 8); [| apply wmono_refl | lia | lia].
    intros i Hi. destruct Hwin as (_ & _ & Hs). change (Z.of_nat 8) with 8 in Hi.
    exact (proj1 (Hs (A + 272 + i) ltac:(lia))). }
  set (m1 := write_to_mem mem (wa (A + 272)) (le8 (Z_to_bv 64 (b2z (t_8819 (g_in g) j))))).
  assert (HK : forall R0 pc' mem' regs' md',
    (pc' = Z_to_bv 64 0x82098 /\ mem' = m1 /\
     getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
     getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
     getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 22 = getr regs 22 /\
     getr R0 26 = getr regs 26 /\ getr R0 27 = getr regs 27 /\
     getr R0 24 = Z_to_bv 64 (t_k (g_in g) j) /\ getr R0 10 = Z_to_bv 64 (phi + 18) /\
     getr R0 11 = Z_to_bv 64 0 /\ getr R0 12 = Z_to_bv 64 (phi + 18) /\
     getr R0 13 = Z_to_bv 64 (- (phi + 18)) /\ getr R0 14 = Z_to_bv 64 32 /\ getr R0 17 = Z_to_bv 64 32 /\
     getr R0 5 = Z_to_bv 64 (phi + 18)) ->
    (forall r, getr regs' r = getr R0 r) -> AsanLift.mat_le md md' ->
    SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') (Post B APIf ra g)).
  { intros R0 pc' mem' regs' md' (Hpc & Hmem & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er20 & Er22 &
      Er26 & Er27 & Er24 & Er10 & Er11 & Er12 & Er13 & Er14 & Er17 & Er5) Hreg Hmat.
    subst pc' mem'.
    set (W := [(A + 272, A + 280)]).
    assert (MU : munch W mem m1).
    { subst m1 W. apply munch_write; [apply munch_refl | lia | rewrite length_le8; lia
        | rewrite length_le8; cbn [inside]; left; lia]. }
    assert (WM : wmono rsegs mem m1) by (subst m1; apply wmono_write; apply wmono_refl).
    assert (HWIN' : stk rsegs m1 (g_S g - AF.SLOT_STACK) (g_S g))
      by (subst m1; apply stk_write; [exact Hwin | lia | rewrite length_le8; lia]).
    assert (HAW : all_app W) by (subst W; cbn [all_app]; repeat split; try exact I; intros a Ha; unfold app_mem; right; lia).
    assert (HD : rt_disjoint W).
    { subst W. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN. cbn [disjoint_from]. repeat split; first [exact I | left; lia]. }
    assert (HWloc : forall x, ~ outside W x -> A + 72 <= x < A + 336).
    { intros x Hx. destruct (c_not_out W x Hx) as (r & Hin & Hr). subst W. cbn [In] in Hin.
      destruct Hin as [<-|[]]; cbn [fst snd] in Hr; lia. }
    assert (OW : forall x, ~ (A + 272 <= x < A + 280) -> outside W x)
      by (intros x H1; subst W; cbn [outside]; split; [exact H1 | exact I]).
    assert (OWlo : forall x, x < A + 272 -> outside W x /\ outside W (shadow_addr x)).
    { intros x Hx. split; [apply OW; lia|].
      destruct (Z_lt_le_dec x 0) as [Hn|Hp].
      - apply OW; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
      - assert (Hsx : shadow_addr x <= x / 8 + ASAN_K) by (unfold shadow_addr; lia).
        assert (Hx8 : x / 8 <= A / 8 + 34) by (Z.div_mod_to_equations; lia).
        assert (HA8 : A / 8 + ASAN_K + 34 < A) by (unfold ASAN_K; Z.div_mod_to_equations; lia).
        apply OW; lia. }
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact Er27).
    destruct (c_fra_spill B APIf ra empty FF g fr _ regs regs' mem m1 md md' A W HFRA HENT Hr9 HA64 MU WM HAW HD
                HWloc HWIN' Hmat Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26) as (HFRA'' & HENT'').
    assert (Q272 : q64 m1 (A + 272) (b2z (t_8819 (g_in g) j))).
    { subst m1. unfold q64. apply bytes_at_write_same; [lia | rewrite length_le8; lia]. }
    assert (HA448' : A + 448 <= 2 ^ 64) by lia.
    assert (H9' : rg regs' 9 A) by exact (c_rg_move regs regs' _ _ Hr9 Fr9).
    assert (Ofr : forall x, fr <= x < fr + FRAME_BYTES -> outside W x /\ outside W (shadow_addr x))
      by (intros x Hx; apply OWlo; lia).
    assert (Olo : forall x, 0 <= x < AC.GT -> outside W x /\ outside W (shadow_addr x))
      by (intros x Hx; apply OWlo; lia).
    rewrite <- SEGS. apply Hexit.
    exists phi, regs', m1, md', fr. unfold flen.
    split; [reflexivity|]. split; [exact HFRA''|]. split; [exact HENT''|].
    split; [exact Hgn|]. split; [exact Hj|].
    split.
    { split; [exact Hphinz|].
      apply (c_addr_keep W mem m1 phi _ HAd MU). intros i Hi. apply OWlo. lia. }
    split; [exact (c_rg_move regs regs' _ _ Hs2 Fr18)|].
    split; [exact (c_rg_move regs regs' _ _ Hs4 Fr20)|].
    split.
    { apply (c_fturn_keep g j phi A regs regs' mem m1 W HFT Hr9 ltac:(lia) HA448' Fr9 MU).
      - intros x Hx. apply OW; lia.
      - intros x Hx. apply OWlo. lia. }
    split.
    { apply (c_lk_keep g fr j A regs regs' mem m1 W HLK Hr9 ltac:(lia) HA448' Fr9 Fr27 MU WM).
      - intros x _ _ _ H1 _. exact (OW x H1).
      - exact Ofr.
      - exact Olo. }
    split; [exact (c_rg_move regs regs' _ _ H22 Fr22)|].
    split.
    { exact (c_fsj_keep g fr j regs regs' mem m1 W HFS MU Ofr). }
    split; [exact (c_rec0_keep g fr j W mem m1 HREC MU (fun x Hx => proj1 (Ofr x Hx)))|].
    split; [exact (c_fps_keep g fr j W mem m1 HFPS MU Ofr)|].
    split; [unfold F272; exists A; split; [exact H9' | exact Q272]|].
    split; [exact H50|].
    split; [unfold rg; rewrite Hreg; exact Er24|].
    split; [unfold a0v, rg; rewrite Hreg; exact Er10|].
    split; [unfold rg; rewrite Hreg; exact Er11|].
    split; [unfold rg; rewrite Hreg; exact Er12|].
    split; [unfold rg; rewrite Hreg; exact Er13|].
    split; [unfold rg; rewrite Hreg; exact Er14|].
    split; [unfold rg; rewrite Hreg; exact Er17|].
    unfold rg; rewrite Hreg; exact Er5. }
  destruct (Z.eq_dec (cp_v (t_g (g_in g) j) 12) 136) as [H12eq|H12ne].
  - (* ---- byte 12 is 0x88: the check of byte 13 and [A+272] = (byte 13 = 0x19) ---- *)
    assert (H8819 : b2z (t_8819 (g_in g) j) = (if cp_v (t_g (g_in g) j) 13 =? 25 then 1 else 0)).
    { unfold b2z, t_8819. rewrite Hbig.
      replace (cp_v (t_g (g_in g) j) 12 =? 0x88) with true by (symmetry; apply Z.eqb_eq; exact H12eq).
      cbn [andb]. change 0x19 with 25. destruct (cp_v (t_g (g_in g) j) 13 =? 25); reflexivity. }
    refine (c_run_lib regs (Z_to_bv 64 0x81fbc) mem md _ (Post B APIf ra g) Hhalt _ HK).
    rewrite c_mkR_expand. unfold a0v in Ha0. c_slot Ha0. c_slot Hs2. c_slot Hr9. c_slot Hr26.
    (* 0x81fbc mv s8,a0 ; 0x81fc0 li a0,-13 ; 0x81fc4 bgeu a0,s2 : taken *)
    step. step. step.
    rewrite (f4_ltu_false _ phi) by (clear - Hphib; f4_mlia). cbn [negb]. cbv iota.
    (* 0x81fcc addi a0,s2,12 ; srli a1,a0,3 ; add a1,a1,s10 ; lb a1 : shadow 0 ; bnez a1 : not taken *)
    step. rewrite ?(MState.unsigned_lit phi) by (clear - Hphib; lia).
    step. step. rewrite ?(MState.unsigned_lit (phi + 12)) by (clear - Hphib; lia).
    step.
    replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    step. try rewrite bv_eqb_refl. cbn [negb]. cbv iota.
    (* 0x81fe0 lbu a0,0(a0) ; li a1,136 ; bne a0,a1 : not taken *)
    step. step. step.
    rewrite (f4_zxb_eq (nth 12 (t_g (g_in g) j) cp_z) (cp_v (t_g (g_in g) j) 12)) by reflexivity.
    rewrite (f4_eqb_lit (cp_v (t_g (g_in g) j) 12) 136) by lia.
    replace (cp_v (t_g (g_in g) j) 12 =? 136) with true by (symmetry; apply Z.eqb_eq; exact H12eq).
    cbn [negb]. cbv iota.
    (* 0x81fec li a0,-14 ; bgeu a0,s2 : taken *)
    step. step.
    rewrite (f4_ltu_false _ phi) by (clear - Hphib; f4_mlia). cbn [negb]. cbv iota.
    (* 0x81ff8 addi a0,s2,13 ; srli ; add ; lb : shadow 0 ; bnez : not taken *)
    step. rewrite ?(MState.unsigned_lit phi) by (clear - Hphib; lia).
    step. step. rewrite ?(MState.unsigned_lit (phi + 13)) by (clear - Hphib; lia).
    step.
    replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    step. try rewrite bv_eqb_refl. cbn [negb]. cbv iota.
    (* 0x8200c lbu a0,0(a0) ; addi a0,a0,-25 ; seqz a0,a0 *)
    step.
    rewrite (f4_zxb_eq (nth 13 (t_g (g_in g) j) cp_z) (cp_v (t_g (g_in g) j) 13)) by reflexivity.
    step. rewrite ?(MState.unsigned_lit (cp_v (t_g (g_in g) j) 13)) by lia.
    step. rewrite f4_seqz.
    (* 0x82018 sd a0,272(s1) ; 0x8201c j 8206c *)
    step. step.
    f4_tail phi Hphib.
    all: try (subst m1; rewrite H8819; do 3 f_equal; rewrite f4_sub25b by lia; reflexivity).
    all: try (symmetry; first [exact Hs2 | exact Hr9 | exact Hr26]).
    all: try (apply f4_word_eq; clear - Hphib; f4_mlia).
    all: try reflexivity.
  - (* ---- byte 12 is not 0x88: [A+272] = 0 ---- *)
    assert (H8819f : t_8819 (g_in g) j = false).
    { unfold t_8819.
      replace (cp_v (t_g (g_in g) j) 12 =? 0x88) with false by (symmetry; apply Z.eqb_neq; exact H12ne).
      rewrite andb_false_r. rewrite andb_false_l. reflexivity. }
    refine (c_run_lib regs (Z_to_bv 64 0x81fbc) mem md _ (Post B APIf ra g) Hhalt _ HK).
    rewrite c_mkR_expand. unfold a0v in Ha0. c_slot Ha0. c_slot Hs2. c_slot Hr9. c_slot Hr26.
    step. step. step.
    rewrite (f4_ltu_false _ phi) by (clear - Hphib; f4_mlia). cbn [negb]. cbv iota.
    step. rewrite ?(MState.unsigned_lit phi) by (clear - Hphib; lia).
    step. step. rewrite ?(MState.unsigned_lit (phi + 12)) by (clear - Hphib; lia).
    step.
    replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    step. try rewrite bv_eqb_refl. cbn [negb]. cbv iota.
    step. step. step.
    rewrite (f4_zxb_eq (nth 12 (t_g (g_in g) j) cp_z) (cp_v (t_g (g_in g) j) 12)) by reflexivity.
    rewrite (f4_eqb_lit (cp_v (t_g (g_in g) j) 12) 136) by lia.
    replace (cp_v (t_g (g_in g) j) 12 =? 136) with false by (symmetry; apply Z.eqb_neq; exact H12ne).
    cbn [negb]. cbv iota.
    (* 0x82068 sd zero,272(s1) *)
    step.
    f4_tail phi Hphib.
    all: try (subst m1; rewrite H8819f; reflexivity).
    all: try (symmetry; first [exact Hs2 | exact Hr9 | exact Hr26]).
    all: try (apply f4_word_eq; clear - Hphib; f4_mlia).
    all: try reflexivity.
Qed.

End S.
