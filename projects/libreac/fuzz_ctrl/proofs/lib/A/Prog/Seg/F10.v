(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v; 262 of its 291 lines of code are new or changed and 367 lines of the source are left out. *)
(* Segment F10 (0x81ff4-0x82068 with the out-of-line slow path 0x829a8-0x829b0 and the error call 0x82cc4,
   plan-asan 2): the checks on the result of `jal reac_ctrl_identity_reply@0x81ff0`. The entry cut Inv_A81ff4_at is
   the return point of that call: a0 = reply_ret (the register clause of the post of
   reac_ctrl_identity_reply_contract, A/Prog/reac_ctrl_identity_reply_c.v:83) and, under reply_ok, the three reply
   cells at pa = fr+256, pp = fr+272, pn = fr+304 (the post's clause at reac_ctrl_identity_reply_c.v:90-93). The
   segment reads them back: `bltz a0` (0x81ff4) is not taken (reply_args holds, so a0 is 0 or 1); `bne a0,1`
   (0x81ffc) goes to Inv_A820fc_at when ir is false (a0 = 0); on a0 = 1 the five record tests 0x82004-0x82034 and
   0x82054 are not taken ([s1+280] = sum_ok = 1, [pp] = phi+38, [pn] = ir_s - 13, s6 = phi+18, the record byte
   phi+26 = ir_s), the instrumented check of the byte s6+8 = phi+26 (a load of the shadow byte at
   ((phi+26) >> 3) + K and a compare, 0x82038-0x82048) reads shadow byte 0 (the 8-byte granule of phi+26 lies inside
   the addressable heap block HB(phi), len >= 50), so neither the slow path 0x829a8 nor the error call 0x82cc4 is
   reached, and `beqz a1` (0x8205c, a1 = ir_s - 8 in [6, 15]) is not taken: the segment falls through to the
   record-sum loop head Inv_A8206c_at. The beqz exit Inv_A820ac_at is defined (the state at 0x820ac) but is not
   reached from this entry. No memory is written, so FRA moves by sl_fra_move alone. The three cuts are SlotInv's
   official texts; the identity record IDj moves unchanged to 0x8206c, and on the ir = false edge it is the stage-2
   record IDb1 of 0x820fc, because ID1 g j = rp_id (t_ID j) (flen g j) (t_g j) is t_ID j there (SlotModel.rp_id). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag RcParse RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module ULMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.
(* The cell vocabulary of the callee contracts (lib/Lib, as reac_ctrl_identity_reply_c.v states its post). *)
Module LCl := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LSt := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* Turn a carried `bytes_at` fact into the `ov_read_bytes _ _ _ n = Some bs` form the UL `step`/solve_load
   consumes (its HR branch). *)
Lemma f10_rd1 : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (ULMem.wa a) 1 = Some [b].
Proof.
  intros m a b H.
  pose proof (ULMem.bytes_at_ov_read rsegs m a [b] 0 1 H ltac:(cbn; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r in HH. cbn [firstn skipn] in HH. exact HH.
Qed.
Lemma f10_rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (ULMem.wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (ULMem.bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.
(* One byte k of a carried byte list. *)
Lemma f10_rdk : forall m a (bs : list byte) k, bytes_at rsegs m a bs -> (k < length bs)%nat ->
  ov_read_bytes rsegs m (ULMem.wa (a + Z.of_nat k)) 1 = Some [nth k bs cp_z].
Proof.
  intros m a bs k H Hk.
  rewrite (ULMem.bytes_at_ov_read rsegs m a bs k 1 H ltac:(lia)). f_equal.
  clear H. revert k Hk. induction bs as [|b bs IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in Hk. lia.
Qed.
(* An 8-byte reply cell of the contract post (lib/Lib cells) as carried bytes. *)
Lemma f10_lrw8 : forall m a v, LSt.rw_cells rsegs m a [LCl.CB 8 (le8 v)] -> bytes_at rsegs m a (le8 v).
Proof. intros m a v [[_ H] _]. cbn [LCl.cells_bytes LCl.cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

Lemma f10_eqb0_false : forall v, 0 < v < 2 ^ 64 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = false.
Proof.
  intros v Hv. apply Bool.not_true_iff_false. intro HC. apply bv_eqb_eq in HC.
  apply (f_equal bv_unsigned) in HC. rewrite !MState.unsigned_lit in HC by lia. lia.
Qed.
Lemma f10_ltu_false : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> y <= x ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros x y Hx Hy Hxy. unfold bv_ltu. rewrite !MState.unsigned_lit by lia. apply Z.ltb_ge. lia. Qed.
Lemma f10_sub_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) - bv_unsigned (Z_to_bv 64 y)) = Z_to_bv 64 (x - y).
Proof. intros x y Hx Hy. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.
Lemma f10_zxb_eq : forall (b : byte) x, x = bv_unsigned b -> zxb b = Z_to_bv 64 x.
Proof. intros b x ->. reflexivity. Qed.

(* The shadow byte of phi+26 is 0 when the heap block (phi, len) with len >= 50 is addressable: the whole 8-byte
   granule of phi+26 lies in [phi, phi+34) (AsanRTFacts.meta8 on the granule start). *)
Lemma f10_sh26 : forall m phi L, addressable m phi (AC.a_size L) -> 50 <= L ->
  bytes_at rsegs m (Z.shiftr (phi + 26) 3 + ASAN_K) [Z_to_bv 8 0].
Proof.
  intros m phi L HA HL.
  pose proof HA as (Hp0 & _ & _ & _).
  pose proof (Z.mod_pos_bound (phi + 26) 8 ltac:(lia)) as Hr.
  assert (H8 : addressable m (phi + (26 - (phi + 26) mod 8)) 8)
    by (apply (addressable_sub m phi (AC.a_size L)); [exact HA | lia | lia | unfold AC.a_size; lia]).
  destruct (meta8 m _ H8) as [[_ RB] _].
  assert (E : Z.shiftr (phi + (26 - (phi + 26) mod 8)) 3 = Z.shiftr (phi + 26) 3).
  { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    pose proof (Z.div_mod (phi + 26) 8 ltac:(lia)) as D.
    replace (phi + (26 - (phi + 26) mod 8)) with ((phi + 26) / 8 * 8) by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  rewrite E in RB. exact RB.
Qed.

(* mkR_of regs is definitionally the explicit 31-slot register map; exposing it lets `step` read a slot we have
   rewritten to a concrete value. *)
Lemma f10_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  Frame.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Rewrite a known register slot `getr regs r` to its carried concrete value, from H : rg regs r v. *)
Ltac f10_subst_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

(* The carried body moves across a register change with the memory unchanged (F10 writes none): every conjunct
   of FLSI (with its FLC spills) / LK / b5_C / b5_K and of the three push-13/14 carry bundles (b5_F17, b5_W240,
   b5_PF) reads the registers only through reg 2 (aspZ), 9 (the spill base, also of FSj's two first-fragment
   spills and of [A+200] / [A+240] / [A+72] / [A+64]), 18, 20, 21, 22, 23, 24 and 25, and F10 keeps all nine. *)
Lemma f10_keep : forall g j phi fr (regs regs' : bvmap 5 word) m,
  getr regs' 2 = getr regs 2 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 20 = getr regs 20 -> getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 ->
  getr regs' 23 = getr regs 23 -> getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 ->
  FLSI g j fr regs m -> LK g fr j regs m -> b5_C g j phi fr regs m -> b5_K g j phi fr regs m ->
  b5_F17 g j phi fr regs m -> b5_W240 g j regs m -> b5_PF g j phi fr regs m ->
  FLSI g j fr regs' m /\ LK g fr j regs' m /\ b5_C g j phi fr regs' m /\ b5_K g j phi fr regs' m /\
  b5_F17 g j phi fr regs' m /\ b5_W240 g j regs' m /\ b5_PF g j phi fr regs' m.
Proof.
  intros g j phi fr regs regs' m E2 E9 E18 E20 E21 E22 E23 E24 E25 HF HL HC HKk H17 H240 HPF.
  unfold FLSI, FLSH, PRO, FLC, LK, b5_C, b5_K, b5_PH, b5_sp, b5_F17, b5_W240, b5_PF, FSj, FSb, spill, rg,
    AC.aspZ in *.
  rewrite ?E2, ?E9, ?E18, ?E20, ?E21, ?E22, ?E23, ?E24, ?E25.
  split; [exact HF|]. split; [exact HL|]. split; [exact HC|]. split; [exact HKk|].
  split; [exact H17|]. split; [exact H240 | exact HPF].
Qed.

Lemma seg_F10 : forall j, Hat B APIf ra (Inv_A8206c_at B APIf ra) j ->
  Hat B APIf ra (Inv_A820ac_at B APIf ra) j ->
  Hat B APIf ra (Inv_A820fc_at B APIf ra) j -> Hat B APIf ra (Inv_A81ff4_at B APIf ra) j.
Proof.
  intros j Hx1 Hx2 Hx3 g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    Hgn & Hj & HHB & HFLSI & HLK & HbC & HbK & HbRC & Ha0 & Hpost & HID & H17 & H240 & HPF).
  subst c. rewrite SEGS.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (Af & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hrest).
  pose proof HbC as HbC2.
  destruct HbC2 as (Hs7 & Hs2 & (A & H9 & HA & HSP & Hq232) & HPH & HFR & HFS & HbKN & HFGj & HFSj).
  destruct HSP as (Hq248 & Hq256 & Hq144 & Hq184 & Hq208 & Hq64 & Hq72 & Hq80 & Hq272 & Hq264).
  pose proof HbK as HbK2.
  destruct HbK2 as (Hs4 & Hs6 & Hs8 & Hs9 & Hsp280 & Hu32 & Hargs).
  destruct HPH as (HGb & HPHp & HPHf).
  destruct HHB as (Hphi0 & HAd).
  pose proof HAd as (Hp0 & _ & Hpe & _). unfold AC.a_size, APPMEM_END in Hpe.
  (* the [A+280] spill base is the cut's own A *)
  assert (Hq280 : q64 mem (A + 280) (b2z (t_sum_ok (g_in g) j))).
  { destruct Hsp280 as (A' & HA' & HA'b & Hq'). 
    assert (EA' : A' = A).
    { assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in HA', H9; rewrite <- HA'; exact H9).
      apply (f_equal (bv_unsigned (n:=64))) in E. rewrite !MState.unsigned_lit in E by lia. exact E. }
    subst A'. exact Hq'. }
  destruct (ir (flen g j) (t_g (g_in g) j)) eqn:Hir.
  - (* ---- reply result a0 = 1 (reply_ok): fall through to 0x8206c ---- *)
    assert (Hok : reply_ok phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j) = true)
      by (unfold reply_ok; rewrite Hargs, Hir; reflexivity).
    assert (Hr1 : reply_ret phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j) = 1)
      by (unfold reply_ret; rewrite Hargs, Hir; reflexivity).
    rewrite Hr1 in Ha0.
    pose proof (Hpost Hok) as HRP.
    pose proof HRP as (RWa & RWp & RWn).
    destruct (ir_bytes _ _ Hir) as (H50 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsr & _ & _ & Hbs & _).
    assert (Hbig : t_big (g_in g) j = true) by (unfold t_big; apply Z.leb_le; exact H50).
    assert (Hsum : t_sum_ok (g_in g) j = true)
      by (unfold t_sum_ok; rewrite Hbig; unfold ir_blk in Hbs; rewrite Hbs; reflexivity).
    assert (Hs6' : rg regs 22 (phi + 18)) by (rewrite Hbig in Hs6; exact Hs6).
    assert (Hq280' : q64 mem (A + 280) 1) by (rewrite Hsum in Hq280; exact Hq280).
    pose proof (HGb H50) as HG.
    rewrite Z.max_l in Hpe by lia.
    pose proof (f10_sh26 mem phi (flen g j) HAd H50) as Hsh.
    pose proof (f10_rdk mem phi (t_g (g_in g) j) 26 HG ltac:(unfold t_g; rewrite fr50_length; lia)) as RD26.
    change (Z.of_nat 26) with 26 in RD26.
    assert (Hb26 : bv_unsigned (nth 26 (t_g (g_in g) j) cp_z) = ir_s (t_g (g_in g) j)) by reflexivity.
    revert RD26 Hb26. generalize (nth 26 (t_g (g_in g) j) cp_z) as b26. intros b26 RD26 Hb26.
    pose proof (f10_rd1 mem _ _ Hsh) as RDsh.
    pose proof (f10_rd8 mem _ _ Hq280' ltac:(apply length_le8)) as RD280.
    pose proof (f10_rd8 mem _ _ Hq272 ltac:(apply length_le8)) as RD272.
    pose proof (f10_rd8 mem _ _ Hq264 ltac:(apply length_le8)) as RD264.
    pose proof (f10_rd8 mem _ _ (f10_lrw8 _ _ _ RWp) ltac:(apply length_le8)) as RDpp.
    pose proof (f10_rd8 mem _ _ (f10_lrw8 _ _ _ RWn) ltac:(apply length_le8)) as RDpn.
    apply (sl_run regs (Z_to_bv 64 0x81ff4) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x8206c /\ mem' = mem /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\
         getr R 21 = getr regs 21 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
         getr R 9 = Z_to_bv 64 A /\ getr R 26 = Z_to_bv 64 ASAN_K /\ getr R 18 = Z_to_bv 64 (flen g j) /\
         getr R 22 = Z_to_bv 64 (phi + 18) /\ getr R 23 = Z_to_bv 64 phi /\
         getr R 10 = Z_to_bv 64 (phi + 34) /\ getr R 11 = Z_to_bv 64 (ir_s (t_g (g_in g) j) - 13 + 5) /\
         getr R 12 = Z_to_bv 64 (phi + 38) /\ getr R 13 = Z_to_bv 64 (ir_s (t_g (g_in g) j) - 13) /\
         getr R 14 = Z_to_bv 64 0 /\ getr R 15 = Z_to_bv 64 (phi + 34))
      (Post B APIf ra g)).
    + exact Hhalt.
    + rewrite f10_mkR_of_expand.
      f10_subst_slot Ha0. f10_subst_slot H9. f10_subst_slot Hs7. f10_subst_slot Hs2. f10_subst_slot Hs6'.
      f10_subst_slot Hr26.
      (* 0x81ff4 bltz a0 (a0 = 1) not taken ; 0x81ff8 li a1,1 ; 0x81ffc bne a0,a1 not taken *)
      step. if_false. step. step. if_false.
      (* 0x82000 ld a0,280(s1) = sum_ok = 1 ; 0x82004 beqz a0 not taken *)
      step. step. if_false.
      (* 0x82008 ld a0,272(s1) = pp ; 0x8200c ld a2,0(a0) = phi+38 ; 0x82010 bltu a2,s7 not taken *)
      step. step. step. rewrite (f10_ltu_false (phi + 38) phi) by lia. cbv_concl_iota.
      (* 0x82014 sub a0,a2,s7 = 38 ; 0x82018 bltu s2,a0 not taken (len >= 50) *)
      step. rewrite (f10_sub_lit (phi + 38) phi) by lia. replace (phi + 38 - phi) with 38 by lia.
      step. rewrite (f10_ltu_false (flen g j) 38) by lia. cbv_concl_iota.
      (* 0x8201c ld a1,264(s1) = pn ; 0x82020 ld a3,0(a1) = ir_s-13 ; 0x82024 addi a1,a3,2 ;
         0x82028 sub a0,s2,a0 = len-38 ; 0x8202c bltu a0,a1 not taken *)
      step. step. step. step. rewrite (MState.unsigned_lit (flen g j)) by lia.
      step. rewrite (f10_ltu_false (flen g j - 38) (ir_s (t_g (g_in g) j) - 13 + 2)) by lia. cbv_concl_iota.
      (* 0x82030 addi a0,s6,20 = phi+38 ; 0x82034 bne a2,a0 not taken *)
      step. step. rewrite bv_eqb_refl; cbn [negb]; cbv_concl_iota.
      (* 0x82038 addi a0,s6,8 ; srli ; add ; lb a1 = shadow byte of phi+26 = 0 ; 0x82048 bnez a1 not taken *)
      step. step. step. rewrite (MState.unsigned_lit (phi + 26)) by lia.
      step. step. if_false.
      (* 0x8204c lbu a0,0(a0) = b26 = ir_s ; 0x82050 addi a1,a3,13 ; 0x82054 bne a1,a0 not taken *)
      step. step. step.
      rewrite (f10_zxb_eq b26 (ir_s (t_g (g_in g) j) - 13 + 13)) by lia.
      rewrite bv_eqb_refl; cbn [negb]; cbv_concl_iota.
      (* 0x82058 addi a1,a3,5 ; 0x8205c beqz a1 not taken (a1 = ir_s - 8 in [6, 15]) *)
      step. step. rewrite (f10_eqb0_false (ir_s (t_g (g_in g) j) - 13 + 5)) by lia. cbv_concl_iota.
      (* 0x82060 li a4,0 ; 0x82064 addi a5,s6,16 ; 0x82068 addi a0,s6,16 ; land at 0x8206c *)
      step. step. step. finish. all: simp_regs; try reflexivity.
    + (* continuation: rebuild the exit cut Inv_A8206c_at and apply it *)
      intros R pc' mem' regs'' md'
        (Hpc & Hmem & HR2 & HR3 & HR4 & HR8 & HR19 & HR20 & HR21 & HR24 & HR25 & HR9 & HR26 & HR18 &
         HR22 & HR23 & HR10 & HR11 & HR12 & HR13 & HR14 & HR15) Hreg Hmat.
      subst pc' mem'. rewrite <- SEGS. apply Hx1.
      assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact HR2).
      assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg, HR9; unfold rg in H9; symmetry; exact H9).
      assert (E18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg, HR18; unfold rg in Hs2; symmetry; exact Hs2).
      assert (E20 : getr regs'' 20 = getr regs 20) by (rewrite Hreg; exact HR20).
      assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact HR21).
      assert (E22 : getr regs'' 22 = getr regs 22)
        by (rewrite Hreg, HR22; unfold rg in Hs6'; symmetry; exact Hs6').
      assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg, HR23; unfold rg in Hs7; symmetry; exact Hs7).
      assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact HR24).
      assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact HR25).
      destruct (f10_keep g j phi fr regs regs'' mem E2 E9 E18 E20 E21 E22 E23 E24 E25 HFLSI HLK HbC HbK
                  H17 H240 HPF)
        as (HFLSI' & HLK' & HbC' & HbK' & H17' & H240' & HPF').
      exists phi, regs'', mem, md', fr.
      split; [reflexivity|].
      split.
      { apply (sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs'' mem md md' HFRA);
          [ exact E2 | rewrite Hreg; exact HR3 | rewrite Hreg; exact HR4
          | rewrite Hreg; exact HR8 | exact E9 | rewrite Hreg; exact HR19
          | rewrite Hreg, HR26; unfold rg in Hr26; symmetry; exact Hr26
          | exact Hmat ]. }
      split; [ eapply ent_mat; [ exact HENT | exact Hmat ] |].
      split; [exact Hgn|].
      split; [exact Hj|].
      split; [split; [exact Hphi0 | exact HAd]|].
      split; [exact HFLSI'|].
      split; [exact HLK'|].
      split; [exact HbC'|].
      split; [exact HbK'|].
      split; [exact HbRC|].
      split; [exact H50|].
      split; [exact Hsum|].
      split; [exact Hok|].
      split; [exact HRP|].
      split; [ unfold rg; rewrite Hreg; exact HR10 |].
      split; [ unfold rg; rewrite Hreg, HR11; f_equal; lia |].
      split; [ unfold rg; rewrite Hreg; exact HR12 |].
      split; [ unfold rg; rewrite Hreg; exact HR13 |].
      split; [ unfold rg; rewrite Hreg; exact HR14 |].
      split; [ unfold rg; rewrite Hreg; exact HR15 |].
      split; [exact HID|].
      split; [exact H17'|]. split; [exact H240' | exact HPF'].
  - (* ---- reply result a0 = 0 (reply_args, ir false): `bne a0,a1` taken to 0x820fc ---- *)
    assert (Hr0 : reply_ret phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j) = 0)
      by (unfold reply_ret; rewrite Hargs, Hir; reflexivity).
    rewrite Hr0 in Ha0.
    apply (sl_run regs (Z_to_bv 64 0x81ff4) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x820fc /\ mem' = mem /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
         getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\
         getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\
         getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26)
      (Post B APIf ra g)).
    + exact Hhalt.
    + rewrite f10_mkR_of_expand. f10_subst_slot Ha0.
      (* 0x81ff4 bltz a0 (a0 = 0) not taken ; 0x81ff8 li a1,1 ; 0x81ffc bne a0,a1 taken *)
      step. if_false. step. step. if_true.
      finish. all: simp_regs; try reflexivity.
    + intros R pc' mem' regs'' md'
        (Hpc & Hmem & HR2 & HR3 & HR4 & HR8 & HR9 & HR18 & HR19 & HR20 & HR21 & HR22 & HR23 & HR24 &
         HR25 & HR26) Hreg Hmat.
      subst pc' mem'. rewrite <- SEGS. apply Hx3.
      assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact HR2).
      assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact HR9).
      assert (E18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact HR18).
      assert (E20 : getr regs'' 20 = getr regs 20) by (rewrite Hreg; exact HR20).
      assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact HR21).
      assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact HR22).
      assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact HR23).
      assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact HR24).
      assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact HR25).
      destruct (f10_keep g j phi fr regs regs'' mem E2 E9 E18 E20 E21 E22 E23 E24 E25 HFLSI HLK HbC HbK
                  H17 H240 HPF)
        as (HFLSI' & HLK' & HbC' & HbK' & H17' & H240' & HPF').
      exists phi, regs'', mem, md', fr.
      split; [reflexivity|].
      split.
      { apply (sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs'' mem md md' HFRA);
          [ exact E2 | rewrite Hreg; exact HR3 | rewrite Hreg; exact HR4
          | rewrite Hreg; exact HR8 | exact E9 | rewrite Hreg; exact HR19
          | rewrite Hreg; exact HR26 | exact Hmat ]. }
      split; [ eapply ent_mat; [ exact HENT | exact Hmat ] |].
      split; [exact Hgn|].
      split; [exact Hj|].
      split; [split; [exact Hphi0 | exact HAd]|].
      split; [exact HFLSI'|].
      split; [exact HLK'|].
      split; [exact HbC'|].
      split; [exact HbK'|].
      split; [exact HbRC|].
      split; [exact Hir|].
      (* IDb1: on the ir = false edge the stage-2 record ID1 g j is the carried t_ID j *)
      split; [ unfold IDb1, ID1, rp_id; rewrite Hir; exact HID |].
      split; [exact H17'|]. split; [exact H240' | exact HPF'].
Qed.

End S.
