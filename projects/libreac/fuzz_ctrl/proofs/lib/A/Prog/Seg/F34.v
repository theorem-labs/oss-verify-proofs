(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 1114 of its 1252 lines of code are new or changed and 873 lines of the source are left out. *)
(* Segment F34 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): 0x8286c-0x82884, the row_of_block loop head
   (W00) and the call of declaration_of (plan-asan section 2 row F34; ubsan twin W02).
   rule 24: no function proved.
   v1.9.0: moved onto a Theorem Labs lane's v1.9 cut bundle (a working branch, 2026-10-28); the commit messages name the
   builds that check it and the FACTS sha of each.

     0x8286c-0x82878  sb zero,8(s3) .. sb zero,11(s3)
                      -- the four shadow bytes of the 32-byte slot [fr + 64, fr + 96) are set to 0, so the slot
                         is addressable (the row slot declaration_of writes).
     0x8287c  mv a0,s4   -- a0 = T + 296 i, the row pointer of row i.
     0x82880  mv a1,s9   -- a1 = fr + 64, the row slot.
     0x82884  jal declaration_of -> 0x82888 with a0 = 1 (every catalogue row has decl_ok, declaration_of_rows)
                                    and the 32 bytes at fr + 64 equal to decl_i i.

   Cuts: both are SlotInv.v's official bodies (push 6c, kept through push 14E).  The entry Inv_A8286c_at (row i)
   is the frame-loop skeleton written out (exists phi, CUTST g 0x8286c (hb1 phi (AC.a_size (flen g j))) with
   FLSI) with LK, i <= 10, RL (row pointer s4, rows left s8, the rows before i unmatched,
   t_rowsel = true and the pass-through bundle FLSX) and the hand-on bundle LT; the exit Inv_A82888_at adds a0 = 1
   and the row slot's declaration bytes and addressability.
   The call is used through DECLc.declaration_of_contract (Section Hypothesis DECL), whose premise is mem_inv: no
   cut carries mem_inv (FRA carries ro_agree), so the call runs on the normalized memory (MemNorm.evt_normalize)
   and its post is brought back with lib/A/RoAdapt's transfers.  The rows come from declaration_of_rows_holds and
   are addressable by FRA's frame_AG conjunct.  The write set W = the four frame-shadow bytes S(fr) + 8 .. 11, the
   callee's window [sp - 2304, sp) and the slot [fr + 64, fr + 96): FRA moves across it by f34_fra_w (F32's
   f32_fra_w for this W), ENT by Tac_slot's ent_store and ent_mat, and FLSI / FLSX / LK / LT by the F32 transports
   (the spill base and everything above it, the block, out[] at fr + 2624, the frame records at fr + 2688, FLC's
   record range at fragb fr = fr + 2768 and the harness block are outside W). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YN2e.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcIdentModel RcFrag RcFragLib
  RcDecl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require declaration_of_c declaration_of.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs Tac_b5.
Import ListNotations.
(* The plain lib/Prog files also load lib/Reusable/YK11, so the short name YK11 is the plain one here; the slot's
   cuts are stated with the image-A one, which this alias names. *)
Module AYK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Import AYK.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module DECLc := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.declaration_of_c.
Module DECLp := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.declaration_of.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module RA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.RoAdapt.
Module ULF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.

(* ========================= image / model helpers ========================= *)

(* The image bytes of a range, byte by byte (Image.image_bytes reads through Lib.Mem.wa). *)
Lemma f34_img_S : forall A n, Image.image_bytes rsegs A (S n) =
  match seg_rom rsegs (LM.wa A), Image.image_bytes rsegs (A + 1) n with
  | Some b, Some bs => Some (b :: bs)
  | _, _ => None
  end.
Proof. reflexivity. Qed.

Lemma f34_img_nth : forall n A bs k, Image.image_bytes rsegs A n = Some bs -> (k < n)%nat ->
  seg_rom rsegs (Z_to_bv 64 (A + Z.of_nat k)) = nth_error bs k.
Proof.
  induction n as [|n IH]; intros A bs k H Hk; [cbn in Hk; lia|].
  rewrite f34_img_S in H. revert H.
  destruct (Image.image_bytes rsegs (A + 1) n) as [bs'|] eqn:E2;
    destruct (seg_rom rsegs (LM.wa A)) as [b|] eqn:E1; intros H; simpl in H; try discriminate H.
  injection H as Hbs. subst bs. destruct k as [|k].
  - cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact E1.
  - cbn [nth_error]. replace (A + Z.of_nat (S k)) with (A + 1 + Z.of_nat k) by lia.
    apply (IH (A + 1) bs' k E2). lia.
Qed.

(* The catalogue rows: image bytes, decl_ok, length (declaration_of_rows_holds). *)
Lemma f34_row : forall i, (i < 11)%nat ->
  Image.image_bytes rsegs (CAT + CAT_ROW * Z.of_nat i) 296 = Some (rowb (Z.of_nat i)) /\
  decl_ok (rowb (Z.of_nat i)) = true /\ length (rowb (Z.of_nat i)) = 296%nat.
Proof.
  intros i Hi.
  destruct (DECLp.declaration_of_rows_holds i Hi) as (row & Himg & Hok & _).
  assert (E : DECLc.BOX_CATALOGUE + 296 * Z.of_nat i = CAT + CAT_ROW * Z.of_nat i)
    by (unfold CAT, CAT_ROW, DECLc.BOX_CATALOGUE; lia).
  rewrite E in Himg.
  assert (Erow : rowb (Z.of_nat i) = row) by (unfold rowb, img; rewrite Himg; reflexivity).
  rewrite Erow. split; [exact Himg|]. split; [exact Hok|].
  exact (Image.image_bytes_length rsegs 296 _ _ Himg).
Qed.

Lemma f34_k_big : forall inp j, t_k inp j <> 0 -> 50 <= t_len inp j.
Proof.
  intros inp j K. destruct (Z_le_gt_dec 50 (t_len inp j)) as [H|H]; [exact H|].
  exfalso. apply K. unfold t_k. apply ctrlparse_none. intros (HC & _ & _). lia.
Qed.

Lemma f34_rowsel_len : forall inp j, t_rowsel inp j = true -> 50 <= t_len inp j.
Proof.
  intros inp j H. apply f34_k_big. intros K0.
  unfold t_rowsel in H. rewrite K0 in H. cbn in H. discriminate H.
Qed.

(* ========================= memory helpers ========================= *)

Lemma f34_mbyte_mrd : forall m q, mbyte rsegs m q = mrd rsegs m (wa q).
Proof. intros m q. reflexivity. Qed.

Lemma f34_outside_dec : forall W q, {outside W q} + {~ outside W q}.
Proof.
  induction W as [|[lo hi] W IH]; intros q; [left; exact I|].
  destruct (IH q) as [H|H]; [|right; intros (_ & Hc); exact (H Hc)].
  destruct (Z_le_dec lo q) as [H1|H1]; destruct (Z_lt_dec q hi) as [H2|H2].
  - right. intros (Hc & _). apply Hc. split; [exact H1 | exact H2].
  - left. split; [intros (_ & Hc); lia | exact H].
  - left. split; [intros (Hc & _); lia | exact H].
  - left. split; [intros (Hc & _); lia | exact H].
Qed.

Lemma f34_sub_stk : forall m lo hi lo' hi', stk rsegs m lo hi -> lo <= lo' -> hi' <= hi -> lo' <= hi' ->
  stk rsegs m lo' hi'.
Proof.
  intros m lo hi lo' hi' (H0 & H1 & H) Ha Hb Hc.
  split; [lia|]. split; [lia|]. intros a Haa. apply H. lia.
Qed.

Lemma f34_rw_of_stk : forall m lo hi, stk rsegs m lo hi -> lo + 32 <= hi ->
  exists ob, length ob = 32%nat /\ rw_cells rsegs m lo [CB 32 ob].
Proof.
  intros m lo hi HST Hle.
  pose proof (f34_sub_stk m lo hi lo (lo + 32) HST ltac:(lia) ltac:(lia) ltac:(lia)) as HS2.
  destruct (stk_bytes rsegs m lo (lo + 32) HS2 ltac:(lia)) as (bs & Hlen & Hb).
  replace (Z.to_nat (lo + 32 - lo)) with 32%nat in Hlen by lia.
  exists bs. split; [exact Hlen|]. split.
  - split; [cbn [cells_wf cell_wf]; split; [exact Hlen | exact I]|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - destruct HST as (H0 & H1 & H).
    split; [lia|]. split; [cbn [cells_size csize]; lia|].
    intros k Hk. cbn [cells_size csize] in Hk. apply (proj1 (H (lo + k) ltac:(lia))).
Qed.

Lemma f34_addr_keep : forall m m' p n, addressable m p n ->
  (forall a, p <= a < p + n -> mrd rsegs m' (wa (shadow_addr a)) = mrd rsegs m (wa (shadow_addr a))) ->
  addressable m' p n.
Proof.
  intros m m' p n (H0 & Hn & Hend & HA) HK. split; [lia|]. split; [lia|]. split; [lia|].
  intros k Hk. destruct (HA k Hk) as (Happ & b & Hb & Hok).
  split; [exact Happ|]. exists b. split; [|exact Hok]. rewrite (HK (p + k) ltac:(lia)). exact Hb.
Qed.

Lemma f34_addr_app : forall m p n k, addressable m p n -> 0 <= k < n -> app_mem (p + k).
Proof. intros m p n k (_ & _ & _ & HA) Hk. exact (proj1 (HA k Hk)). Qed.

Lemma f34_addr_of_bytes : forall m p n, 0 <= p -> 0 <= n -> p + n <= APPMEM_END ->
  (forall a, p <= a < p + n -> addressable m a 1) -> addressable m p n.
Proof.
  intros m p n Hp Hn Hend H. split; [lia|]. split; [lia|]. split; [lia|].
  intros k Hk. destruct (H (p + k) ltac:(lia)) as (_ & _ & _ & HA).
  pose proof (HA 0 ltac:(lia)) as HB. rewrite Z.add_0_r in HB. exact HB.
Qed.


(* Every FakeStack metadata cell lies in [FS, FS + 36864). *)
Lemma f34_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q [Hq|[Hq|[(c & Hc & Hq)|(c & jj & Hc & Hj & Hq)]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hq. lia.
  - subst q. exact (a_fs_flag_range FS c jj Hc Hj).
Qed.

(* The image keeps its writable and executable segments apart (MemNorm.evt_normalize's premise). *)
Lemma f34_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

(* ========================= the machine run ========================= *)

(* 0x8286c -> 0x82888: the four shadow stores at S + 8 .. S + 11 (so that [o, o + 32) is addressable), then
   declaration_of(r, o) by its contract.  The contract asks for mem_inv, which no cut carries: the call runs on
   normalize m1 (MemNorm.evt_normalize, from ro_agree) and its post is brought back across mem_rel (MemNorm's
   munch_rel / wmono_rel / ro_agree_same / bytes_at_rel and lib/A/RoAdapt's rel_*_norm / rel_*_back).  All bounds
   are on plain Z values, so the caller discharges them from the cut without touching the register file. *)
Lemma f34_evt : DECLc.declaration_of_contract ->
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (S r o spv lo : Z) (row ob : list byte) (md0 : Model),
    x2 = Z_to_bv 64 spv -> x19 = Z_to_bv 64 S -> x20 = Z_to_bv 64 r -> x25 = Z_to_bv 64 o ->
    2148236288 <= S -> S + 12 <= 2 ^ 64 ->
    (forall k, 0 <= k < 4 -> wview rsegs m (wa (S + 8 + k)) <> None) ->
    (forall k, 0 <= k < 4 -> in_shadow (S + 8 + k)) ->
    0 <= o -> o + 32 <= APPMEM_END -> (forall k, 0 <= k < 32 -> app_mem (o + k)) -> app_mem (o + 32) ->
    (forall k, 0 <= k < 32 -> S + 8 <= shadow_addr (o + k) < S + 12) ->
    rw_cells rsegs m o [CB 32 ob] -> length ob = 32%nat ->
    0 <= r -> r + 296 <= 652472 -> r mod 8 = 0 -> length row = 296%nat -> decl_ok row = true ->
    bytes_at rsegs m r row -> addressable m r 296 ->
    stk rsegs m lo spv -> HIGHMEM_BEG <= lo -> lo + 2304 <= spv -> spv <= APPMEM_END ->
    (o + 32 <= spv - 2304 \/ spv <= o) -> RT_HI <= o -> 6283264 <= o ->
    ro_agree rsegs m -> AsanRTInv.RT spv m md0 ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82888) x2 x3 x4 t0' t1' t2' x8 x9 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
                       x18 (Z_to_bv 64 S) (Z_to_bv 64 r) x21 x22 x23 x24 (Z_to_bv 64 o) x26 x27 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82888) fcs None m' (seg_rom rsegs) /\
         munch [(S + 8, S + 12); (spv - 2304, spv); (o, o + 32)] m m' /\
         wmono rsegs m m' /\ ro_agree rsegs m' /\ shadow_rw m' /\ stk rsegs m' lo spv /\
         bytes_at rsegs m' o (decl row) /\ addressable m' o 32 /\
         (forall q, 0 <= q < 2 ^ 64 ->
            ~ outside [(S + 8, S + 12); (spv - 2304, spv); (o, o + 32)] q ->
            exists b, mrd rsegs m' (wa q) = Some b))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x8286c) fcs None m (seg_rom rsegs)).
Proof.
  intros DECL x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m S r o spv lo row ob md0
    E2 E19 E20 E25 HSlo HShi HWv HSin Ho0 Ho1 Hoapp Hoend Hosh Hob Hoblen
    Hr0 Hr1 Hr8 Hrlen Hok Hrow Hraddr HST Hlo1 Hlo2 Hsp1 Hodj HoRT HoGT HRO HRT.
  subst x2 x19 x20 x25.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSW.
  assert (EAPP : APPMEM_END = 140737488355328) by reflexivity.
  assert (EHMB : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (ESLOT : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (ERTH : RT_HI = 693624) by reflexivity.
  assert (ERTL : RT_LO = 654032) by reflexivity.
  assert (EDK : DECLc.DECLARATION_OF_K = 2304) by reflexivity.
  assert (EK : ASAN_K = 2147450880) by reflexivity.
  (* --- the four stores --- *)
  assert (HSok : forall (m' : word -> option byte) k, wmono rsegs m m' -> 0 <= k < 4 ->
            store_ok rsegs m' (wa (S + 8 + k)) 1 = true).
  { intros m' k Hw Hk.
    assert (WR : wr_at rsegs m' (S + 8 + k) 1).
    { split; [lia|]. split; [lia|]. intros kk Hkk. assert (Ei : kk = 0) by lia. subst kk.
      rewrite Z.add_0_r. apply Hw. apply HWv. lia. }
    pose proof (wr_at_store_ok rsegs m' (S + 8 + k) 1 0 1%nat WR ltac:(lia) ltac:(lia)) as HSS.
    rewrite Z.add_0_r in HSS. exact HSS. }
  assert (H8 : store_ok rsegs m (wa (S + 8)) 1 = true).
  { replace (S + 8) with (S + 8 + 0) by lia. apply (HSok m 0); [apply wmono_refl | lia]. }
  step.
  match goal with
  | |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (H9 : store_ok rsegs mm (wa (S + 9)) 1 = true)
        by (replace (S + 9) with (S + 8 + 1) by lia; apply (HSok mm 1);
            [repeat (apply wmono_write); apply wmono_refl | lia])
  end.
  step.
  match goal with
  | |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (H10 : store_ok rsegs mm (wa (S + 10)) 1 = true)
        by (replace (S + 10) with (S + 8 + 2) by lia; apply (HSok mm 2);
            [repeat (apply wmono_write); apply wmono_refl | lia])
  end.
  step.
  match goal with
  | |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (H11 : store_ok rsegs mm (wa (S + 11)) 1 = true)
        by (replace (S + 11) with (S + 8 + 3) by lia; apply (HSok mm 3);
            [repeat (apply wmono_write); apply wmono_refl | lia])
  end.
  step. step. step. step.
  (* --- the post-store memory --- *)
  match goal with
  | |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (Em1 : mm = write_to_mem (write_to_mem (write_to_mem (write_to_mem m (wa (S + 8)) [Z_to_bv 8 0])
                       (wa (S + 9)) [Z_to_bv 8 0]) (wa (S + 10)) [Z_to_bv 8 0]) (wa (S + 11)) [Z_to_bv 8 0])
        by (repeat f_equal; try reflexivity; vm_compute; reflexivity);
      rewrite Em1; clear Em1
  end.
  set (m1 := write_to_mem (write_to_mem (write_to_mem (write_to_mem m (wa (S + 8)) [Z_to_bv 8 0])
                 (wa (S + 9)) [Z_to_bv 8 0]) (wa (S + 10)) [Z_to_bv 8 0]) (wa (S + 11)) [Z_to_bv 8 0]) in *.
  assert (MU1 : munch [(S + 8, S + 12)] m m1).
  { unfold m1. apply munch_write; [apply munch_write; [apply munch_write; [apply munch_write;
      [apply munch_refl | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; left; lia]
      | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; left; lia]
      | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; left; lia]
      | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; left; lia]. }
  assert (WM1 : wmono rsegs m m1)
    by (unfold m1; apply wmono_write, wmono_write, wmono_write, wmono_write, wmono_refl).
  (* ro_agree survives the stores: they write shadow bytes, at no read-only address *)
  assert (RO1 : ro_agree rsegs m1).
  { apply (RA.ro_agree_munch [(S + 8, S + 12)] m m1 HRO MU1).
    intros x Hx. apply RA.ro_addr_false_w.
    destruct (Z_lt_le_dec (bv_unsigned x) (S + 8)) as [L|L]; [|lia].
    exfalso. apply Hx. cbn [outside]. split; [lia | exact I]. }
  assert (Hb8 : forall k, 0 <= k < 4 -> bytes_at rsegs m1 (S + 8 + k) [Z_to_bv 8 0]).
  { intros k Hk. unfold m1.
    assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
    destruct Hk' as [ -> | [ -> | [ -> | -> ]]].
    - rewrite Z.add_0_r.
      apply bytes_at_write_other; [apply bytes_at_write_other; [apply bytes_at_write_other;
        [apply bytes_at_write_same | | |] | | |] | | |]; cbn [length]; lia.
    - replace (S + 8 + 1) with (S + 9) by lia.
      apply bytes_at_write_other; [apply bytes_at_write_other;
        [apply bytes_at_write_same | | |] | | |]; cbn [length]; lia.
    - replace (S + 8 + 2) with (S + 10) by lia.
      apply bytes_at_write_other; [apply bytes_at_write_same | | |]; cbn [length]; lia.
    - replace (S + 8 + 3) with (S + 11) by lia. apply bytes_at_write_same; cbn [length]; lia. }
  assert (Hkeep : forall a bs, bytes_at rsegs m a bs -> (a + Z.of_nat (length bs) <= S + 8 \/ S + 12 <= a) ->
                    bytes_at rsegs m1 a bs).
  { intros a bs Hb Hd. eapply fl_bytes; [exact Hb | exact MU1 |].
    intros x Hx. cbn [outside]. split; [lia | exact I]. }
  assert (Hsh1 : forall a, in_shadow a -> exists b, mrd rsegs m1 (wa a) = Some b).
  { intros a Ha.
    destruct (Z_le_dec (S + 8) a) as [Hl|Hl]; destruct (Z_lt_dec a (S + 12)) as [Hh|Hh].
    - destruct (Hb8 (a - S - 8) ltac:(lia)) as (_ & _ & Hb).
      replace (S + 8 + (a - S - 8)) with a in Hb by lia.
      pose proof (Hb 0%nat ltac:(cbn [length]; lia)) as Hb0. cbn [Z.of_nat] in Hb0.
      rewrite Z.add_0_r in Hb0. exists (Z_to_bv 8 0). exact Hb0.
    - destruct (HSW a Ha) as (_ & b & Hb). exists b. unfold mrd in *. rewrite (MU1 (wa a)); [exact Hb|].
      rewrite wa_unsigned by (pose proof (in_shadow_range a Ha); lia). cbn [outside]. split; [lia | exact I].
    - destruct (HSW a Ha) as (_ & b & Hb). exists b. unfold mrd in *. rewrite (MU1 (wa a)); [exact Hb|].
      rewrite wa_unsigned by (pose proof (in_shadow_range a Ha); lia). cbn [outside]. split; [lia | exact I].
    - destruct (HSW a Ha) as (_ & b & Hb). exists b. unfold mrd in *. rewrite (MU1 (wa a)); [exact Hb|].
      rewrite wa_unsigned by (pose proof (in_shadow_range a Ha); lia). cbn [outside]. split; [lia | exact I]. }
  assert (HSW1 : shadow_rw m1)
    by (intros a Ha; split; [apply WM1; exact (proj1 (HSW a Ha)) | exact (Hsh1 a Ha)]).
  assert (HRT1 : AsanRTInv.RT spv m1 md0).
  { eapply (AsanRTInv.RT_meta_write spv spv m m1 md0 md0 [(S + 8, S + 12)]);
      [exact HRT | exact MU1 | exact WM1 | | exact Hsh1].
    unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
      RT_AGLOB, RT_AGLOB_LEN.
    cbn [disjoint_from]. repeat split; try exact I; left; lia. }
  assert (HAC1 : asan_cells m1) by exact (proj1 HRT1).
  assert (Hrow1 : bytes_at rsegs m1 r row) by (apply Hkeep; [exact Hrow | rewrite Hrlen; lia]).
  assert (Hob1 : rw_cells rsegs m1 o [CB 32 ob]).
  { destruct Hob as ((Hwf & Hbb) & Hw). split.
    - split; [exact Hwf|]. eapply fl_bytes; [exact Hbb | exact MU1 |].
      intros x Hx. cbn [cells_bytes cbytes] in Hx. rewrite app_nil_r, Hoblen in Hx.
      cbn [outside]. split; [|exact I]. intros Hc.
      apply (app_not_shadow x).
      + replace x with (o + (x - o)) by lia. apply Hoapp. cbn [Z.of_nat] in Hx. lia.
      + replace x with (S + 8 + (x - S - 8)) by lia. apply HSin. lia.
    - unfold m1. apply wr_at_write, wr_at_write, wr_at_write, wr_at_write. exact Hw. }
  assert (Hstk1 : stk rsegs m1 lo spv).
  { unfold m1. apply stk_write; [apply stk_write; [apply stk_write; [apply stk_write;
      [exact HST | lia | cbn [length]; lia] | lia | cbn [length]; lia] | lia | cbn [length]; lia]
      | lia | cbn [length]; lia]. }
  assert (Haddr1 : addressable m1 o 32).
  { split; [lia|]. split; [lia|]. split; [lia|].
    intros k Hk. split; [apply Hoapp; lia|].
    exists (Z_to_bv 8 0). split; [|unfold shadow_ok; left; reflexivity].
    destruct (Hb8 (shadow_addr (o + k) - S - 8) ltac:(pose proof (Hosh k Hk); lia)) as (_ & _ & Hb).
    replace (S + 8 + (shadow_addr (o + k) - S - 8)) with (shadow_addr (o + k)) in Hb
      by (pose proof (Hosh k Hk); lia).
    pose proof (Hb 0%nat ltac:(cbn [length]; lia)) as Hb0. cbn [Z.of_nat] in Hb0.
    rewrite Z.add_0_r in Hb0. exact Hb0. }
  assert (Haddrrow1 : addressable m1 r 296).
  { apply (f34_addr_keep m m1 r 296 Hraddr). intros a Ha. unfold mrd.
    rewrite (MU1 (wa (shadow_addr a))); [reflexivity|].
    assert (Happa : app_mem a) by (pose proof (f34_addr_app m r 296 (a - r) Hraddr ltac:(lia)) as Hp;
      replace (r + (a - r)) with a in Hp by lia; exact Hp).
    rewrite wa_unsigned by (pose proof (in_shadow_range _ (shadow_of_app a Happa)); lia).
    cbn [outside]. split; [|exact I]. intros Hc.
    unfold shadow_addr, ASAN_K in *. revert Ha Hc Hr0 Hr1 HSlo. Z.div_mod_to_equations. lia. }
  (* --- declaration_of, on the normalized memory (its contract asks for mem_inv) --- *)
  pose proof (mem_rel_normalize rsegs m1 RO1) as REL1.
  pose proof DECL as HD. unfold DECLc.declaration_of_contract in HD. cbv zeta in HD.
  eapply evt_cut.
  { eapply (evt_normalize rsegs _ _ _ _ _ None m1 (seg_rom rsegs) f34_wx RO1).
    eapply HD with (lo := lo) (row := row) (ob := ob).
    all: rewrite ?(unsigned_lit r), ?(unsigned_lit o), ?(unsigned_lit spv) by lia.
    - apply (RA.rel_stk_norm m1 (normalize rsegs m1) lo spv REL1); [|exact Hstk1].
      intros x Hx. apply RA.ro_addr_false_hi. lia.
    - unfold DECLc.DECLARATION_OF_K. lia.
    - exact Hr8.
    - exact Hrlen.
    - exact (bytes_at_normalize rsegs m1 r row RO1 Hrow1).
    - apply (RA.rel_rw_norm m1 (normalize rsegs m1) o [CB 32 ob] REL1); [|exact Hob1].
      intros i Hi. cbn [cells_size csize] in Hi. apply RA.ro_addr_false_hi. lia.
    - right. unfold RT_HI in HoRT. lia.
    - left. unfold DECLc.DECLARATION_OF_K. lia.
    - unfold DECLc.DECLARATION_OF_K. destruct Hodj as [HDj|HDj]; [left; lia | right; lia].
    - exact (mem_inv_normalize rsegs m1).
    - exact (RA.rel_ac_norm m1 _ REL1 HAC1).
    - exact (RA.rel_sw_norm m1 _ REL1 HSW1).
    - exact Hlo1.
    - exact Hsp1.
    - exact (RA.rel_addr_norm m1 _ r 296 REL1 Haddrrow1).
    - exact (RA.rel_addr_norm m1 _ o 32 REL1 Haddr1).
    - exact Hoend.
    - right. exact HoRT. }
  intros ms2 (s0 & Hpost & REL2 & SAME2).
  unfold DECLc.declaration_of_post in Hpost.
  destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0 &
                     E0 & MU0 & WM0 & MI0 & ST0 & RW0 & BA0 & AC0 & SW0).
  subst s0.
  destruct ms2 as [rg2 fg2 pc2 sv2 rv2 fc2 m2 ro2].
  destruct REL2 as (Er2 & Ef2 & Epc2 & Esv2 & Erv2 & Efc2 & Ero2 & REL2).
  unfold MS in Er2, Ef2, Epc2, Esv2, Erv2, Efc2, Ero2, REL2.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom]
    in Er2, Ef2, Epc2, Esv2, Erv2, Efc2, Ero2, REL2, SAME2.
  subst rg2 fg2 pc2 sv2 rv2 fc2 ro2.
  (* the post, brought back from the normalized memory m0 to the real one m2 *)
  pose proof (munch_rel rsegs _ m1 (normalize rsegs m1) m2 m0 REL1 REL2 SAME2 MU0) as MU2.
  pose proof (wmono_rel rsegs m1 (normalize rsegs m1) m2 m0 REL1 REL2 SAME2 WM0) as WM2.
  pose proof (ro_agree_same rsegs m1 m2 RO1 SAME2) as RO2.
  pose proof (RA.rel_stk_back m2 m0 _ _ REL2 ST0) as ST2.
  pose proof (RA.rel_rw_back m2 m0 _ _ REL2 RW0) as RW2.
  pose proof (RA.rel_sw_back m2 m0 REL2 SW0) as SW2.
  clear MU0 WM0 MI0 ST0 RW0 BA0 AC0 SW0.
  rewrite (unsigned_lit o) in MU2, RW2 by lia.
  rewrite (unsigned_lit spv) in MU2, ST2 by lia.
  rewrite Hok in RW2.
  replace (ret_pc (Z_to_bv 64 0x82888)) with (Z_to_bv 64 0x82888)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  rewrite Hok.
  (* --- the combined write set --- *)
  assert (MUa : munch [(S + 8, S + 12); (spv - 2304, spv); (o, o + 32)] m m2).
  { eapply munch_trans.
    - eapply munch_weaken; [|exact MU1]. intros x (Hx & _). cbn [outside]. split; [exact Hx | exact I].
    - eapply munch_weaken; [|exact MU2]. intros x (_ & Hx1 & Hx2 & _). cbn [outside].
      split; [exact Hx1|]. split; [exact Hx2 | exact I]. }
  assert (WMa : wmono rsegs m m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
  destruct RW2 as (((Hdlen & _) & Hdbb) & _).
  cbn [cells_bytes cbytes] in Hdbb. rewrite app_nil_r in Hdbb.
  assert (HINa : forall q, 0 <= q < 2 ^ 64 ->
            ~ outside [(S + 8, S + 12); (spv - 2304, spv); (o, o + 32)] q ->
            exists b, mrd rsegs m2 (wa q) = Some b).
  { intros q Hq Hno.
    assert (Hslot : o <= q < o + 32 -> exists b, mrd rsegs m2 (wa q) = Some b).
    { intros Hin. destruct Hdbb as (_ & _ & Hb).
      pose proof (Hb (Z.to_nat (q - o)) ltac:(rewrite Hdlen; lia)) as Hb0.
      replace (o + Z.of_nat (Z.to_nat (q - o))) with q in Hb0 by lia.
      destruct (nth_error (decl row) (Z.to_nat (q - o))) as [b|] eqn:En;
        [exists b; exact Hb0 | apply nth_error_None in En; rewrite Hdlen in En; lia]. }
    assert (Hshq : S + 8 <= q < S + 12 -> exists b, mrd rsegs m2 (wa q) = Some b).
    { intros Hin. apply (proj2 (SW2 q ltac:(replace q with (S + 8 + (q - S - 8)) by lia; apply HSin; lia))). }
    assert (Hwinq : spv - 2304 <= q < spv -> exists b, mrd rsegs m2 (wa q) = Some b).
    { intros Hin. apply (proj2 (proj2 (proj2 ST2) q ltac:(unfold AF.SLOT_STACK in *; lia))). }
    destruct (Z_le_dec (S + 8) q) as [L1|L1]; destruct (Z_lt_dec q (S + 12)) as [L2|L2];
    destruct (Z_le_dec (spv - 2304) q) as [L3|L3]; destruct (Z_lt_dec q spv) as [L4|L4];
    destruct (Z_le_dec o q) as [L5|L5]; destruct (Z_lt_dec q (o + 32)) as [L6|L6];
    first [ apply Hshq; lia | apply Hwinq; lia | apply Hslot; lia
          | exfalso; apply Hno; cbn [outside]; repeat split; try exact I; lia ]. }
  assert (Haddr2 : addressable m2 o 32).
  { apply (f34_addr_keep m1 m2 o 32 Haddr1). intros a Ha. unfold mrd.
    rewrite (MU2 (wa (shadow_addr a))); [reflexivity|].
    assert (Hin : S + 8 <= shadow_addr a < S + 12) by (pose proof (Hosh (a - o) ltac:(lia)) as Hp;
      replace (o + (a - o)) with a in Hp by lia; exact Hp).
    assert (Happa : app_mem a) by (replace a with (o + (a - o)) by lia; apply Hoapp; lia).
    assert (Hinsh : in_shadow (shadow_addr a)) by (apply shadow_of_app; exact Happa).
    rewrite wa_unsigned by (pose proof (in_shadow_range _ Hinsh); lia).
    cbn [outside]. split; [|split; [|exact I]].
    - intros Hc. apply (app_not_shadow (shadow_addr a)); [|exact Hinsh].
      unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia.
    - intros Hc. apply (app_not_shadow (shadow_addr a)); [|exact Hinsh].
      replace (shadow_addr a) with (o + (shadow_addr a - o)) by lia. apply Hoapp. lia. }
  apply evt_done.
  eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
  split; [reflexivity|].
  split; [exact MUa|]. split; [exact WMa|]. split; [exact RO2|]. split; [exact SW2|].
  split; [exact ST2|]. split; [exact Hdbb|]. split; [exact Haddr2 | exact HINa].
Qed.

(* ========================= the write set (F32's helpers, renamed) ========================= *)

Lemma f34_ba_some : forall m a bs i, bytes_at rsegs m a bs -> 0 <= i < Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa (a + i)) = Some b.
Proof.
  intros m a bs i (_ & _ & H) Hi.
  specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia. rewrite H.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Lemma f34_sh_frame : forall fr y k, 0 <= fr -> fr mod 8 = 0 -> 0 <= y -> shadow_addr y = shadow_addr fr + k ->
  fr + 8 * k <= y < fr + 8 * k + 8.
Proof. unfold shadow_addr. intros fr y k H0 H8 Hy E. Z.div_mod_to_equations. lia. Qed.

Lemma f34_sh_frame_of : forall fr k, 0 <= fr -> fr mod 8 = 0 -> 0 <= k ->
  shadow_addr (fr + 8 * k) = shadow_addr fr + k.
Proof. unfold shadow_addr. intros fr k H0 H8 Hk. Z.div_mod_to_equations. lia. Qed.

Lemma f34_in_shadow_bnd : forall x, in_shadow x -> LOWMEM_END <= x < HIGHMEM_BEG.
Proof. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG. intros; lia. Qed.

Lemma f34_addr_keepW : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) MU HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (shadow_of_app (p + i) Hap) as Hs. pose proof (in_shadow_range _ Hs) as Hbd.
  unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. apply HW. exact Hi.
Qed.

(* A word_mem witness and the le8 word at the same address agree mod 2^64. *)
Lemma f34_wm_uniq : forall m x v (w : word), word_mem rsegs m x v -> bytes_at rsegs m x (le8 w) ->
  v mod 2 ^ 64 = bv_unsigned w.
Proof.
  intros m x v w Hv Hw.
  pose proof Hw as (Hx0 & Hx1 & _). rewrite length_le8 in Hx1. change (Z.of_nat 8) with 8 in Hx1.
  assert (Hv' : word_mem rsegs m x (v mod 2 ^ 64)).
  { intros k Hk. rewrite (Hv k Hk). f_equal. f_equal. unfold le_byte.
    change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity. }
  pose proof (Z.mod_pos_bound v (2 ^ 64) ltac:(lia)) as Hr.
  pose proof (word_mem_le8 rsegs m x (v mod 2 ^ 64) Hv' Hr Hx0 ltac:(lia)) as H8.
  pose proof (fl_le8_eq [] m m x _ _ H8 Hw (munch_refl [] m) (fun _ _ => I)) as E.
  apply (f_equal bv_unsigned) in E. rewrite unsigned_lit in E by lia. exact E.
Qed.

Lemma f34_in_fs_range : forall m a (w : word), AC.a_in_fs AC.ASYMS m a -> bytes_at rsegs m RT_TP (le8 w) ->
  bv_unsigned w + AC.FS_SIZE <= 2 ^ 64 -> 0 <= a < 2 ^ 64 -> bv_unsigned w <= a < bv_unsigned w + AC.FS_SIZE.
Proof.
  intros m a w (b & Hbr & Hb & Hab) Hw Hsz Ha.
  change (AC.as_tp AC.ASYMS) with RT_TP in Hb.
  pose proof (f34_wm_uniq m RT_TP b w Hb Hw) as E.
  pose proof (Z.div_mod b (2 ^ 64) ltac:(lia)) as D. rewrite E in D.
  pose proof (bv_unsigned_in_range 64 w) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw.
  unfold AC.FS_SIZE in *. lia.
Qed.

Lemma f34_mrd_munch : forall W m m' x, munch W m m' -> 0 <= x < 2 ^ 64 -> outside W x ->
  mrd rsegs m' (wa x) = mrd rsegs m (wa x).
Proof.
  intros W m m' x MU Hx Ho. unfold mrd. rewrite (MU (wa x)); [reflexivity|].
  rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma f34_rg_mod : forall regs r a b, rg regs r a -> rg regs r b -> a mod 2 ^ 64 = b mod 2 ^ 64.
Proof.
  unfold rg. intros regs r a b Ha Hb. rewrite Ha in Hb. apply (f_equal bv_unsigned) in Hb.
  rewrite !Z_to_bv_unsigned in Hb. exact Hb.
Qed.

(* A value of s1 within 416 bytes of the spill base A (both read through rg) is A. *)
Lemma f34_rg_near : forall (regs : bvmap 5 word) (r : bv 5) a b, rg regs r a -> rg regs r b ->
  416 <= a -> a + 416 <= 2 ^ 64 -> -400 <= b -> b + 8 <= 2 ^ 64 -> b = a.
Proof.
  intros regs r a b Ha Hb H1 H2 H3 H4.
  pose proof (f34_rg_mod regs r b a Hb Ha) as E. rewrite (Z.mod_small a) in E by lia.
  pose proof (Z.div_mod b (2 ^ 64) ltac:(lia)) as D. rewrite E in D. lia.
Qed.

(* The image's registered globals lie below the image top GT. *)
Lemma f34_AG_low : forall a, in_globals AF.frame_AG a -> 0 <= a < AC.GT.
Proof.
  intros a (lo & len & Hil & Hr). unfold AF.frame_AG in Hil. cbn in Hil. unfold AC.GT.
  repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]).
  destruct Hil.
Qed.

(* The write set W = [S(fr) + 8, S(fr) + 12) ++ [sp - 2304, sp) ++ [fr + 64, fr + 96) misses the shadow byte of
   every app byte x outside the slot: S(fr) + 8 .. 11 are the shadow bytes of [fr + 64, fr + 96) alone (fr is
   8-aligned), a shadow byte is below HIGHMEM_BEG <= sp - 2304, and it is never app memory. *)
Lemma f34_sh_outW : forall fr sp x,
  0 <= fr -> fr mod 8 = 0 -> HIGHMEM_BEG <= sp - 2304 -> (forall y, fr <= y < fr + 3136 -> app_mem y) ->
  app_mem x -> ~ (fr + 64 <= x < fr + 96) ->
  outside [(Sfr fr + 8, Sfr fr + 12); (sp - 2304, sp); (fr + 64, fr + 96)] (shadow_addr x).
Proof.
  intros fr sp x H0 H8 Hsp Happ Hx Hn.
  pose proof (shadow_of_app x Hx) as Hs. pose proof (f34_in_shadow_bnd _ Hs) as Hb.
  assert (Hx0 : 0 <= x) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hx; lia).
  cbn [outside]. split; [|split; [lia | split; [|exact I]]].
  - intros [H1 H2]. apply Hn. unfold Sfr in H1, H2.
    pose proof (f34_sh_frame fr x (shadow_addr x - shadow_addr fr) H0 H8 Hx0 ltac:(lia)) as Hz. lia.
  - intros [H1 H2]. exact (app_not_shadow (shadow_addr x) (Happ (shadow_addr x) ltac:(lia)) Hs).
Qed.

(* ---- The official bundles (SlotInv.v FLSH / FLSI / FLSX / LK / LT) across the write set (F32's transports):
   the spill base A and everything above it, the record bytes at Phi, out[] at fr + 2624, the frame records and
   the harness block are outside W. *)

Lemma f34_spill_mem : forall regs regs' m m' W off v A,
  rg regs 9 A -> 416 <= A -> A + 416 <= 2 ^ 64 -> 0 <= off <= 400 ->
  getr regs' 9 = getr regs 9 -> munch W m m' -> (forall x, A <= x -> outside W x) ->
  spill regs m off v -> spill regs' m' off v.
Proof.
  intros regs regs' m m' W off v A HA H1 H2 Hoff E MU HW (A' & HA' & Hq).
  pose proof Hq as (Hq0 & Hq1 & _). rewrite length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
  assert (EA : A' = A) by (apply (f34_rg_near regs 9 A A' HA HA'); lia).
  subst A'. exists A. split; [unfold rg in *; rewrite E; exact HA|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
  rewrite length_le8. intros x Hx. apply HW. lia.
Qed.

(* Push 14E: PRO's four new spills (184 / 256 / 264 / 272) and FLC's ten spills (offsets <= 272) move with the
   spill base like the others; FLC's two addressable ranges (fragb fr, 72) and (fr + 2688, 38) are premises on m',
   as (fr + 2691, 17) is (F32's f32_flsi_mem).  v1.9: PRO's [A + 200] is [A + 208] and PRO gains [A + 32] =
   fr + 2880 as its 16th conjunct; FLC's slots are renumbered (208 / 64 / 72 / 80 / 56 / 48 -> 192 / 80 / 88 / 96 /
   72 / 64) and FLC gains [A + 56] = fr + 2889 and [A + 48] = fr + 2890 as its 13th and 14th, all spills. *)
Lemma f34_flsi_mem : forall g j fr regs regs' m m' W A,
  rg regs 9 A -> 416 <= A -> A + 416 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> munch W m m' -> (forall x, A <= x -> outside W x) ->
  addressable m' (fr + 2624) 6 -> stk rsegs m' fr (fr + 3136) -> addressable m' (fr + 2691) 17 -> f1_IN g m' ->
  addressable m' (fragb fr) 72 -> addressable m' (fr + 2688) 38 ->
  FLSI g j fr regs m -> FLSI g j fr regs' m'.
Proof.
  intros g j fr regs regs' m m' W A HA H1 H2 E MU HW Ha' Hs' Ha17' HIN' Hfg' Hrec'
    (((P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & _ & _ & Hin & P184 & P256 & P264 & P272 & P32) &
      S128 & _ & S144 & _) &
     S216 & S224 & S248 & _ &
     (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & _ & _ & C72 & C64 & C56 & C48)).
  pose proof (fun off v (Hoff : 0 <= off <= 400) => f34_spill_mem regs regs' m m' W off v A HA H1 H2 Hoff E MU HW)
    as T.
  pose proof HIN' as (_ & Hpad' & Hpb').
  unfold FLSI, FLSH, PRO, FLC.
  split.
  { split.
    { split; [exact (T 40 _ ltac:(lia) P40)|]. split; [exact (T 120 _ ltac:(lia) P120)|].
      split; [exact (T 136 _ ltac:(lia) P136)|]. split; [exact (T 160 _ ltac:(lia) P160)|].
      split; [exact (T 168 _ ltac:(lia) P168)|]. split; [exact (T 176 _ ltac:(lia) P176)|].
      split; [exact (T 208 _ ltac:(lia) P208)|]. split; [exact (T 248 _ ltac:(lia) P248)|].
      split; [exact Ha'|]. split; [exact Hpb'|].
      split; [intros Hn; split; [exact (proj1 (Hin Hn)) | exact Hpad']|].
      split; [exact (T 184 _ ltac:(lia) P184)|]. split; [exact (T 256 _ ltac:(lia) P256)|].
      split; [exact (T 264 _ ltac:(lia) P264)|].
      split; [exact (T 272 _ ltac:(lia) P272) | exact (T 32 _ ltac:(lia) P32)]. }
    split; [exact (T 128 _ ltac:(lia) S128)|]. split; [exact Hs'|].
    split; [exact (T 144 _ ltac:(lia) S144) | exact Ha17']. }
  split; [exact (T 216 _ ltac:(lia) S216)|]. split; [exact (T 224 _ ltac:(lia) S224)|].
  split; [exact (T 248 _ ltac:(lia) S248)|]. split; [exact HIN'|].
  split; [exact (T 256 _ ltac:(lia) C256)|]. split; [exact (T 184 _ ltac:(lia) C184)|].
  split; [exact (T 192 _ ltac:(lia) C192)|]. split; [exact (T 80 _ ltac:(lia) C80)|].
  split; [exact (T 88 _ ltac:(lia) C88)|]. split; [exact (T 96 _ ltac:(lia) C96)|].
  split; [exact (T 272 _ ltac:(lia) C272)|]. split; [exact (T 264 _ ltac:(lia) C264)|].
  split; [exact Hfg'|]. split; [exact Hrec'|].
  split; [exact (T 72 _ ltac:(lia) C72)|]. split; [exact (T 64 _ ltac:(lia) C64)|].
  split; [exact (T 56 _ ltac:(lia) C56) | exact (T 48 _ ltac:(lia) C48)].
Qed.

Lemma f34_lk_mem : forall g fr j regs regs' m m' W,
  getr regs' 21 = getr regs 21 -> munch W m m' ->
  (forall x, fr + 2624 <= x < fr + 2630 -> outside W x) ->
  LK g fr j regs m -> LK g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' W E MU HW (Hj & H21 & HO). split; [exact Hj|].
  split; [unfold rg in *; rewrite E; exact H21|].
  unfold OURb in *. eapply fl_bytes; [exact HO | exact MU |].
  intros x Hx. apply HW. unfold OUR in Hx. rewrite length_map, length_seq in Hx. lia.
Qed.

(* FLSX's record part (guarded by 50 <= len_j) names the 50 bytes t_g (fr50 always has 50) and the record t_phi,
   whose length the record part bounds by len_j: both lie in the block [Phi, Phi + len_j). *)
Lemma f34_flsx_mem : forall g j phi fr regs regs' m m' W A,
  rg regs 9 A -> 416 <= A -> A + 416 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 22 = getr regs 22 ->
  getr regs' 23 = getr regs 23 -> getr regs' 25 = getr regs 25 ->
  munch W m m' -> (forall x, A <= x -> outside W x) ->
  (forall x, phi <= x < phi + flen g j -> outside W x) ->
  FLSI g j fr regs' m' -> FLSX g j phi fr regs m -> FLSX g j phi fr regs' m'.
Proof.
  intros g j phi fr regs regs' m m' W A HA H1 H2 E9 E18 E22 E23 E25 MU HW HWp HI'
    (_ & H18 & H22 & H23 & H25 & Hrec & H152 & H280).
  unfold FLSX.
  split; [exact HI'|].
  split; [unfold rg in *; rewrite E18; exact H18|]. split; [unfold rg in *; rewrite E22; exact H22|].
  split; [unfold rg in *; rewrite E23; exact H23|]. split; [unfold rg in *; rewrite E25; exact H25|].
  split.
  { intros Hl. destruct (Hrec Hl) as (Hp0 & Hp1 & Hg & Hph & Hpl).
    assert (Lg : length (t_g (g_in g) j) = 50%nat)
      by (unfold t_g, fr50; rewrite length_firstn, length_app, repeat_length; lia).
    split; [exact Hp0|]. split; [exact Hp1|].
    split; [eapply fl_bytes; [exact Hg | exact MU |]; rewrite Lg; intros x Hx; apply HWp; lia|].
    split; [eapply fl_bytes; [exact Hph | exact MU |]; intros x Hx; apply HWp; lia|].
    exact Hpl. }
  split; [exact (f34_spill_mem regs regs' m m' W 152 _ A HA H1 H2 ltac:(lia) E9 MU HW H152)|].
  exact (f34_spill_mem regs regs' m m' W 280 _ A HA H1 H2 ltac:(lia) E9 MU HW H280).
Qed.

(* LT (SlotInv.v: IFS g fr (S j), the frame records and the first-fragment spills of turn j + 1).  The frame
   records lie at fr + 2688 (38 bytes) and fr + 2768 (72 bytes): every turn keeps their lengths (ING_length for
   the identity record, the four fg_next cases for the fragment state), so they lie inside the frame. *)

Lemma f34_rp_id_len : forall idb len g, length idb = ID_SIZE -> length (rp_id idb len g) = ID_SIZE.
Proof.
  intros idb len g H. unfold rp_id.
  match goal with |- context [if ?c then _ else _] => destruct c end; [apply ING_length; exact H | exact H].
Qed.

Lemma f34_fg_id_len : forall idb len st g, length idb = ID_SIZE -> length (fg_id idb len st g) = ID_SIZE.
Proof.
  intros idb len st g H. unfold fg_id.
  match goal with |- context [if ?c then _ else _] => destruct c end; [apply ING_length; exact H | exact H].
Qed.

Lemma f34_tID_length : forall inp j, length (t_ID inp j) = ID_SIZE.
Proof.
  intros inp j. unfold t_ID. induction j as [|j IH]; [reflexivity|].
  cbn [fst_at]. unfold turn. cbv beta zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id]; apply f34_fg_id_len, f34_rp_id_len; exact IH.
Qed.

Lemma f34_fg_st_len : forall len st g, length st = 72%nat -> length g = 50%nat ->
  length (fg_st len st g) = 72%nat.
Proof.
  intros len st g HL HG. unfold fg_st, fcls. cbn [fg_class Z.eqb orb].
  destruct (fg_fr len g) eqn:Efr; cbn [negb fg_next]; [|exact HL].
  assert (Hn : 1 <= fg_n g <= 22).
  { unfold fg_fr in Efr. apply andb_prop in Efr as [Efr _]. apply andb_prop in Efr as [Efr E22].
    apply andb_prop in Efr as [_ E1]. apply Z.leb_le in E22. apply Z.leb_le in E1. lia. }
  destruct (bat g 19 =? 1); cbn [fg_next].
  - unfold fg_first, fg_body. rewrite !length_app, length_skipn, HL. cbn [length].
    rewrite !rf_bsl_length by lia. lia.
  - destruct (negb (fg_keep st g)) eqn:Ek; cbn [fg_next].
    + apply rf_clear_length. exact HL.
    + assert (HT : fg_T st g <= 64).
      { unfold fg_keep in Ek. apply negb_false_iff in Ek. apply andb_prop in Ek as [_ Ek].
        apply Z.leb_le in Ek. exact Ek. }
      destruct (negb (fg_close st g)); cbn [fg_next]; apply rf_clear_length; apply rf_fg_join_length;
        assumption.
Qed.

Lemma f34_tFG_length : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. unfold t_FG. induction j as [|j IH]; [reflexivity|].
  assert (HG : length (t_g inp j) = 50%nat).
  { unfold t_g, fr50. rewrite length_firstn, length_app, repeat_length. lia. }
  cbn [fst_at]. unfold turn. cbv beta zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_fg]; apply f34_fg_st_len; assumption.
Qed.

Lemma f34_f1in_mem : forall g m m' W,
  munch W m m' ->
  (forall x, g_p g <= x < g_p g + g_n g -> outside W x) ->
  (forall x, g_p g <= x < g_p g + g_n g -> outside W (shadow_addr x)) ->
  f1_IN g m -> f1_IN g m'.
Proof.
  intros g m m' W MU HW HWs (Hin & Had & Hb). split; [exact Hin|]. split.
  - apply (f34_addr_keepW W m m' _ _ Had MU). intros i Hi. apply HWs. lia.
  - eapply fl_bytes; [exact Hb | exact MU |]. intros x Hx. apply HW. unfold g_n, nlen. lia.
Qed.

(* v1.9 FSb: the body of the last FIRST fragment, at fr + 2880, is at most 23 bytes (block[9 ..] of a 50-byte
   frame record), so it lies in [fr + 2880, fr + 2915), the 35 addressable bytes FSb names. *)
Lemma f34_fs_body_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  assert (HG : length (t_g inp j) = 50%nat).
  { unfold t_g, fr50. rewrite length_firstn, length_app, repeat_length. lia. }
  cbn [fst_at]. unfold turn. cbv beta zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_body]; [|exact IH].
  rewrite length_firstn, length_skipn, HG. lia.
Qed.

(* v1.9 FSb: [A + 104] / [A + 112], the body bytes at fr + 2880 and their addressability (shadow S(fr) + 360 ..
   364), memory only. *)
Lemma f34_lt_mem : forall g fr j regs regs' m m' W A,
  rg regs 9 A -> 416 <= A -> A + 416 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> munch W m m' -> (forall x, A <= x -> outside W x) ->
  (forall x, fr + 2688 <= x < fr + 2840 -> outside W x) ->
  (forall x, fr + 2880 <= x < fr + 2915 -> outside W x /\ outside W (shadow_addr x)) ->
  LT g fr j regs m -> LT g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' W A HA H1 H2 E MU HW HWr HWb
    ((HID & Hidok) & (HFG & Hfgok) & (Q104 & Q112 & Qbody & Qad & HFI)).
  pose proof (fun off v (Hoff : 0 <= off <= 400) => f34_spill_mem regs regs' m m' W off v A HA H1 H2 Hoff E MU HW)
    as T.
  pose proof (f34_tID_length (g_in g) (S j)) as LID. pose proof (f34_tFG_length (g_in g) (S j)) as LFG.
  unfold ID_SIZE in LID.
  unfold LT, IFS, IDj, FGj, IDb, FGb, FSj, FSb.
  split.
  { split; [|exact Hidok]. unfold IDBe in *. eapply fl_bytes; [exact HID | exact MU |].
    rewrite LID. intros x Hx. apply HWr. lia. }
  split.
  { split; [|exact Hfgok]. unfold FGBe in *. eapply fl_bytes; [exact HFG | exact MU |].
    rewrite LFG. intros x Hx. apply HWr. lia. }
  split; [exact (T 104 _ ltac:(lia) Q104)|]. split; [exact (T 112 _ ltac:(lia) Q112)|].
  split.
  { eapply fl_bytes; [exact Qbody | exact MU |].
    pose proof (f34_fs_body_len (g_in g) (S j)) as LB. intros x Hx. exact (proj1 (HWb x ltac:(lia))). }
  split; [|exact HFI].
  apply (f34_addr_keepW W m m' _ _ Qad MU). intros i Hi. exact (proj2 (HWb (fr + 2880 + i) ltac:(lia))).
Qed.

Section F34.
Context {fx : AYK.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis DECL : DECLc.declaration_of_contract.

Local Notation STKLO mem md := (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
Local Notation STKHI mem md := (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
Local Notation OWNED H mem md := (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md).

(* The frame's place (F32's fra_loc): the side stack FS is the word at tp, below the real stack; the frame is on
   the real stack (at or above stklo) or inside FS. *)
Lemma f34_fra_loc : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  exists FS, (exists w : word, bytes_at rsegs mem RT_TP (le8 w) /\ bv_unsigned w = FS) /\
    AC.GT <= FS /\ FS + AC.FS_SIZE <= STKLO mem md /\ (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a) /\
    HIGHMEM_BEG <= STKLO mem md /\
    0 <= fr /\ AC.GT <= fr /\ (forall a, fr <= a < fr + 3136 -> app_mem a) /\
    ((STKLO mem md <= fr /\ fr + 3136 <= APPMEM_END) \/ (FS <= fr /\ fr + 3136 <= FS + AC.FS_SIZE)).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md HFRA.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGTfr & Hfrapp).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof Hwin as (Hw0 & Hw1 & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (RT_fs_cells _ _ _ HRT) as (_ & _ & _ & _ & (FSw & HFSw & HFok) & _).
  pose proof (bv_unsigned_in_range 64 FSw) as HFSr. change (bv_modulus 64) with (2 ^ 64) in HFSr.
  assert (Hwm : word_mem rsegs mem (AC.as_tp AC.ASYMS) (bv_unsigned FSw)).
  { change (AC.as_tp AC.ASYMS) with RT_TP. exact (bytes_at_le8_word rsegs mem RT_TP FSw HFSw). }
  destruct (AC.a_laws_fs_place _ _ _ _ _ LAWS _ mem md (bv_unsigned FSw) HAH Hwm HFSr)
    as (HGT & HFSlo & _ & HFSapp).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hhi.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  pose proof Hhdr1 as (Hfr0 & Hfr8 & _). rewrite length_le8 in Hfr8. change (Z.of_nat 8) with 8 in Hfr8.
  exists (bv_unsigned FSw).
  split; [exists FSw; split; [exact HFSw | reflexivity]|].
  split; [exact HGT|]. split; [exact HFSlo|]. split; [exact HFSapp|]. split; [exact Hhi|].
  split; [exact Hfr0|]. split; [exact HGTfr|]. split; [exact Hfrapp|].
  destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
  - pose proof (Hreal fr ltac:(lia)) as R1. pose proof (Hreal (fr + 3135) ltac:(lia)) as R2.
    left. lia.
  - assert (HFS1 : bv_unsigned FSw + AC.FS_SIZE <= 2 ^ 64) by (unfold AC.FS_SIZE in *; lia).
    pose proof (f34_in_fs_range mem fr FSw (Hfs fr ltac:(lia)) HFSw HFS1 ltac:(lia)) as F1.
    assert (Hin : forall a, fr <= a < fr + 3136 -> bv_unsigned FSw <= a < bv_unsigned FSw + AC.FS_SIZE).
    { intros a Ha. apply (f34_in_fs_range mem a FSw (Hfs a Ha) HFSw HFS1).
      unfold AF.SLOT_STACK, AC.FS_SIZE in *. lia. }
    pose proof (Hin (fr + 3135) ltac:(lia)) as F2.
    right. lia.
Qed.

(* A byte of a live heap block is not a frame byte (F32's fra_blk). *)
Lemma f34_fra_blk : forall g fr hb regs mem md p n a, FRA B APIf ra g fr hb regs mem md ->
  In (p, n) (hb ++ g_H g) -> p <= a < p + n -> fr <= a < fr + 3136 -> False.
Proof.
  intros g fr hb regs mem md p n a HFRA Hin Ha Hfa.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfA & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md p n HAH Hin) as (_ & _ & Hend & _ & Hall).
  destruct (Hall a Ha) as (_ & _ & _ & _ & Hnfs).
  destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
  - pose proof (Hreal a Hfa). lia.
  - exact (Hnfs (Hfs a Hfa)).
Qed.

(* FRA across this segment's write set W = the four frame-shadow bytes S(fr) + 8 .. 11, declaration_of's window
   [sp - 2304, sp) and the row slot [fr + 64, fr + 96) (F32's f32_fra_w for this W).  RT by RT_meta_write (shadow
   bytes are rewritten, every shadow byte is still readable); AH and stklo from the caller; the 392 shadow bytes
   are rebuilt from shadow_rw mem'; the S-anchored stack window is backed again (the callee's window by its stk
   result, the slot by its new bytes, every other byte of it is outside W); the side arm's FakeStack record and
   every other FRA cell are outside W by the address bounds (the image is below GT <= fr, the shadow is below
   HIGHMEM_BEG <= stklo < sp - 2304, the FakeStack is below stklo, the frame header is apart from the window by
   fra_frame, the spill base A and the saved registers are at or above sp and above the frame); an addressable
   byte outside the frame (a registered global, a byte of the slot window) keeps its shadow byte (f34_sh_outW). *)
Lemma f34_fra_w : forall g fr hb regs regs' mem mem' md spv,
  FRA B APIf ra g fr hb regs mem md ->
  AC.aspZ regs = spv ->
  munch [(Sfr fr + 8, Sfr fr + 12); (spv - 2304, spv); (fr + 64, fr + 96)] mem mem' ->
  wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  STKLO mem' md = STKLO mem md ->
  shadow_rw mem' ->
  stk rsegs mem' (spv - FN_STACK) spv ->
  (forall a, fr + 64 <= a < fr + 96 -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md spv HFRA Hasp MU WM HRO HAH' HSTK HSW' HWIN HSLOT
    E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hplace & _ & _ & _).
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWAd &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (Esp : spv = sp) by (rewrite <- Hasp; exact Haspz).
  clear Hasp. subst spv.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HHB : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HAE : APPMEM_END = 140737488355328) by reflexivity.
  assert (HLE : LOWMEM_END = 2147450880) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  unfold AC.GT in HGT.
  assert (Hwin0 : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hwin; destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (Hpl : fr + 3136 <= sp - 2304 \/ sp <= fr).
  { destruct (Hplace 2304 ltac:(lia)) as [H|H]; rewrite Haspz in H; [left | right]; lia. }
  assert (Hhi0 : HIGHMEM_BEG <= STKLO mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                (hb ++ g_H g) mem md HAH).
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; clear; Z.div_mod_to_equations; lia).
  assert (HWw : HIGHMEM_BEG <= sp - 2304) by lia.
  (* the frame's shadow bytes *)
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + 392 -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + 3136) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ _ Hin)) as His.
    replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  assert (Hin8 : in_shadow (Sfr fr + 8)) by (apply HshIS; lia).
  assert (Hin11 : in_shadow (Sfr fr + 11)) by (apply HshIS; lia).
  pose proof (f34_in_shadow_bnd _ Hin8) as HS8b.
  pose proof (f34_in_shadow_bnd _ Hin11) as HS11b.
  pose proof (f34_in_shadow_bnd _ (HshIS (Sfr fr) ltac:(lia))) as HS0b.
  pose proof (f34_in_shadow_bnd _ (HshIS (Sfr fr + 391) ltac:(lia))) as HS379b.
  assert (Hmeta8 : Sfr fr + 8 < fr \/ fr + 3136 <= Sfr fr + 8).
  { apply (app_ivl_meta fr (fr + 3136)); [exact Happ | exact Hin8]. }
  assert (Hmeta11 : Sfr fr + 11 < fr \/ fr + 3136 <= Sfr fr + 11).
  { apply (app_ivl_meta fr (fr + 3136)); [exact Happ | exact Hin11]. }
  (* outside W for the classes of addresses FRA reads *)
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1.
    assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by lia. cbn [outside]. repeat split; try exact I; lia. }
    unfold mbyte. rewrite Hm. reflexivity. }
  assert (HWfr : forall x, fr <= x < fr + 24 ->
                   outside [(Sfr fr + 8, Sfr fr + 12); (sp - 2304, sp); (fr + 64, fr + 96)] x).
  { intros x Hx. cbn [outside]. repeat split; try exact I; lia. }
  assert (HWA : forall x, A <= x ->
                  outside [(Sfr fr + 8, Sfr fr + 12); (sp - 2304, sp); (fr + 64, fr + 96)] x).
  { intros x Hx. cbn [outside]. repeat split; try exact I; lia. }
  (* an addressable byte outside the frame keeps its shadow byte *)
  assert (Hkeep1 : forall a, addressable mem a 1 -> ~ (fr <= a < fr + 3136) -> addressable mem' a 1).
  { intros a Ha Hnf. apply (f34_addr_keepW _ mem mem' a 1 Ha MU). intros i Hi.
    replace (a + i) with a by lia.
    apply (f34_sh_outW fr sp a); [lia | exact Hfr8 | exact HWw | exact Happ | exact (addr1_app mem a Ha) | lia]. }
  (* RT *)
  assert (HRT' : AsanRTInv.RT sp mem' md).
  { eapply (AsanRTInv.RT_meta_write sp sp mem mem' md md); [exact HRT | exact MU | exact WM | | ].
    - unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
        RT_AGLOB, RT_AGLOB_LEN.
      cbn [disjoint_from]. repeat split; first [left; lia | exact I].
    - intros a Ha. destruct (HSW' a Ha) as (_ & b & Hb). exists b. exact Hb. }
  exists A, sp, s5.
  split; [exact HRT'|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo;
          [lia | rewrite Hthr in Hx; cbn in Hx; lia].
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo;
          [lia | rewrite Hlock in Hx; cbn in Hx; lia].
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
  split; [exact HA416|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. apply HWA. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. apply HWA. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr24 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWA. lia. }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfrz [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfrz|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + split.
        * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo2 | exact Hhi2]].
          intros k Hk. rewrite KBlo.
          -- exact (Hw k Hk).
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * apply (fsrec_munch_lo APIf (hb ++ g_H g) mem mem' md _ fr Hrec HAH (proj1 (fr_munch_ul _ _ _) MU)).
          -- intros x Hx. apply (proj2 (fr_outside_lib _ _)). cbn [outside].
             repeat split; try exact I; lia.
          -- intros x Hx Hnb Hlo. apply (proj2 (fr_outside_lib _ _)). cbn [outside].
             split; [intros Hc; apply (app_not_shadow x Hx); apply HshIS; lia|].
             split; [lia|].
             split; [lia | exact I]. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWfr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWfr. lia. }
  split.
  { assert (HSTKsh : stk rsegs mem' (Sfr fr) (Sfr fr + 392)).
    { split; [lia|]. split; [lia|]. intros a Ha. exact (HSW' a (HshIS a Ha)). }
    destruct (stk_bytes rsegs mem' (Sfr fr) (Sfr fr + 392) HSTKsh ltac:(lia)) as (sh' & Hl' & Hb').
    exists sh'. split; [exact Hb'|]. rewrite Hl'. replace (Sfr fr + 392 - Sfr fr) with 392 by lia.
    reflexivity. }
  split.
  { destruct Hwin as (Hw0 & Hw1 & Hwv). split; [exact Hw0|]. split; [exact Hw1|].
    intros a Ha. destruct (Hwv a Ha) as (Hwa & b & Hb). split; [exact (WM _ Hwa)|].
    assert (Hout : ~ (sp - 2304 <= a < sp) -> ~ (fr + 64 <= a < fr + 96) ->
                   exists b', mrd rsegs mem' (wa a) = Some b').
    { intros N1 N2. exists b. rewrite (f34_mrd_munch _ mem mem' a MU ltac:(lia)); [exact Hb|].
      cbn [outside]. split; [lia|]. split; [exact N1|]. split; [exact N2 | exact I]. }
    destruct (Z_le_gt_dec (sp - 2304) a) as [L3|L3]; [destruct (Z_lt_ge_dec a sp) as [L4|L4]|].
    - destruct HWIN as (_ & _ & HW). exact (proj2 (HW a ltac:(lia))).
    - destruct (Z_le_gt_dec (fr + 64) a) as [L1|L1]; [destruct (Z_lt_ge_dec a (fr + 96)) as [L2|L2]|];
        [apply HSLOT; lia | apply Hout; lia | apply Hout; lia].
    - destruct (Z_le_gt_dec (fr + 64) a) as [L1|L1]; [destruct (Z_lt_ge_dec a (fr + 96)) as [L2|L2]|];
        [apply HSLOT; lia | apply Hout; lia | apply Hout; lia]. }
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWA. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn [length] in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split.
  { intros a Hin. apply Hkeep1; [exact (HAG a Hin)|].
    pose proof (f34_AG_low a Hin) as Hl. unfold AC.GT in Hl. lia. }
  split; [intros a H1 H2; exact (Hkeep1 a (HWAd a H1 H2) H2)|].
  split; [exact HSHI1|]. split; [exact HSHI2|]. split; [exact HSHI3|].
  split; [exact Hhb | exact Hlive].
Qed.

(* ===================== the segment lemma ===================== *)

(* Entry Inv_A8286c_at j i (the row loop head at row i); exit Inv_A82888_at j i (declaration_of returned). *)
Lemma seg_F34 : forall j i,
  Hat2 B APIf ra (Inv_A82888_at B APIf ra) j i -> Hat2 B APIf ra (Inv_A8286c_at B APIf ra) j i.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros j i Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI &
    HLK & Hi10 & HRL & HLT).
  subst c. rewrite SEGS.
  pose proof HRL as (_ & H20 & H24 & Hprev & Hsel & HFLSX).
  pose proof HFLSX as (_ & _ & _ & _ & H25 & _).
  pose proof HFLSI as (((_ & _ & _ & _ & _ & _ & _ & _ & Had2624 & _ & _) & _ & Hstkfr & _ & Had2691) &
    _ & _ & _ & HIN & (_ & _ & _ & _ & _ & _ & _ & _ & Hadfg & Hadrec & _)).
  (* a selected row has kind 9, so len_j >= 50: the block's a_size is its length *)
  assert (Hl50 : 50 <= flen g j) by (unfold flen; exact (f34_rowsel_len (g_in g) j Hsel)).
  assert (Hsz : AC.a_size (flen g j) = flen g j) by (unfold AC.a_size; lia).
  rewrite Hsz in HFRA, HENT.
  pose proof (fra_win B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (Hlosp & HSTKw).
  pose proof (fra_frame B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (Hplace & _ & HFSb & _).
  pose proof (fra_app B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (HGTfr & Hfrapp).
  pose proof (f34_fra_loc g fr (hb1 phi (flen g j)) regs mem md HFRA)
    as (FS & (FSw & HFSw & EFS) & HGTFS & HFSlo & HFSapp & Hhi & Hfr0 & _ & _ & Hfrloc).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz & Hstklo &
    Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5v & HAm & HAS & Hspa & HfrA & HA416 & HS4 & HAPP &
    Hspill & Hsel5 & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAGf & HWAd &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  rewrite Haspz in Hlosp, HSTKw, Hplace.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HHBv : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HAE : APPMEM_END = 140737488355328) by reflexivity.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof Hwin as (Hw0 & Hw1 & _).
  assert (HAb : 416 <= A /\ A + 416 <= 2 ^ 64) by lia.
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; clear; Z.div_mod_to_equations; lia).
  assert (Efr8 : 8 * (fr / 8) = fr) by (revert Hfr8; clear; Z.div_mod_to_equations; lia).
  assert (HspE : sp <= APPMEM_END) by lia.
  assert (HWw : HIGHMEM_BEG <= sp - 2304) by lia.
  unfold AC.GT in HGTfr.
  assert (Hfrb : fr + 3136 <= APPMEM_END).
  { assert (Ha : app_mem (fr + 3135)) by (apply Hfrapp; lia).
    unfold app_mem, LOWMEM_END in Ha. lia. }
  (* the frame's shadow bytes and the slot's *)
  assert (Hshf : forall x, Sfr fr <= x < Sfr fr + 392 -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + 3136) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Hfrapp _ Hin)) as His.
    replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  pose proof (f34_in_shadow_bnd _ (Hshf (Sfr fr + 8) ltac:(lia))) as Hrng8.
  pose proof (f34_in_shadow_bnd _ (Hshf (Sfr fr + 11) ltac:(lia))) as Hrng11.
  assert (HWsh : forall x, app_mem x -> ~ (Sfr fr + 8 <= x < Sfr fr + 12)).
  { intros x Hx Hc. exact (app_not_shadow x Hx (Hshf x ltac:(lia))). }
  assert (Hpl2304 : fr + 3136 <= sp - 2304 \/ sp <= fr).
  { destruct (Hplace 2304 ltac:(lia)) as [H|H]; [left | right]; lia. }
  assert (HWfrm : forall x, fr <= x < fr + 3136 -> ~ (sp - 2304 <= x < sp)).
  { destruct Hpl2304 as [Hq|Hq]; intros x Hx; lia. }
  assert (Hshw : forall k, 0 <= k < 4 -> wview rsegs mem (wa (Sfr fr + 8 + k)) <> None)
    by (intros k Hk; exact (proj1 (AsanRTInv.RT_shadow_rw _ _ _ HRT _ (Hshf (Sfr fr + 8 + k) ltac:(lia))))).
  assert (Hslotsh : forall k, 0 <= k < 32 -> Sfr fr + 8 <= shadow_addr (fr + 64 + k) < Sfr fr + 12).
  { intros k Hk. unfold Sfr, shadow_addr. revert Efr8 Hk. clear. Z.div_mod_to_equations. lia. }
  (* the row *)
  destruct (f34_row i ltac:(lia)) as (Himg & Hok & Hrlen).
  assert (Hrb : 0 <= CAT + CAT_ROW * Z.of_nat i /\ CAT + CAT_ROW * Z.of_nat i + 296 <= 652472)
    by (unfold CAT, CAT_ROW; lia).
  assert (Hrow : bytes_at rsegs mem (CAT + CAT_ROW * Z.of_nat i) (rowb (Z.of_nat i))).
  { split; [lia|]. split; [rewrite Hrlen; lia|].
    intros k Hk. rewrite Hrlen in Hk.
    assert (Hin : in_globals AF.frame_RELRO (CAT + CAT_ROW * Z.of_nat i + Z.of_nat k)).
    { exists 0x9e348, 9344. split; [cbn [In]; left; reflexivity|]. unfold CAT, CAT_ROW in *. lia. }
    pose proof (Hgimg (CAT + CAT_ROW * Z.of_nat i + Z.of_nat k) Hin) as Hg. rewrite SEGS in Hg.
    transitivity (seg_rom rsegs (Z_to_bv 64 (CAT + CAT_ROW * Z.of_nat i + Z.of_nat k))); [exact Hg|].
    exact (f34_img_nth 296 (CAT + CAT_ROW * Z.of_nat i) (rowb (Z.of_nat i)) k Himg ltac:(lia)). }
  assert (Hraddr : addressable mem (CAT + CAT_ROW * Z.of_nat i) 296).
  { apply f34_addr_of_bytes; [lia | lia | unfold APPMEM_END, CAT, CAT_ROW in *; lia |].
    intros a Ha. apply HAGf. exists 0x9e800, 3256.
    split; [unfold AF.frame_AG; cbn [In]; repeat first [ left; reflexivity | right ]|].
    unfold CAT, CAT_ROW in *. lia. }
  (* the slot *)
  assert (Hslotstk : stk rsegs mem (fr + 64) (fr + 96))
    by (apply (f34_sub_stk mem fr (fr + 3136)); [exact Hstkfr | lia | lia | lia]).
  destruct (f34_rw_of_stk mem (fr + 64) (fr + 96) Hslotstk ltac:(lia)) as (ob & Hoblen & Hob).
  apply (@sl_run_lib fx regs (Z_to_bv 64 0x8286c) mem md
    (fun R0 pc' mem' => pc' = Z_to_bv 64 0x82888 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 21 = getr regs 21 /\ getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\
       getr R0 24 = getr regs 24 /\ getr R0 26 = getr regs 26 /\
       getr R0 19 = Z_to_bv 64 (Sfr fr) /\ getr R0 20 = Z_to_bv 64 (CAT + CAT_ROW * Z.of_nat i) /\
       getr R0 25 = Z_to_bv 64 (fr + 64) /\ getr R0 10 = Z_to_bv 64 1 /\
       munch [(Sfr fr + 8, Sfr fr + 12); (sp - 2304, sp); (fr + 64, fr + 96)] mem mem' /\
       wmono rsegs mem mem' /\ ro_agree rsegs mem' /\ shadow_rw mem' /\
       stk rsegs mem' (sp - FN_STACK) sp /\
       bytes_at rsegs mem' (fr + 64) (decl (rowb (Z.of_nat i))) /\ addressable mem' (fr + 64) 32 /\
       (forall q, 0 <= q < 2 ^ 64 ->
          ~ outside [(Sfr fr + 8, Sfr fr + 12); (sp - 2304, sp); (fr + 64, fr + 96)] q ->
          exists b, mrd rsegs mem' (wa q) = Some b))
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold Regs6ss.mkR_of.
    eapply LE.evt_mono.
    { eapply (f34_evt DECL) with (S := Sfr fr) (r := CAT + CAT_ROW * Z.of_nat i) (o := fr + 64)
        (spv := sp) (lo := sp - FN_STACK) (row := rowb (Z.of_nat i)) (ob := ob) (md0 := md).
      - exact Hr2.
      - unfold rg in Hr19. exact Hr19.
      - unfold rg in H20. exact H20.
      - unfold rg in H25. exact H25.
      - revert HGTfr. clear. unfold Sfr, shadow_addr, ASAN_K. intros H. Z.div_mod_to_equations. lia.
      - lia.
      - exact Hshw.
      - intros k Hk. apply Hshf. lia.
      - lia.
      - lia.
      - intros k Hk. apply Hfrapp. lia.
      - apply Hfrapp. lia.
      - exact Hslotsh.
      - exact Hob.
      - exact Hoblen.
      - lia.
      - lia.
      - replace (CAT + CAT_ROW * Z.of_nat i) with ((81152 + 37 * Z.of_nat i) * 8)
          by (unfold CAT, CAT_ROW; lia).
        apply Z.mod_mul. lia.
      - exact Hrlen.
      - exact Hok.
      - exact Hrow.
      - exact Hraddr.
      - exact HSTKw.
      - lia.
      - lia.
      - exact HspE.
      - destruct Hpl2304 as [HD|HD]; [left; lia | right; lia].
      - unfold RT_HI. lia.
      - lia.
      - exact Hro.
      - exact HRT. }
    { intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                  E2m & MU2 & WM2 & RO2 & SW2 & ST2 & BA2 & AD2 & IN2).
      eexists _, (Z_to_bv 64 0x82888), m2. split; [exact E2m|].
      (* the row slot ends at o + 32 = fr + 64 + 32, written fr + 96 in the run's write set *)
      replace (fr + 64 + 32) with (fr + 96) in MU2 by lia.
      replace (fr + 64 + 32) with (fr + 96) in IN2 by lia.
      repeat (split; [reflexivity|]).
      split; [exact MU2|]. split; [exact WM2|]. split; [exact RO2|]. split; [exact SW2|].
      split; [exact ST2|]. split; [exact BA2|]. split; [exact AD2 | exact IN2]. }
  - intros R0 pc' mem' regs' md'
      (Hpc & E2 & E3 & E4 & E8 & E9 & E18 & E21 & E22 & E23 & E24 & E26 & E19 & E20 & E25 & E10 &
       MU & WM & RO' & SW' & ST' & BA' & AD' & HINw) Hreg Hmat.
    subst pc'.
    assert (F2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (F3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (F4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (F8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (F9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (F18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact E18).
    assert (F21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact E21).
    assert (F22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact E22).
    assert (F23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact E23).
    assert (F24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact E24).
    assert (F26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact E26).
    assert (F19 : getr regs' 19 = getr regs 19) by (rewrite Hreg, E19; unfold rg in Hr19; symmetry; exact Hr19).
    assert (F20 : getr regs' 20 = Z_to_bv 64 (CAT + CAT_ROW * Z.of_nat i)) by (rewrite Hreg; exact E20).
    assert (F25 : getr regs' 25 = getr regs 25) by (rewrite Hreg, E25; unfold rg in H25; symmetry; exact H25).
    assert (F10 : getr regs' 10 = Z_to_bv 64 1) by (rewrite Hreg; exact E10).
    (* every byte the run wrote is present again *)
    assert (HpresM : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                      exists b, mbyte rsegs mem' q = Some b).
    { intros q Hq Hp.
      destruct (f34_outside_dec [(Sfr fr + 8, Sfr fr + 12); (sp - 2304, sp); (fr + 64, fr + 96)] q) as [Ho|Ho].
      - destruct Hp as (b0 & Hb0). exists b0. rewrite f34_mbyte_mrd in *.
        rewrite (f34_mrd_munch _ mem mem' q MU Hq Ho). exact Hb0.
      - rewrite f34_mbyte_mrd. exact (HINw q Hq Ho). }
    assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
      by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
    (* the heap invariant, the runtime's own bytes and the stack bounds across the write set *)
    assert (HAHS : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (flen g j) ++ g_H g) mem' md /\
                   (forall q, OWNED (hb1 phi (flen g j) ++ g_H g) mem' md q <->
                              OWNED (hb1 phi (flen g j) ++ g_H g) mem md q) /\
                   STKLO mem' md = STKLO mem md /\ STKHI mem' md = STKHI mem md).
    { destruct Hfrloc as [[Hlo Hhi'] | [Hlo Hhi']].
      - assert (Hst : forall a, 0 <= a < 2 ^ 64 ->
                  ~ AC.a_store_ok (hb1 phi (flen g j) ++ g_H g) (STKLO mem md) a ->
                  mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
        { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia. cbn [outside].
          split; [|split; [|split; [|exact I]]].
          - intros [Hc1 Hc2]. apply Hns. right; right; right. exists (fr + 8 * (a - Sfr fr)).
            split; [rewrite f34_sh_frame_of by lia; unfold Sfr in *; lia|].
            right; left. lia.
          - intros [Hc1 Hc2]. apply Hns. right; left. lia.
          - intros [Hc1 Hc2]. apply Hns. right; left. lia. }
        exact (AC.a_laws_store _ _ _ _ _ LAWS (hb1 phi (flen g j) ++ g_H g) mem mem' md HAH Hst HwmL).
      - pose proof (bv_unsigned_in_range 64 FSw) as HFSr. change (bv_modulus 64) with (2 ^ 64) in HFSr.
        rewrite EFS in HFSr.
        assert (Hwm : word_mem rsegs mem (AC.as_tp AC.ASYMS) FS).
        { change (AC.as_tp AC.ASYMS) with RT_TP. rewrite <- EFS.
          exact (bytes_at_le8_word rsegs mem RT_TP FSw HFSw). }
        assert (Hfsz : FS + AC.FS_SIZE <= 2 ^ 64) by (unfold AC.FS_SIZE in *; lia).
        assert (Hmeta : forall q, fs_meta FS q -> outside
                          [(Sfr fr + 8, Sfr fr + 12); (sp - 2304, sp); (fr + 64, fr + 96)] q).
        { intros q Hq. pose proof (f34_fs_meta_range FS q Hq) as Hq12.
          pose proof (HFSb FS Hwm HFSr) as Hq3.
          assert (Happq : app_mem q) by (apply HFSapp; unfold AC.FS_SIZE in *; lia).
          cbn [outside]. split; [exact (HWsh q Happq)|]. split; [|split; [|exact I]].
          - intros [Hc1 Hc2]. unfold AC.FS_SIZE in *. lia.
          - intros [Hc1 Hc2]. lia. }
        assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
                  ~ AC.a_store_ok (hb1 phi (flen g j) ++ g_H g) (STKLO mem md) q ->
                  ~ (FS <= q < FS + AC.FS_SIZE) ->
                  ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) ->
                  mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
        { intros q Hq Hns Hnf Hnsh. apply MU. rewrite MState.unsigned_lit by lia. cbn [outside].
          split; [|split; [|split; [|exact I]]].
          - intros [Hc1 Hc2]. apply Hnsh. exists (fr + 8 * (q - Sfr fr)).
            split; [lia|]. rewrite f34_sh_frame_of by lia. unfold Sfr in *. lia.
          - intros [Hc1 Hc2]. apply Hns. right; left. lia.
          - intros [Hc1 Hc2]. apply Hnf. lia. }
        exact (a_fs_ok_store_AH AC.ASYMS _ _ _ _
                 [(Sfr fr + 8, Sfr fr + 12); (sp - 2304, sp); (fr + 64, fr + 96)]
                 (hb1 phi (flen g j) ++ g_H g) mem mem' md FS LAWS HAH Hwm HFSr Hfsz MU
                 (fun q _ Hw => WM _ Hw) (fun q Hq Hp => HpresM q Hq Hp) Hmeta Hagree). }
    destruct HAHS as (HAH' & HOWN & HSTK' & HSTKHI').
    assert (HSLOT' : forall a, fr + 64 <= a < fr + 96 -> exists b, mrd rsegs mem' (wa a) = Some b).
    { intros a Ha. apply (HINw a ltac:(lia)). cbn [outside]. intros (_ & _ & Hc & _). apply Hc. lia. }
    (* FRA and ENT across the write set and the lazy pages *)
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs' mem' md)
      by exact (f34_fra_w g fr (hb1 phi (flen g j)) regs regs' mem mem' md sp HFRA Haspz
                  MU WM RO' HAH' HSTK' SW' ST' HSLOT' F2 F3 F4 F8 F9 F19 F26).
    assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs' mem' md')
      by (apply (sl_fra_move B APIf ra g fr (hb1 phi (flen g j)) regs' regs' mem' md md' HFRA');
          try reflexivity; exact Hmat).
    assert (HENT' : ENT APIf g (hb1 phi (flen g j)) mem' md).
    { apply (ent_store B APIf ra g fr (hb1 phi (flen g j)) regs mem mem' md
               [(Sfr fr + 8, Sfr fr + 12); (sp - 2304, sp); (fr + 64, fr + 96)] HENT HFRA
               (proj1 (fr_munch_ul _ _ _) MU)).
      - intros x Hx.
        destruct (Z_le_gt_dec (Sfr fr + 8) x) as [L1|L1]; [destruct (Z_lt_ge_dec x (Sfr fr + 12)) as [L2|L2]|];
          [right; right; right; lia | |];
          (destruct (Z_le_gt_dec (fr + 64) x) as [L3|L3]; [destruct (Z_lt_ge_dec x (fr + 96)) as [L4|L4]|];
             [right; right; left; lia | |];
           (destruct (Z_le_gt_dec (sp - 2304) x) as [L5|L5]; [destruct (Z_lt_ge_dec x sp) as [L6|L6]|];
              [ right; left; lia
              | left; cbn [ULF.outside]; repeat split; try exact I; lia
              | left; cbn [ULF.outside]; repeat split; try exact I; lia ])).
      - exact HSTK'.
      - exact HSTKHI'.
      - intros a _ Ho. exact (proj2 (HOWN a) Ho). }
    pose proof (ent_mat APIf g _ mem' md md' HENT' Hmat) as HENT''.
    (* the block: app memory below stklo and off the frame, so apart from the write set *)
    pose proof HHB as (Hphinz & Hphiad). rewrite Hsz in Hphiad.
    assert (Hblkfr : forall x, phi <= x < phi + flen g j -> ~ (fr <= x < fr + 3136)).
    { intros x Hx Hc.
      exact (f34_fra_blk g fr (hb1 phi (flen g j)) regs mem md phi (flen g j) x HFRA
               ltac:(left; reflexivity) Hx Hc). }
    assert (Hblkapp : forall x, phi <= x < phi + flen g j -> app_mem x).
    { intros x Hx. replace x with (phi + (x - phi)) by lia.
      exact (proj1 (proj2 (proj2 (proj2 Hphiad)) (x - phi) ltac:(lia))). }
    assert (Hblkstk : phi + flen g j <= STKLO mem md).
    { destruct (AC.a_laws_blocks _ _ _ _ _ LAWS (hb1 phi (flen g j) ++ g_H g) mem md phi (flen g j) HAH
                  ltac:(left; reflexivity)) as (_ & _ & Hend & _). exact Hend. }
    assert (HblkW : forall x, phi <= x < phi + flen g j -> outside
                      [(Sfr fr + 8, Sfr fr + 12); (sp - 2304, sp); (fr + 64, fr + 96)] x).
    { intros x Hx. cbn [outside]. split; [exact (HWsh x (Hblkapp x Hx))|]. split; [|split; [|exact I]].
      - intros [Hc1 Hc2]. lia.
      - intros [Hc1 Hc2]. exact (Hblkfr x Hx ltac:(lia)). }
    assert (HHB' : HB mem' phi (flen g j)).
    { split; [exact Hphinz|]. rewrite Hsz.
      apply (f34_addr_keepW _ mem mem' phi (flen g j) Hphiad MU). intros k Hk.
      apply (f34_sh_outW fr sp (phi + k));
        [lia | exact Hfr8 | exact HWw | exact Hfrapp | exact (Hblkapp (phi + k) ltac:(lia)) |].
      intros Hc. exact (Hblkfr (phi + k) ltac:(lia) ltac:(lia)). }
    (* the frame above the slot, and its shadow, are apart from the write set *)
    assert (Kfr : forall x, fr + 96 <= x < fr + 3136 -> outside
                    [(Sfr fr + 8, Sfr fr + 12); (sp - 2304, sp); (fr + 64, fr + 96)] x).
    { intros x Hx. cbn [outside]. split; [exact (HWsh x (Hfrapp x ltac:(lia)))|].
      split; [exact (HWfrm x ltac:(lia))|]. split; [lia | exact I]. }
    assert (Kfrsh : forall x, fr + 96 <= x < fr + 3136 -> outside
                      [(Sfr fr + 8, Sfr fr + 12); (sp - 2304, sp); (fr + 64, fr + 96)] (shadow_addr x)).
    { intros x Hx.
      apply (f34_sh_outW fr sp x); [lia | exact Hfr8 | exact HWw | exact Hfrapp | apply Hfrapp; lia | lia]. }
    assert (Had' : addressable mem' (fr + 2624) 6).
    { apply (f34_addr_keepW _ mem mem' (fr + 2624) 6 Had2624 MU). intros k Hk. apply Kfrsh. lia. }
    assert (Had2691' : addressable mem' (fr + 2691) 17).
    { apply (f34_addr_keepW _ mem mem' (fr + 2691) 17 Had2691 MU). intros k Hk. apply Kfrsh. lia. }
    assert (Hadfg' : addressable mem' (fragb fr) 72).
    { apply (f34_addr_keepW _ mem mem' (fragb fr) 72 Hadfg MU). intros k Hk. apply Kfrsh. unfold fragb. lia. }
    assert (Hadrec' : addressable mem' (fr + 2688) 38).
    { apply (f34_addr_keepW _ mem mem' (fr + 2688) 38 Hadrec MU). intros k Hk. apply Kfrsh. lia. }
    assert (Hstk' : stk rsegs mem' fr (fr + 3136)).
    { destruct Hstkfr as (S0 & S1 & SS). split; [exact S0|]. split; [exact S1|].
      intros a Ha. split.
      - apply WM. exact (proj1 (SS a Ha)).
      - destruct (f34_outside_dec [(Sfr fr + 8, Sfr fr + 12); (sp - 2304, sp); (fr + 64, fr + 96)] a)
          as [Ho|Ho].
        + destruct (SS a Ha) as (_ & b & Hb). exists b.
          rewrite (f34_mrd_munch _ mem mem' a MU ltac:(lia) Ho). exact Hb.
        + exact (HINw a ltac:(lia) Ho). }
    (* FLSI's harness input block f1_IN: a live entry block (when it is not empty), below stklo, off the frame *)
    pose proof HIN as (HinH0 & Hinad & _).
    assert (Hpapp : forall x, g_p g <= x < g_p g + g_n g -> app_mem x).
    { intros x Hx. replace x with (g_p g + (x - g_p g)) by lia.
      exact (proj1 (proj2 (proj2 (proj2 Hinad)) (x - g_p g) ltac:(lia))). }
    assert (Hpblk : forall x, g_p g <= x < g_p g + g_n g ->
                      g_p g + g_n g <= STKLO mem md /\ ~ (fr <= x < fr + 3136)).
    { intros x Hx.
      assert (HinH : In (g_p g, g_n g) (hb1 phi (flen g j) ++ g_H g))
        by (apply in_or_app; right; apply HinH0; lia).
      destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md (g_p g) (g_n g) HAH HinH) as (_ & _ & HpEnd & _).
      split; [exact HpEnd|].
      intros Hc. exact (f34_fra_blk g fr (hb1 phi (flen g j)) regs mem md (g_p g) (g_n g) x HFRA HinH Hx Hc). }
    assert (HIN' : f1_IN g mem').
    { apply (f34_f1in_mem g mem mem' _ MU); [ | | exact HIN].
      - intros x Hx. destruct (Hpblk x Hx) as (HpEnd & Hpfr).
        cbn [outside]. split; [exact (HWsh x (Hpapp x Hx))|].
        split; [lia|]. split; [intros [Hc1 Hc2]; exact (Hpfr ltac:(lia)) | exact I].
      - intros x Hx. destruct (Hpblk x Hx) as (_ & Hpfr).
        apply (f34_sh_outW fr sp x); [lia | exact Hfr8 | exact HWw | exact Hfrapp | exact (Hpapp x Hx) |].
        intros Hc. exact (Hpfr ltac:(lia)). }
    (* the spill base and everything above it is apart from the write set *)
    assert (HWA_ : forall x, A <= x -> outside
                     [(Sfr fr + 8, Sfr fr + 12); (sp - 2304, sp); (fr + 64, fr + 96)] x).
    { intros x Hx. cbn [outside]. repeat split; try exact I; lia. }
    (* the exit cut's bundles *)
    pose proof (f34_flsi_mem g j fr regs regs' mem mem' _ A Hr9 (proj1 HAb) (proj2 HAb) F9 MU HWA_
                  Had' Hstk' Had2691' HIN' Hadfg' Hadrec' HFLSI) as HFLSI'.
    assert (HLK' : LK g fr j regs' mem').
    { apply (f34_lk_mem g fr j regs regs' mem mem' _ F21 MU); [|exact HLK].
      intros x Hx. apply Kfr. lia. }
    pose proof (f34_flsx_mem g j phi fr regs regs' mem mem' _ A Hr9 (proj1 HAb) (proj2 HAb)
                  F9 F18 F22 F23 F25 MU HWA_ HblkW HFLSI' HFLSX) as HFLSX'.
    assert (HWr : forall x, fr + 2688 <= x < fr + 2840 -> outside
                    [(Sfr fr + 8, Sfr fr + 12); (sp - 2304, sp); (fr + 64, fr + 96)] x)
      by (intros x Hx; apply Kfr; lia).
    assert (HWb : forall x, fr + 2880 <= x < fr + 2915 ->
                    outside [(Sfr fr + 8, Sfr fr + 12); (sp - 2304, sp); (fr + 64, fr + 96)] x /\
                    outside [(Sfr fr + 8, Sfr fr + 12); (sp - 2304, sp); (fr + 64, fr + 96)] (shadow_addr x))
      by (intros x Hx; split; [apply Kfr | apply Kfrsh]; lia).
    pose proof (f34_lt_mem g fr j regs regs' mem mem' _ A Hr9 (proj1 HAb) (proj2 HAb) F9 MU HWA_ HWr HWb
                  HLT) as HLT'.
    assert (HIexit : Inv_A82888_at B APIf ra g j i
                       (mkCfg (mkst regs' (Z_to_bv 64 0x82888) mem' (seg_rom rsegs)) md')).
    { exists phi, regs', mem', md', fr. rewrite SEGS, Hsz. split; [reflexivity|].
      split; [exact HFRA''|]. split; [exact HENT''|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB'|]. split; [exact HFLSI'|].
      split; [exact HLK'|]. split; [exact Hi10|].
      split.
      { split; [exact Hi10|].
        split; [unfold rg; exact F20|].
        split; [unfold rg; rewrite F24; exact H24|].
        split; [exact Hprev|]. split; [exact Hsel | exact HFLSX']. }
      split; [unfold rg; exact F10|].
      split; [exact BA'|]. split; [exact AD' | exact HLT']. }
    pose proof (Hexit g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End F34.
(* b8refit: applied map b8refit-v190.tsv sha256=7153b913f625df27 kinds=frame,pc,slot. Do not apply it again. *)
