(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec StepTac DriverCfg AllocNodesCfg FPInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Arr Image.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PDrvData PDrvMain PDrvCall PDrvHeap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Local Notation stk := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk.
Open Scope Z_scope.

Section FuzzGlue.
Variable HI : heap_iface.
Variables GP TP : word.
Variables IMG_LO IMG_END HTOP : Z.
Variable STATIC : list ivl.
Hypothesis HOK : heap_ok PSEGS DCFG HI GP TP IMG_LO IMG_END HTOP STATIC CELLS_NE 0x51310 8192 0x511d0 8192.
(* [comment removed for export] *)
Variables (FNZ : Z) (RO : list (Z * Z)).
Hypothesis HFZ : fuzz_contract PSEGS DCFG (hi_HS HI) (hi_Heap HI) (hi_blocks HI) GP TP IMG_LO IMG_END HTOP STATIC CELLS_NE 0x22b18 FNZ RO.

#[using="HOK HFZ"] Theorem fx_fuzz : forall E L ms md hs (size : Z) (i0 i7 : nat) (o0 : Z) (sp : Z) R7 K,
  sden PSEGS E L ms -> s_pc L = 0x22b18 -> s_resv L = RNone -> ms_rom ms = seg_rom PSEGS ->
  havoc_ok L [(i0, o0, FNZ); (i7, 4, 4)] (Some (lconst 0)) = true ->
  nth_error (s_rgs L) i7 = Some R7 -> bv_unsigned (lden E (rg_base R7)) = 0x75b28 ->
  hi_Heap HI hs (ms_mem ms) md -> md_ok md -> U md + FUZZ_CHARGE <= UBOUND ->
  getr (ms_regs ms) 11 = Z_to_bv 64 size -> 0 <= size < 2 ^ 26 ->
  (size = 0 \/ In (bv_unsigned (getr (ms_regs ms) 10), size) (hi_blocks HI hs)) ->
  bv_unsigned (getr (ms_regs ms) 1) mod 2 = 0 -> getr (ms_regs ms) 3 = GP -> getr (ms_regs ms) 4 = TP ->
  getr (ms_regs ms) 2 = Z_to_bv 64 sp -> sp mod 16 = 0 -> 0 < FNZ -> 0xa0000 <= sp - FNZ -> sp <= 2 ^ 47 -> HTOP <= sp - FNZ ->
  frame_in E L i0 o0 FNZ (sp - FNZ) -> avoid_heap3 IMG_LO IMG_END HTOP STATIC E (s_rgs L) ->
  Forall (fun r => pristine (ms_mem ms) (fst r) (snd r)) RO ->
  (forall E' ms' md' hs', agree (s_next L) E E' ->
      sden PSEGS E' (havoc_call L (bv_unsigned (getr (ms_regs ms) 1)) KEEPH [(i0, o0, FNZ); (i7, 4, 4)] (Some (lconst 0))) ms' ->
      ms_rom ms' = ms_rom ms ->
      hi_Heap HI hs' (ms_mem ms') md' -> md_ok md' -> vm_only md md' -> U md' <= U md + FUZZ_CHARGE ->
      blocks_same (hi_blocks HI hs) (hi_blocks HI hs') ->
      munch (STATIC ++ [(0, IMG_LO); (IMG_END, HTOP); (sp - FNZ, sp)]) (ms_mem ms) (ms_mem ms') ->
      (forall p n, In (p, n) (hi_blocks HI hs) -> forall a, p <= a < p + n -> ms_mem ms' (wa a) = ms_mem ms (wa a)) ->
      (forall a, (0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48) -> ms_mem ms' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
      realizes PSEGS (mkCfg ms' md') K) ->
  realizes PSEGS (mkCfg ms md) K.
Proof. LiaFast.lf_pins (fun (HOK HFZ : LiaFast.U) => LiaFast.u0).
  intros E L ms md hs size i0 i7 o0 sp R7 K Hd Hpc Hrv Hrom Hok Hi7 Hb7 Hheap Hmd HU H11 Hsz Hpay Hra H3 H4 H2 Hs16 Hfnz Hslo Hshi Htop Hfr Hav HRO Hk.
  pose proof HOK as ((HB1 & HST) & _ & _ & _ & Hblk).
  rewrite (sden_mkst PSEGS E L ms Hd Hrv). rewrite Hpc, Hrom.
  set (regs := ms_regs ms) in *. set (mem := ms_mem ms) in *. set (rom := seg_rom PSEGS) in *.
  set (fxs := mkFP (ms_fregs ms) (ms_fcsr ms)).
  assert (HSP : sp_of regs = sp) by (unfold sp_of; rewrite H2; apply u_small64; unfold two64; lia).
  destruct Hfr as (R0 & Hi0 & Ha0 & Hwk0 & Ho0 & Hn0).
  pose proof (sden_rg _ _ _ _ _ _ Hd Hi0) as HR0.
  assert (Hstk : stk PSEGS mem (sp - FNZ) sp).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (rg_ok_rw_byte PSEGS E _ R0 HR0 Hwk0 (o0 + (a - (sp - FNZ))) ltac:(lia)) as [Hr Hw].
    replace (bv_unsigned (lden E (rg_base R0)) + (o0 + (a - (sp - FNZ)))) with a in Hr, Hw by lia.
    split; [exact Hw|]. unfold mrd, wa. unfold rd1 in Hr. change (ms_mem ms) with mem in Hr.
    destruct (match mem (Z_to_bv 64 a) with Some b => Some b | None => seg_rom PSEGS (Z_to_bv 64 a) end) as [b|] eqn:He;
      [exists b; reflexivity | exfalso; exact (Hr eq_refl)]. }
  assert (Hfrm : frm0 (@fp_csr fxs)) by exact (sden_frm _ _ _ _ Hd).
  apply (HFZ fxs regs mem md hs size (getr regs 1) K Hheap Hmd HU H11 Hsz Hpay eq_refl Hra H3 H4 ltac:(rewrite HSP; exact Hs16)
           ltac:(rewrite HSP; exact Hshi) ltac:(rewrite HSP; exact Htop) ltac:(rewrite HSP; exact Hstk) Hfrm HRO).
  intros fx' regs' m' md' hs' Hheap' Hmd' Hvo HU' Hkeep H10' Hcs Hfc Hsame Hmunch Hblks Hstk'.
  assert (Hcells : forall a, (0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48) -> m' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha. apply Hkeep. cbn [ioutside CELLS_NE]. intros (A & B & _). destruct Ha as [Ha|Ha]; [exact (A Ha) | exact (B Ha)]. }
  rewrite HSP in Hmunch, Hstk'.
  set (ms' := @mkst fx' regs' (getr regs 1) m' rom).
  assert (P1 : ms_pc_val ms' = Z_to_bv 64 (bv_unsigned (getr regs 1))) by (unfold ms', mkst; cbn [ms_pc_val]; symmetry; apply Z_to_bv_bv_unsigned).
  assert (P2 : forall r : reg, existsb (Pos.eqb (rkey r)) KEEPH = true -> rkey r <> 11%positive \/ Some (lconst 0) = @None lin ->
                 getr (ms_regs ms') r = getr regs r).
  { intros r Hr _. unfold ms', mkst; cbn [ms_regs]. exact (keeph_cs regs regs' r Hcs Hr). }
  assert (P3 : forall l, Some (lconst 0) = Some l -> getr (ms_regs ms') (Z_to_bv 5 10) = lden E l).
  { intros l Hl. injection Hl as <-. unfold ms', mkst; cbn [ms_regs]. rewrite lden_lconst. exact H10'. }
  assert (Hout : forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x -> ~ in_fp E (s_rgs L) [(i0, o0, FNZ); (i7, 4, 4)] x ->
                   m' x = mem x).
  { intros i R x Hi Hin Hnf.
    destruct (HIface.outside_dec CELLS_NE (bv_unsigned x)) as [Hc1|Hc1].
    - destruct (HIface.outside_dec ERRC (bv_unsigned x)) as [Hc2|Hc2].
      + assert (Hc : ioutside (CELLS_NE ++ ERRC) (bv_unsigned x)) by (apply HIface.outside_app; split; assumption).
        apply Hmunch. apply HIface.outside_app.
        pose proof (bv_unsigned_in_range _ x) as Rx. unfold bv_modulus in Rx. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rx.
        destruct (Hav i R x Hi Hin Hc) as [A|(A & B)].
        * split.
          -- destruct (HIface.outside_dec STATIC (bv_unsigned x)) as [S|S]; [exact S|]. exfalso. pose proof (HST _ S). lia.
          -- cbn [ioutside]. split; [lia|]. split; [lia|]. split; [|exact I].
             intros Hx. apply Hnf. exists i0, o0, FNZ, R0. split; [left; reflexivity|]. split; [exact Hi0|]. lia.
        * split; [exact B|]. cbn [ioutside]. split; [lia|]. split; [lia|]. split; [|exact I].
          intros Hx. apply Hnf. exists i0, o0, FNZ, R0. split; [left; reflexivity|]. split; [exact Hi0|]. lia.
      + exfalso. apply Hnf. exists i7, 4, 4, R7. split; [right; left; reflexivity|]. split; [exact Hi7|]. rewrite Hb7.
        cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside ERRC] in Hc2. lia.
    - rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hcells. cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside CELLS_NE] in Hc1.
      destruct (Z_le_gt_dec 0x63da0 (bv_unsigned x)); destruct (Z_lt_ge_dec (bv_unsigned x) 0x63da8); [left; lia | | |];
        destruct (Z_le_gt_dec 0x95e40 (bv_unsigned x)); destruct (Z_lt_ge_dec (bv_unsigned x) 0x95e48); try (right; lia);
        exfalso; apply Hc1; repeat split; lia. }
  assert (P4 : forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x -> ~ in_fp E (s_rgs L) [(i0, o0, FNZ); (i7, 4, 4)] x ->
                 ms_mem ms' x = ms_mem ms x) by (intros i R x Hi Hrx Hnf; unfold ms', mkst; cbn [ms_mem]; exact (Hout i R x Hi Hrx Hnf)).
  assert (P5 : forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x ->
                 (rd1 PSEGS (ms_mem ms) x <> None -> rd1 PSEGS (ms_mem ms') x <> None) /\
                 (wview PSEGS (ms_mem ms) x <> None -> wview PSEGS (ms_mem ms') x <> None)).
  { intros i R x Hi Hrx. unfold ms', mkst; cbn [ms_mem].
    destruct (HIface.outside_dec ERRC (bv_unsigned x)) as [Hc2|Hc2].
    - destruct (Z_le_gt_dec (sp - FNZ) (bv_unsigned x)) as [A|A]; [destruct (Z_lt_ge_dec (bv_unsigned x) sp) as [B|B]|].
      + destruct Hstk' as (_ & _ & HS). destruct (HS (bv_unsigned x) ltac:(lia)) as [Hw (b & Hb)]. unfold wa in Hw, Hb.
        rewrite Z_to_bv_bv_unsigned in Hw, Hb. unfold mrd in Hb. unfold rd1. split; intros _; [rewrite Hb; discriminate | exact Hw].
      + unfold rd1, wview. rewrite (Hout i R x Hi Hrx); [tauto|]. intros (j & o & k & R' & Hj & Hnj & Hx). destruct Hj as [Hj|[Hj|[]]]; injection Hj as <- <- <-.
        * rewrite Hi0 in Hnj. injection Hnj as <-. lia.
        * rewrite Hi7 in Hnj. injection Hnj as <-. rewrite Hb7 in Hx. cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside ERRC] in Hc2. lia.
      + unfold rd1, wview. rewrite (Hout i R x Hi Hrx); [tauto|]. intros (j & o & k & R' & Hj & Hnj & Hx). destruct Hj as [Hj|[Hj|[]]]; injection Hj as <- <- <-.
        * rewrite Hi0 in Hnj. injection Hnj as <-. lia.
        * rewrite Hi7 in Hnj. injection Hnj as <-. rewrite Hb7 in Hx. cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside ERRC] in Hc2. lia.
    - cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside ERRC] in Hc2.
      assert (Hx : 0x75b2c <= bv_unsigned x < 0x75b30).
      { apply Decidable.not_not; [unfold Decidable.decidable; lia|]. intros C. apply Hc2. split; [exact C | exact I]. }
      assert (HS : seg_rom PSEGS x <> None /\ wview PSEGS (fun _ => None) x <> None).
      { rewrite <- (Z_to_bv_bv_unsigned _ x).
        assert (Q : bv_unsigned x = 0x75b2c \/ bv_unsigned x = 0x75b2d \/ bv_unsigned x = 0x75b2e \/ bv_unsigned x = 0x75b2f) by lia.
        destruct Q as [Q|[Q|[Q|Q]]]; rewrite Q; vm_compute; split; discriminate. }
      destruct HS as [HS1 HS2]. unfold rd1, wview in *. split; intros _; destruct (m' x); [discriminate | exact HS1 | discriminate | exact HS2]. }
  assert (P6 : frm_zero (ms_fcsr ms')) by (unfold ms', mkst; cbn [ms_fcsr]; exact Hfc).
  destruct (havoc_call_sound2 PSEGS E L ms ms' (bv_unsigned (getr regs 1)) KEEPH [(i0, o0, FNZ); (i7, 4, 4)] (Some (lconst 0)) Hok Hd P1 eq_refl eq_refl
              P6 P2 P3 P4 P5) as (E' & Ha' & Hd').
  apply (Hk E' ms' md' hs' Ha' Hd' ltac:(unfold ms', mkst; cbn [ms_rom]; symmetry; exact Hrom) Hheap' Hmd' Hvo HU' Hsame).
  - unfold ms', mkst; cbn [ms_mem]. exact Hmunch.
  - intros p n Hpn a Ha. unfold ms', mkst; cbn [ms_mem]. exact (Hblks p n Hpn a Ha).
  - exact Hcells.
Qed.
(* [comment removed for export] *)
#[using="HOK"] Theorem fx_free_g : forall E L ms md hs (n : Z) (i0 i7 : nat) (o0 : Z) (sp : Z) R7 K,
  sden PSEGS E L ms -> s_pc L = 0x511d0 -> s_resv L = RNone -> ms_rom ms = seg_rom PSEGS ->
  havoc_ok L [(i0, o0, 8192); (i7, 4, 4)] None = true ->
  nth_error (s_rgs L) i7 = Some R7 -> bv_unsigned (lden E (rg_base R7)) = 0x75b28 ->
  hi_Heap HI hs (ms_mem ms) md -> md_ok md ->
  forall (pb : Z), getr (ms_regs ms) 10 = Z_to_bv 64 pb -> (pb = 0 /\ n = 0) \/ (In (pb, n) (hi_blocks HI hs) /\ pb <> 0) ->
  bv_unsigned (getr (ms_regs ms) 1) mod 2 = 0 -> getr (ms_regs ms) 3 = GP -> getr (ms_regs ms) 4 = TP ->
  getr (ms_regs ms) 2 = Z_to_bv 64 sp -> sp mod 16 = 0 -> 0xa0000 <= sp - 8192 -> sp <= 2 ^ 47 -> HTOP <= sp - 8192 ->
  frame_in E L i0 o0 8192 (sp - 8192) -> avoid_heap3 IMG_LO IMG_END HTOP STATIC E (s_rgs L) ->
  (forall E' ms' md' hs', agree (s_next L) E E' ->
      sden PSEGS E' (havoc_call L (bv_unsigned (getr (ms_regs ms) 1)) KEEPH [(i0, o0, 8192); (i7, 4, 4)] None) ms' -> ms_rom ms' = ms_rom ms ->
      hi_Heap HI hs' (ms_mem ms') md' -> md_ok md' -> vm_only md md' -> U md' <= U md ->
      (if pb =? 0 then blocks_same (hi_blocks HI hs) (hi_blocks HI hs') else blocks_del (hi_blocks HI hs) (hi_blocks HI hs') (pb, n)) ->
      munch (hi_owned HI hs ++ hi_owned HI hs' ++ [(pb, pb + n); (sp - 8192, sp)]) (ms_mem ms) (ms_mem ms') ->
      (forall a, (0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48) -> ms_mem ms' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
      realizes PSEGS (mkCfg ms' md') K) ->
  realizes PSEGS (mkCfg ms md) K.
Proof. LiaFast.lf_pins (fun (HOK : LiaFast.U) => LiaFast.u0).
  intros E L ms md hs n i0 i7 o0 sp R7 K Hd Hpc Hrv Hrom Hok Hi7 Hb7 Hheap Hmd pb H10 Hpb Hra H3 H4 H2 Hs16 Hslo Hshi Htop Hfr Hav Hk.
  assert (Hor : pb = 0 \/ In (pb, n) (hi_blocks HI hs)) by (destruct Hpb as [[A _]|[A _]]; [left; exact A | right; exact A]).
  pose proof HOK as (_ & _ & HF & _ & Hblk).
  rewrite (sden_mkst PSEGS E L ms Hd Hrv). rewrite Hpc, Hrom.
  set (regs := ms_regs ms) in *. set (mem := ms_mem ms) in *. set (rom := seg_rom PSEGS) in *.
  set (fxs := mkFP (ms_fregs ms) (ms_fcsr ms)).
  assert (HSP : sp_of regs = sp) by (unfold sp_of; rewrite H2; apply u_small64; unfold two64; lia).
  destruct Hfr as (R0 & Hi0 & Ha0 & Hwk0 & Ho0 & Hn0).
  pose proof (sden_rg _ _ _ _ _ _ Hd Hi0) as HR0.
  assert (Hstk : stk PSEGS mem (sp - 8192) sp).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (rg_ok_rw_byte PSEGS E _ R0 HR0 Hwk0 (o0 + (a - (sp - 8192))) ltac:(lia)) as [Hr Hw].
    replace (bv_unsigned (lden E (rg_base R0)) + (o0 + (a - (sp - 8192)))) with a in Hr, Hw by lia.
    split; [exact Hw|]. unfold mrd, wa. unfold rd1 in Hr. change (ms_mem ms) with mem in Hr.
    destruct (match mem (Z_to_bv 64 a) with Some b => Some b | None => seg_rom PSEGS (Z_to_bv 64 a) end) as [b|] eqn:He;
      [exists b; reflexivity | exfalso; exact (Hr eq_refl)]. }
  apply (HF fxs regs mem md hs pb n (getr regs 1) K Hheap Hmd H10 Hor eq_refl Hra H3 H4 ltac:(rewrite HSP; exact Hs16)
           ltac:(rewrite HSP; exact Hshi) ltac:(rewrite HSP; exact Htop) ltac:(rewrite HSP; exact Hstk)).
  intros fx' regs' m' md' hs' Hfc Hheap' Hmd' Hvo HU' Hkeep Hdel Hcs Hmunch Hstk'.
  assert (Hcells : forall a, (0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48) -> m' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha. apply Hkeep. cbn [ioutside CELLS_NE]. intros (A & B & _). destruct Ha as [Ha|Ha]; [exact (A Ha) | exact (B Ha)]. }
  rewrite HSP in Hmunch, Hstk'.
  set (ms' := @mkst fx' regs' (getr regs 1) m' rom).
  assert (P1 : ms_pc_val ms' = Z_to_bv 64 (bv_unsigned (getr regs 1))) by (unfold ms', mkst; cbn [ms_pc_val]; symmetry; apply Z_to_bv_bv_unsigned).
  assert (P2 : forall r : reg, existsb (Pos.eqb (rkey r)) KEEPH = true -> rkey r <> 11%positive \/ None = @None lin ->
                 getr (ms_regs ms') r = getr regs r).
  { intros r Hr _. unfold ms', mkst; cbn [ms_regs]. exact (keeph_cs regs regs' r Hcs Hr). }
  assert (P3 : forall l, None = Some l -> getr (ms_regs ms') (Z_to_bv 5 10) = lden E l) by (intros l Hc; discriminate Hc).
  assert (Hout : forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x -> ~ in_fp E (s_rgs L) [(i0, o0, 8192); (i7, 4, 4)] x ->
                   m' x = mem x).
  { intros i R x Hi Hin0 Hnf. rename Hin0 into Hin0'. pose proof Hin0' as Hin0.
    destruct (HIface.outside_dec CELLS_NE (bv_unsigned x)) as [Hc1|Hc1].
    - destruct (HIface.outside_dec ERRC (bv_unsigned x)) as [Hc2|Hc2].
      + assert (Hc : ioutside (CELLS_NE ++ ERRC) (bv_unsigned x)) by (apply HIface.outside_app; split; assumption).
        apply Hmunch. apply HIface.outside_app. split; [exact (avoid_owned HI GP TP IMG_LO IMG_END HTOP STATIC HOK E L hs mem md i R x Hav Hheap Hi Hin0 Hc)|].
        apply HIface.outside_app. split; [exact (avoid_owned HI GP TP IMG_LO IMG_END HTOP STATIC HOK E L hs' m' md' i R x Hav Hheap' Hi Hin0 Hc)|].
        cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside]. split; [destruct Hpb as [(-> & ->)|(Hin & _)]; [lia | exact (avoid_block HI GP TP IMG_LO IMG_END HTOP STATIC HOK E L hs mem md i R x pb n Hav Hheap Hin Hi Hin0 Hc)]|]. split; [|exact I].
        intros Hx. apply Hnf. exists i0, o0, 8192, R0. split; [left; reflexivity|]. split; [exact Hi0|]. lia.
      + exfalso. apply Hnf. exists i7, 4, 4, R7. split; [right; left; reflexivity|]. split; [exact Hi7|]. rewrite Hb7.
        cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside ERRC] in Hc2. lia.
    - rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hcells. cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside CELLS_NE] in Hc1.
      destruct (Z_le_gt_dec 0x63da0 (bv_unsigned x)); destruct (Z_lt_ge_dec (bv_unsigned x) 0x63da8); [left; lia | | |];
        destruct (Z_le_gt_dec 0x95e40 (bv_unsigned x)); destruct (Z_lt_ge_dec (bv_unsigned x) 0x95e48); try (right; lia);
        exfalso; apply Hc1; repeat split; lia. }
  assert (P4 : forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x -> ~ in_fp E (s_rgs L) [(i0, o0, 8192); (i7, 4, 4)] x ->
                 ms_mem ms' x = ms_mem ms x) by (intros i R x Hi Hrx Hnf; unfold ms', mkst; cbn [ms_mem]; exact (Hout i R x Hi Hrx Hnf)).
  assert (P5 : forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x ->
                 (rd1 PSEGS (ms_mem ms) x <> None -> rd1 PSEGS (ms_mem ms') x <> None) /\
                 (wview PSEGS (ms_mem ms) x <> None -> wview PSEGS (ms_mem ms') x <> None)).
  { intros i R x Hi Hrx. unfold ms', mkst; cbn [ms_mem].
    destruct (HIface.outside_dec ERRC (bv_unsigned x)) as [Hc2|Hc2].
    - destruct (Z_le_gt_dec (sp - 8192) (bv_unsigned x)) as [A|A]; [destruct (Z_lt_ge_dec (bv_unsigned x) sp) as [B|B]|].
      + destruct Hstk' as (_ & _ & HS). destruct (HS (bv_unsigned x) ltac:(lia)) as [Hw (b & Hb)]. unfold wa in Hw, Hb.
        rewrite Z_to_bv_bv_unsigned in Hw, Hb. unfold mrd in Hb. unfold rd1. split; intros _; [rewrite Hb; discriminate | exact Hw].
      + unfold rd1, wview. rewrite (Hout i R x Hi Hrx); [tauto|]. intros (j & o & k & R' & Hj & Hnj & Hx). destruct Hj as [Hj|[Hj|[]]]; injection Hj as <- <- <-.
        * rewrite Hi0 in Hnj. injection Hnj as <-. lia.
        * rewrite Hi7 in Hnj. injection Hnj as <-. rewrite Hb7 in Hx. cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside ERRC] in Hc2. lia.
      + unfold rd1, wview. rewrite (Hout i R x Hi Hrx); [tauto|]. intros (j & o & k & R' & Hj & Hnj & Hx). destruct Hj as [Hj|[Hj|[]]]; injection Hj as <- <- <-.
        * rewrite Hi0 in Hnj. injection Hnj as <-. lia.
        * rewrite Hi7 in Hnj. injection Hnj as <-. rewrite Hb7 in Hx. cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside ERRC] in Hc2. lia.
    - (* [comment removed for export] *)
      cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside ERRC] in Hc2.
      assert (Hx : 0x75b2c <= bv_unsigned x < 0x75b30).
      { apply Decidable.not_not; [unfold Decidable.decidable; lia|]. intros C. apply Hc2. split; [exact C | exact I]. }
      assert (HS : seg_rom PSEGS x <> None /\ wview PSEGS (fun _ => None) x <> None).
      { rewrite <- (Z_to_bv_bv_unsigned _ x).
        assert (Q : bv_unsigned x = 0x75b2c \/ bv_unsigned x = 0x75b2d \/ bv_unsigned x = 0x75b2e \/ bv_unsigned x = 0x75b2f) by lia.
        destruct Q as [Q|[Q|[Q|Q]]]; rewrite Q; vm_compute; split; discriminate. }
      destruct HS as [HS1 HS2]. unfold rd1, wview in *. split; intros _; destruct (m' x); [discriminate | exact HS1 | discriminate | exact HS2]. }
  assert (P6 : frm_zero (ms_fcsr ms')) by (unfold ms', mkst; cbn [ms_fcsr]; rewrite Hfc; exact (sden_frm _ _ _ _ Hd)).
  destruct (havoc_call_sound2 PSEGS E L ms ms' (bv_unsigned (getr regs 1)) KEEPH [(i0, o0, 8192); (i7, 4, 4)] None Hok Hd P1 eq_refl eq_refl
              P6 P2 P3 P4 P5) as (E' & Ha' & Hd').
  apply (Hk E' ms' md' hs' Ha' Hd' ltac:(unfold ms', mkst; cbn [ms_rom]; symmetry; exact Hrom) Hheap' Hmd' Hvo HU' Hdel).
  - unfold ms', mkst; cbn [ms_mem]. exact Hmunch.
  - exact Hcells.
Qed.
End FuzzGlue.
