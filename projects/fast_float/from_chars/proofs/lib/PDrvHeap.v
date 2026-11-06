(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec StepTac DriverCfg AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Arr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PDrvData PDrvMain PDrvCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Local Notation stk := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition KEEPH : list positive := List.map rkey ([2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv : list reg).

Lemma keeph_cs : forall regs regs' (r : reg), HIface.callee_saved regs regs' -> existsb (Pos.eqb (rkey r)) KEEPH = true ->
  getr regs' r = getr regs r.
Proof.
  intros regs regs' r Hc Hr. unfold KEEPH in Hr. apply existsb_exists in Hr as (k & Hk & Hx). apply Pos.eqb_eq in Hx.
  apply in_map_iff in Hk as (r' & <- & Hr'). rewrite (rkey_inj r r' Hx).
  destruct Hc as (A2 & A3 & A4 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
  repeat (destruct Hr' as [<-|Hr']; [assumption|]). destruct Hr'.
Qed.

(* [comment removed for export] *)
Definition CELLS_NE : list ivl := [(0x63da0, 0x63da8); (0x95e40, 0x95e48)].
Definition ERRC : list ivl := [(0x75b2c, 0x75b30)].

(* [comment removed for export] *)
Definition UB0 : Z := 2 ^ 28.                          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition UOK (cap : Z) (md : Model) : Prop :=
  exists j : nat, (j <= 10)%nat /\ cap = 65536 * 2 ^ Z.of_nat j /\ U md <= UB0 + 2 * cap + 2 ^ 21 * (Z.of_nat j + 1).
Definition UCAP : Z := UB0 + 2 ^ 27 + 11 * 2 ^ 21.     (* [comment removed for export] *)
Lemma uok_ucap : forall cap md, UOK cap md -> U md <= UCAP.
Proof.
  intros cap md (j & Hj & -> & HU). unfold UCAP.
  assert (H2 : 2 ^ Z.of_nat j <= 2 ^ 10) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
Lemma uok_same : forall cap md md', UOK cap md -> U md' <= U md -> UOK cap md'.
Proof. intros cap md md' (j & Hj & Hc & HU) H. exists j. split; [exact Hj|]. split; [exact Hc | lia]. Qed.
Lemma U_with_fds : forall f md, U (with_fds f md) = U md.
Proof. intros f md. reflexivity. Qed.

Section HeapGlue.
Variable HI : heap_iface.
Variables GP TP : word.
Variables IMG_LO IMG_END HTOP : Z.
Variable STATIC : list ivl.
Hypothesis HOK : heap_ok PSEGS DCFG HI GP TP IMG_LO IMG_END HTOP STATIC CELLS_NE 0x51310 8192 0x511d0 8192.


(* [comment removed for export] *)
Definition malloc_contract_md (PCM NEED : Z) : Prop :=
  forall (fx : FPState) regs m md hs (n : Z) (ret : word) (K : TSet),
    hi_Heap HI hs m md -> md_ok md -> (U md + MCHARGE n <= UBOUND)%Z ->
    getr regs 10 = Z_to_bv 64 n -> (1 <= n <= 2^26)%Z ->
    getr regs 1 = ret -> (bv_unsigned ret mod 2 = 0)%Z ->
    getr regs 3 = GP -> getr regs 4 = TP ->
    (sp_of regs mod 16 = 0)%Z -> (sp_of regs <= 2^47)%Z -> (HTOP <= sp_of regs - NEED)%Z ->
    stk PSEGS m (sp_of regs - NEED) (sp_of regs) ->
    (forall (fx' : FPState) regs' m' md' hs' (p : Z),
       @fp_csr fx' = @fp_csr fx -> hi_Heap HI hs' m' md' -> md_ok md' -> vm_only md md' -> (U md' <= U md + MCHARGE n)%Z ->
       getr regs' 10 = Z_to_bv 64 p -> (p mod 16 = 0)%Z ->
       blocks_add (hi_blocks HI hs) (hi_blocks HI hs') (p, n) -> ~ In (p, n) (hi_blocks HI hs) ->
       HIface.callee_saved regs regs' ->
       munch (hi_owned HI hs ++ hi_owned HI hs' ++ [(p, p + n); (sp_of regs - NEED, sp_of regs)]%Z) m m' ->
       (forall a, (0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48)%Z -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
       stk PSEGS m' (sp_of regs - NEED) (sp_of regs) ->
       realizes_cfg PSEGS DCFG (mkCfg (@mkst fx' regs' ret m' (seg_rom PSEGS)) md') K) ->
    realizes_cfg PSEGS DCFG (mkCfg (@mkst fx regs (Z_to_bv 64 PCM) m (seg_rom PSEGS)) md) K.
#[using="IMG_LO IMG_END STATIC HOK"] Lemma HMMD : malloc_contract_md 0x51310 8192.
Proof. LiaFast.lf_pins (fun (IMG_LO IMG_END STATIC HOK : LiaFast.U) => LiaFast.u0).
  pose proof HOK as (_ & HM & _). intros fx regs m md hs n ret K Hh Hmd HU H10 Hn H1 Hra H3 H4 Hs16 Hs47 Htop Hstk Hk.
  apply (HM fx regs m md hs n ret K Hh Hmd HU H10 Hn H1 Hra H3 H4 Hs16 Hs47 Htop Hstk).
  intros fx' regs' m' md' hs' p Hfc Hh' Hmd' Hvo HU' Hkeep H10' Hp16 Hadd Hnin Hcs Hmunch Hstk'.
  apply (Hk fx' regs' m' md' hs' p Hfc Hh' Hmd' Hvo HU' H10' Hp16 Hadd Hnin Hcs Hmunch); [| exact Hstk'].
  intros a Ha. apply Hkeep. cbn [ioutside CELLS_NE]. intros (A & B & _). destruct Ha as [Ha|Ha]; [exact (A Ha) | exact (B Ha)].
Qed.

(* [comment removed for export] *)
Definition avoid_heap3 (E : valu) (rgs : list region) : Prop :=
  forall i R x, nth_error rgs i = Some R -> in_rg E R x -> ioutside (CELLS_NE ++ ERRC) (bv_unsigned x) ->
    HTOP <= bv_unsigned x \/ (IMG_LO <= bv_unsigned x < IMG_END /\ ioutside STATIC (bv_unsigned x)).

#[using="GP TP HOK"] Lemma avoid_owned : forall E L hs m md i R x, avoid_heap3 E (s_rgs L) -> hi_Heap HI hs m md ->
  nth_error (s_rgs L) i = Some R -> in_rg E R x -> ioutside (CELLS_NE ++ ERRC) (bv_unsigned x) -> ioutside (hi_owned HI hs) (bv_unsigned x).
Proof. LiaFast.lf_pins (fun (GP TP HOK : LiaFast.U) => LiaFast.u0).
  intros E L hs m md i R x Hav Hh Hi Hin Hc. destruct HOK as (_ & _ & _ & _ & Hblk).
  destruct (Hblk hs m md Hh) as (_ & Hown). destruct (HIface.outside_dec (hi_owned HI hs) (bv_unsigned x)) as [A|A]; [exact A|].
  exfalso. destruct (Hown _ A) as (H1 & H2). destruct (Hav i R x Hi Hin Hc) as [H3|(H3 & H4)]; [lia|]. destruct H2 as [H2|[H2|H2]]; [exact (H2 H4) | lia | lia].
Qed.

#[using="GP TP HOK"] Lemma avoid_block : forall E L hs m md i R x p n, avoid_heap3 E (s_rgs L) -> hi_Heap HI hs m md -> In (p, n) (hi_blocks HI hs) ->
  nth_error (s_rgs L) i = Some R -> in_rg E R x -> ioutside (CELLS_NE ++ ERRC) (bv_unsigned x) -> ~ (p <= bv_unsigned x < p + n).
Proof. LiaFast.lf_pins (fun (GP TP HOK : LiaFast.U) => LiaFast.u0).
  intros E L hs m md i R x p n Hav Hh Hb Hi Hin Hc Hx. destruct HOK as ((B1 & B2) & _ & _ & _ & Hblk).
  destruct (Hblk hs m md Hh) as (Hbl & _). destruct (Hbl p n Hb) as (_ & Hr & _).
  destruct (Hav i R x Hi Hin Hc) as [H3|(H3 & H4)]; lia.
Qed.

#[using="HOK"] Theorem fx_malloc : forall E L ms md hs (n : Z) (i0 i7 : nat) (o0 : Z) (sp : Z) R7 K,
  sden PSEGS E L ms -> s_pc L = 0x51310 -> s_resv L = RNone -> ms_rom ms = seg_rom PSEGS ->
  havoc_ok L [(i0, o0, 8192); (i7, 4, 4)] None = true ->
  nth_error (s_rgs L) i7 = Some R7 -> bv_unsigned (lden E (rg_base R7)) = 0x75b28 ->
  hi_Heap HI hs (ms_mem ms) md -> md_ok md -> U md + MCHARGE n <= UBOUND ->
  getr (ms_regs ms) 10 = Z_to_bv 64 n -> 1 <= n <= 2 ^ 26 ->
  bv_unsigned (getr (ms_regs ms) 1) mod 2 = 0 -> getr (ms_regs ms) 3 = GP -> getr (ms_regs ms) 4 = TP ->
  getr (ms_regs ms) 2 = Z_to_bv 64 sp -> sp mod 16 = 0 -> 0xa0000 <= sp - 8192 -> sp <= 2 ^ 47 -> HTOP <= sp - 8192 ->
  frame_in E L i0 o0 8192 (sp - 8192) -> avoid_heap3 E (s_rgs L) ->
  (forall E' ms' md' hs' (p : Z), agree (s_next L) E E' ->
      sden PSEGS E' (havoc_call L (bv_unsigned (getr (ms_regs ms) 1)) KEEPH [(i0, o0, 8192); (i7, 4, 4)] None) ms' -> ms_rom ms' = ms_rom ms ->
      hi_Heap HI hs' (ms_mem ms') md' -> md_ok md' -> vm_only md md' -> U md' <= U md + MCHARGE n ->
      getr (ms_regs ms') 10 = Z_to_bv 64 p -> p mod 16 = 0 ->
      blocks_add (hi_blocks HI hs) (hi_blocks HI hs') (p, n) -> ~ In (p, n) (hi_blocks HI hs) ->
      munch (hi_owned HI hs ++ hi_owned HI hs' ++ [(p, p + n); (sp - 8192, sp)]) (ms_mem ms) (ms_mem ms') ->
      (forall a, (0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48) -> ms_mem ms' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
      realizes PSEGS (mkCfg ms' md') K) ->
  realizes PSEGS (mkCfg ms md) K.
Proof. LiaFast.lf_pins (fun (HOK : LiaFast.U) => LiaFast.u0).
  intros E L ms md hs n i0 i7 o0 sp R7 K Hd Hpc Hrv Hrom Hok Hi7 Hb7 Hheap Hmd HU H10 Hn Hra H3 H4 H2 Hs16 Hslo Hshi Htop Hfr Hav Hk.
  pose proof HOK as (_ & _ & _ & _ & Hblk). pose proof HMMD as HM.
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
  apply (HM fxs regs mem md hs n (getr regs 1) K Hheap Hmd HU H10 Hn eq_refl Hra H3 H4 ltac:(rewrite HSP; exact Hs16)
           ltac:(rewrite HSP; exact Hshi) ltac:(rewrite HSP; exact Htop) ltac:(rewrite HSP; exact Hstk)).
  intros fx' regs' m' md' hs' p Hfc Hheap' Hmd' Hvo HU' H10' Hp16 Hadd Hnin Hcs Hmunch Hcells Hstk'.
  rewrite HSP in Hmunch, Hstk'.
  set (ms' := @mkst fx' regs' (getr regs 1) m' rom).
  assert (Hpin : In (p, n) (hi_blocks HI hs')) by (apply Hadd; left; reflexivity).
  assert (P1 : ms_pc_val ms' = Z_to_bv 64 (bv_unsigned (getr regs 1))) by (unfold ms', mkst; cbn [ms_pc_val]; symmetry; apply Z_to_bv_bv_unsigned).
  assert (P2 : forall r : reg, existsb (Pos.eqb (rkey r)) KEEPH = true -> rkey r <> 11%positive \/ None = @None lin ->
                 getr (ms_regs ms') r = getr regs r).
  { intros r Hr _. unfold ms', mkst; cbn [ms_regs]. exact (keeph_cs regs regs' r Hcs Hr). }
  assert (P3 : forall l, None = Some l -> getr (ms_regs ms') (Z_to_bv 5 10) = lden E l) by (intros l Hc; discriminate Hc).
  assert (Hout : forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x -> ~ in_fp E (s_rgs L) [(i0, o0, 8192); (i7, 4, 4)] x ->
                   m' x = mem x).
  { intros i R x Hi Hin Hnf.
    destruct (HIface.outside_dec CELLS_NE (bv_unsigned x)) as [Hc1|Hc1].
    - destruct (HIface.outside_dec ERRC (bv_unsigned x)) as [Hc2|Hc2].
      + assert (Hc : ioutside (CELLS_NE ++ ERRC) (bv_unsigned x)) by (apply HIface.outside_app; split; assumption).
        apply Hmunch. apply HIface.outside_app. split; [exact (avoid_owned E L hs mem md i R x Hav Hheap Hi Hin Hc)|].
        apply HIface.outside_app. split; [exact (avoid_owned E L hs' m' md' i R x Hav Hheap' Hi Hin Hc)|].
        cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside]. split; [exact (avoid_block E L hs' m' md' i R x p n Hav Hheap' Hpin Hi Hin Hc)|]. split; [|exact I].
        intros Hx. apply Hnf. exists i0, o0, 8192, R0. split; [left; reflexivity|]. split; [exact Hi0|]. lia.
      + exfalso. apply Hnf. exists i7, 4, 4, R7. split; [right; left; reflexivity|]. split; [exact Hi7|]. rewrite Hb7.
        cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside ERRC] in Hc2. lia.
    - rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hcells. cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside CELLS_NE] in Hc1.
      destruct (Z_le_gt_dec 0x63da0 (bv_unsigned x)); destruct (Z_lt_ge_dec (bv_unsigned x) 0x63da8); [left; lia | | |];
        destruct (Z_le_gt_dec 0x95e40 (bv_unsigned x)); destruct (Z_lt_ge_dec (bv_unsigned x) 0x95e48); try (right; lia);
        exfalso; apply Hc1; repeat split; lia. }
  assert (P4 : forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x -> ~ in_fp E (s_rgs L) [(i0, o0, 8192); (i7, 4, 4)] x ->
                 ms_mem ms' x = ms_mem ms x) by (intros; unfold ms', mkst; cbn [ms_mem]; eapply Hout; eassumption).
  assert (P5 : forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x ->
                 (rd1 PSEGS (ms_mem ms) x <> None -> rd1 PSEGS (ms_mem ms') x <> None) /\
                 (wview PSEGS (ms_mem ms) x <> None -> wview PSEGS (ms_mem ms') x <> None)).
  { intros i R x Hi Hin. unfold ms', mkst; cbn [ms_mem].
    destruct (HIface.outside_dec ERRC (bv_unsigned x)) as [Hc2|Hc2].
    - destruct (Z_le_gt_dec (sp - 8192) (bv_unsigned x)) as [A|A]; [destruct (Z_lt_ge_dec (bv_unsigned x) sp) as [B|B]|].
      + destruct Hstk' as (_ & _ & HS). destruct (HS (bv_unsigned x) ltac:(lia)) as [Hw (b & Hb)]. unfold wa in Hw, Hb.
        rewrite Z_to_bv_bv_unsigned in Hw, Hb. unfold mrd in Hb. unfold rd1. split; intros _; [rewrite Hb; discriminate | exact Hw].
      + unfold rd1, wview. rewrite (Hout i R x Hi Hin); [tauto|]. intros (j & o & k & R' & Hj & Hnj & Hx). destruct Hj as [Hj|[Hj|[]]]; injection Hj as <- <- <-.
        * rewrite Hi0 in Hnj. injection Hnj as <-. lia.
        * rewrite Hi7 in Hnj. injection Hnj as <-. rewrite Hb7 in Hx. cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside ERRC] in Hc2. lia.
      + unfold rd1, wview. rewrite (Hout i R x Hi Hin); [tauto|]. intros (j & o & k & R' & Hj & Hnj & Hx). destruct Hj as [Hj|[Hj|[]]]; injection Hj as <- <- <-.
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
  apply (Hk E' ms' md' hs' p Ha' Hd' ltac:(unfold ms', mkst; cbn [ms_rom]; symmetry; exact Hrom) Hheap' Hmd' Hvo HU' H10' Hp16 Hadd Hnin).
  - unfold ms', mkst; cbn [ms_mem]. exact Hmunch.
  - exact Hcells.
Qed.
#[using="HOK"] Theorem fx_free : forall E L ms md hs (n : Z) (i0 i7 : nat) (o0 : Z) (sp : Z) R7 K,
  sden PSEGS E L ms -> s_pc L = 0x511d0 -> s_resv L = RNone -> ms_rom ms = seg_rom PSEGS ->
  havoc_ok L [(i0, o0, 8192); (i7, 4, 4)] None = true ->
  nth_error (s_rgs L) i7 = Some R7 -> bv_unsigned (lden E (rg_base R7)) = 0x75b28 ->
  hi_Heap HI hs (ms_mem ms) md -> md_ok md ->
  forall (pb : Z), getr (ms_regs ms) 10 = Z_to_bv 64 pb -> In (pb, n) (hi_blocks HI hs) -> pb <> 0 ->
  bv_unsigned (getr (ms_regs ms) 1) mod 2 = 0 -> getr (ms_regs ms) 3 = GP -> getr (ms_regs ms) 4 = TP ->
  getr (ms_regs ms) 2 = Z_to_bv 64 sp -> sp mod 16 = 0 -> 0xa0000 <= sp - 8192 -> sp <= 2 ^ 47 -> HTOP <= sp - 8192 ->
  frame_in E L i0 o0 8192 (sp - 8192) -> avoid_heap3 E (s_rgs L) ->
  (forall E' ms' md' hs', agree (s_next L) E E' ->
      sden PSEGS E' (havoc_call L (bv_unsigned (getr (ms_regs ms) 1)) KEEPH [(i0, o0, 8192); (i7, 4, 4)] None) ms' -> ms_rom ms' = ms_rom ms ->
      hi_Heap HI hs' (ms_mem ms') md' -> md_ok md' -> vm_only md md' -> U md' <= U md ->
      blocks_del (hi_blocks HI hs) (hi_blocks HI hs') (pb, n) ->
      munch (hi_owned HI hs ++ hi_owned HI hs' ++ [(pb, pb + n); (sp - 8192, sp)]) (ms_mem ms) (ms_mem ms') ->
      (forall a, (0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48) -> ms_mem ms' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
      realizes PSEGS (mkCfg ms' md') K) ->
  realizes PSEGS (mkCfg ms md) K.
Proof. LiaFast.lf_pins (fun (HOK : LiaFast.U) => LiaFast.u0).
  intros E L ms md hs n i0 i7 o0 sp R7 K Hd Hpc Hrv Hrom Hok Hi7 Hb7 Hheap Hmd pb H10 Hin Hpb0 Hra H3 H4 H2 Hs16 Hslo Hshi Htop Hfr Hav Hk.
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
  apply (HF fxs regs mem md hs pb n (getr regs 1) K Hheap Hmd H10 (or_intror Hin) eq_refl Hra H3 H4 ltac:(rewrite HSP; exact Hs16)
           ltac:(rewrite HSP; exact Hshi) ltac:(rewrite HSP; exact Htop) ltac:(rewrite HSP; exact Hstk)).
  intros fx' regs' m' md' hs' Hfc Hheap' Hmd' Hvo HU' Hkeep Hdel Hcs Hmunch Hstk'.
  assert (Hcells : forall a, (0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48) -> m' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha. apply Hkeep. cbn [ioutside CELLS_NE]. intros (A & B & _). destruct Ha as [Ha|Ha]; [exact (A Ha) | exact (B Ha)]. }
  assert (Hdel' : blocks_del (hi_blocks HI hs) (hi_blocks HI hs') (pb, n)).
  { replace (pb =? 0) with false in Hdel; [exact Hdel|]. symmetry. apply Z.eqb_neq. exact Hpb0. }
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
        apply Hmunch. apply HIface.outside_app. split; [exact (avoid_owned E L hs mem md i R x Hav Hheap Hi Hin0 Hc)|].
        apply HIface.outside_app. split; [exact (avoid_owned E L hs' m' md' i R x Hav Hheap' Hi Hin0 Hc)|].
        cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside]. split; [exact (avoid_block E L hs mem md i R x pb n Hav Hheap Hin Hi Hin0 Hc)|]. split; [|exact I].
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
  apply (Hk E' ms' md' hs' Ha' Hd' ltac:(unfold ms', mkst; cbn [ms_rom]; symmetry; exact Hrom) Hheap' Hmd' Hvo HU' Hdel').
  - unfold ms', mkst; cbn [ms_mem]. exact Hmunch.
  - exact Hcells.
Qed.
End HeapGlue.
