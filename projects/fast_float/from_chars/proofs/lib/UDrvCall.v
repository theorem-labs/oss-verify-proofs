(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec CatSim SeqExec StepTac StoreOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Frame RefMemcpyLib DriverCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.Frame OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UDrvData UbMemchr UbStrnlen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition KEEP : list positive := List.map rkey callee_saved.

Lemma rkey_inj : forall r r' : reg, rkey r = rkey r' -> r = r'.
Proof.
  intros r r' H. unfold rkey, bv_key in H. apply (f_equal Zpos) in H.
  pose proof (bv_unsigned_in_range _ r). pose proof (bv_unsigned_in_range _ r'). unfold bv_modulus in *.
  rewrite !Z2Pos.id in H by lia. apply bv_eq. lia.
Qed.

Lemma keep_cs : forall r : reg, existsb (Pos.eqb (rkey r)) KEEP = true -> In r callee_saved.
Proof.
  intros r H. unfold KEEP in H. apply existsb_exists in H as (k & Hk & Hx). apply Pos.eqb_eq in Hx.
  apply in_map_iff in Hk as (r' & <- & Hr'). rewrite (rkey_inj r r' Hx). exact Hr'.
Qed.

(* [comment removed for export] *)
Definition frame_in (E : valu) (L : sst) (i : nat) (o n : Z) (a : Z) : Prop :=
  exists R, nth_error (s_rgs L) i = Some R /\ bv_unsigned (lden E (rg_base R)) + o = a /\ wkind (rg_kind R) = true /\
            0 <= o /\ o + n <= rsz E R.

Lemma frame_in_store_ok : forall E L ms i o n a, sden PSEGS E L ms -> frame_in E L i o n a -> 0 <= n ->
  RiscvSemantics.store_ok PSEGS (ms_mem ms) (Z_to_bv 64 a) (Z.to_nat n) = true.
Proof.
  intros E L ms i o n a Hd (R & Hi & Ha & Hk & Ho & Hn) Hn0. rewrite <- Ha.
  apply (rg_store_ok PSEGS E (ms_mem ms) R o (Z.to_nat n)); [exact (sden_rg _ _ _ _ _ _ Hd Hi) | exact Hk | exact Ho |].
  rewrite Z2Nat.id by lia. exact Hn.
Qed.

(* [comment removed for export] *)
Lemma in_fp_single : forall E L i o n a R x, nth_error (s_rgs L) i = Some R -> bv_unsigned (lden E (rg_base R)) + o = a ->
  in_fp E (s_rgs L) [(i, o, n)] x -> a <= bv_unsigned x < a + n.
Proof.
  intros E L i o n a R x Hi Ha (j & o' & n' & R' & [Hx|[]] & Hj & Hin). injection Hx as <- <- <-.
  rewrite Hi in Hj. injection Hj as <-. lia.
Qed.

Lemma not_in_fp_single : forall E L i o n a R x, nth_error (s_rgs L) i = Some R -> bv_unsigned (lden E (rg_base R)) + o = a ->
  ~ (a <= bv_unsigned x < a + n) -> ~ in_fp E (s_rgs L) [(i, o, n)] x.
Proof. intros E L i o n a R x Hi Ha Hx Hc. exact (Hx (in_fp_single E L i o n a R x Hi Ha Hc)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem fx_strnlen : forall E L ms model T (s sp ret : word) buf (K n : Z) (i : nat) (o : Z) (resl : lin),
  sden PSEGS E L ms -> s_pc L = 0x607e8 -> s_resv L = RNone ->
  havoc_ok L [(i, o, 32)] (Some resl) = true -> frame_in E L i o 32 (bv_unsigned sp - 32) ->
  getr (ms_regs ms) 1 = ret -> getr (ms_regs ms) 2 = sp -> getr (ms_regs ms) 10 = s -> getr (ms_regs ms) 11 = Z_to_bv 64 n ->
  mchrH (ms_mem ms) s buf K n -> 0 < bv_unsigned s + K -> 0x12fc8 <= bv_unsigned sp - 32 ->
  (bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned s) ->
  bv_unsigned ret mod 2 = 0 -> lden E resl = Z_to_bv 64 K ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (forall E' ms', agree (s_next L) E E' -> sden PSEGS E' (havoc_call L (bv_unsigned ret) KEEP [(i, o, 32)] (Some resl)) ms' ->
      frame_mod (ms_mem ms) (ms_mem ms') [(Z_to_bv 64 (bv_unsigned sp - 32), 32)] -> ms_rom ms' = ms_rom ms ->
      realizes PSEGS (mkCfg ms' model) T) ->
  realizes PSEGS (mkCfg ms model) T.
Proof.
  intros E L ms model T s sp ret buf K n i o resl Hd Hpc Hrv Hok Hfi H1 H2 H10 H11 HM Hs Hsp Hdj Hret Hres Hh Hl Hk.
  rewrite (sden_mkst PSEGS E L ms Hd Hrv). rewrite Hpc.
  set (fxs := mkFP (ms_fregs ms) (ms_fcsr ms)).
  pose proof (frame_in_store_ok E L ms i o 32 _ Hd Hfi ltac:(lia)) as Hst.
  destruct (@ref_strnlen fxs (ms_mem ms) s sp buf K n (ms_rom ms) (ms_regs ms) ret HM Hs Hst Hsp Hdj
              (ret_ok_even ret Hret) H1 H2 H10 H11) as (regs' & mem' & Hrun & Hkc & Ha0 & Hfr).
  replace (Z_to_bv 64 0x607e8) with (0x607e8%bv : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact Hh | exact Hl | exact Hrun |].
  set (ms' := @mkst fxs regs' ret mem' (ms_rom ms)).
  destruct Hfi as (R & Hi & Ha & Hwk & Ho & Hn).
  assert (P1 : ms_pc_val ms' = Z_to_bv 64 (bv_unsigned ret)) by (cbn; symmetry; apply Z_to_bv_bv_unsigned).
  assert (P2 : forall r : reg, existsb (Pos.eqb (rkey r)) KEEP = true -> rkey r <> 11%positive \/ Some resl = None ->
                 getr (ms_regs ms') r = getr (ms_regs ms) r).
  { intros r Hr _. cbn [ms_regs ms']. apply Hkc. apply keep_cs. exact Hr. }
  assert (P3 : forall l, Some resl = Some l -> getr (ms_regs ms') (Z_to_bv 5 10) = lden E l).
  { intros l Hl0. injection Hl0 as <-. cbn [ms_regs ms']. transitivity (Z_to_bv 64 K); [exact Ha0 | rewrite Hres; reflexivity]. }
  assert (P4 : forall i' R' x, nth_error (s_rgs L) i' = Some R' -> in_rg E R' x -> ~ in_fp E (s_rgs L) [(i, o, 32)] x ->
                 ms_mem ms' x = ms_mem ms x).
  { intros i' R' x Hi' Hin Hnf. cbn [ms_mem ms']. destruct Hfr as [Hout _]. apply Hout.
    split; [|exact I]. unfold in_rng. intros Hx. apply Hnf. exists i, o, 32, R. split; [left; reflexivity|]. split; [exact Hi|].
    pose proof (u_range E (rg_base R)). pose proof (bv_unsigned_in_range _ sp). unfold bv_modulus in *.
    rewrite u_small64 in Hx by (unfold two64 in *; lia). lia. }
  assert (P5 : forall i' R' x, nth_error (s_rgs L) i' = Some R' -> in_rg E R' x -> ms_mem ms x <> None -> ms_mem ms' x <> None).
  { intros i' R' x Hi' Hin Hm. cbn [ms_mem ms']. destruct Hfr as [_ Hg]. exact (Hg x Hm). }
  destruct (havoc_call_sound PSEGS E L ms ms' (bv_unsigned ret) KEEP [(i, o, 32)] (Some resl) Hok Hd P1 eq_refl eq_refl
              (sden_frm _ _ _ _ Hd) P2 P3 P4 P5) as (E' & Ha' & Hd').
  apply (Hk E' ms' Ha' Hd'); [exact Hfr | reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import Ub_code_60914_60c38.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import WalkTac SumWalkTac.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition KEEPN : list positive :=
  List.map rkey ([1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).

Theorem fx_nlk : forall E L ms model T (r : Z),
  sden PSEGS E L ms -> s_pc L = 0x60914 -> s_resv L = RNone -> havoc_ok L [] None = true ->
  rget (s_regs L) (rkey 1) = lconst r -> r mod 2 = 0 -> 0 <= r < 2^64 ->
  rdn PSEGS (ms_mem ms) (Z_to_bv 64 0x97c23) 1%nat = Some [Z_to_bv 8 0] ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (forall E' ms', agree (s_next L) E E' -> sden PSEGS E' (havoc_call L r KEEPN [] None) ms' ->
      ms_mem ms' = ms_mem ms -> ms_rom ms' = ms_rom ms -> realizes PSEGS (mkCfg ms' model) T) ->
  realizes PSEGS (mkCfg ms model) T.
Proof.
  intros E L ms model T r Hd Hpc Hrv Hok G1 Hev Hr Mnl Hh Hl Hk.
  assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 r) by exact (getr_leaf_c PSEGS E L ms 1 _ Hd G1).
  assert (RET : ret_ok (Z_to_bv 64 r)) by (apply ret_ok_even; rewrite u_small64 by (unfold two64; lia); exact Hev).
  rewrite (sden_mkst PSEGS E L ms Hd Hrv). rewrite Hpc.
  set (fxs := mkFP (ms_fregs ms) (ms_fcsr ms)).
  replace (Z_to_bv 64 0x60914) with (0x60914%bv : word) by (apply bv_eq; reflexivity).
  assert (RUN : exists regs', msteps PSEGS (@mkst fxs (ms_regs ms) (0x60914 : word) (ms_mem ms) (ms_rom ms))
                                            (@mkst fxs regs' (Z_to_bv 64 r) (ms_mem ms) (ms_rom ms))
                /\ forall rg : reg, existsb (Pos.eqb (rkey rg)) KEEPN = true -> getr regs' rg = getr (ms_regs ms) rg).
  { eexists. split.
    - stepn F_60914 D_60914.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_60918 | reflexivity | exact D_60918 | gres; imm_norm; addr_norm; rdn_solve]
        | step_simpl]; vnorm.
      stepb_tk F_6091c D_6091c ltac:(cond_compute).
      stepret F_60b0c D_60b0c (Z_to_bv 64 r) ltac:(rewrite Q1; reflexivity).
      apply mst_refl.
    - intros rg Hrg. rewrite !getr_other by (intros Hc; rewrite Hc in Hrg; vm_compute in Hrg; discriminate Hrg). reflexivity. }
  destruct RUN as (regs' & Hrun & Hkc).
  eapply rz_msteps; [exact Hh | exact Hl | exact Hrun |].
  set (ms' := @mkst fxs regs' (Z_to_bv 64 r) (ms_mem ms) (ms_rom ms)).
  assert (P1 : ms_pc_val ms' = Z_to_bv 64 r) by reflexivity.
  assert (P2 : forall rg : reg, existsb (Pos.eqb (rkey rg)) KEEPN = true -> rkey rg <> 11%positive \/ @None lin = None ->
                 getr (ms_regs ms') rg = getr (ms_regs ms) rg).
  { intros rg Hrg _. cbn [ms_regs ms']. exact (Hkc rg Hrg). }
  assert (P3 : forall l, @None lin = Some l -> getr (ms_regs ms') (Z_to_bv 5 10) = lden E l) by (intros l Hl0; discriminate Hl0).
  assert (P4 : forall i' R' x, nth_error (s_rgs L) i' = Some R' -> in_rg E R' x -> ~ in_fp E (s_rgs L) [] x ->
                 ms_mem ms' x = ms_mem ms x) by (intros; reflexivity).
  assert (P5 : forall i' R' x, nth_error (s_rgs L) i' = Some R' -> in_rg E R' x -> ms_mem ms x <> None -> ms_mem ms' x <> None)
    by (intros i' R' x _ _ Hm; exact Hm).
  destruct (havoc_call_sound PSEGS E L ms ms' r KEEPN [] None Hok Hd P1 eq_refl eq_refl
              (sden_frm _ _ _ _ Hd) P2 P3 P4 P5) as (E' & Ha' & Hd').
  apply (Hk E' ms' Ha' Hd'); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import U_memcpy_stmt U_memcpy.
Open Scope Z_scope.

Lemma keep_mkR : forall (regs : bvmap 5 word) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (r : reg), In r callee_saved ->
  getr (mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) t0 t1 t2 (getr regs 8) (getr regs 9) (getr regs 10)
            a1 a2 a3 a4 a5 a6 a7 (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23)
            (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) t3 t4 t5 t6) r = getr regs r.
Proof. intros. unfold callee_saved in H. repeat (destruct H as [<-|H]; [reflexivity|]). destruct H. Qed.

Theorem fx_memcpy : forall E L ms model T (dst src : word) (n : Z) (bs old : list byte) (fp : list fpr) (resl : lin),
  sden PSEGS E L ms -> s_pc L = 0x600a8 -> s_resv L = RNone -> havoc_ok L fp (Some resl) = true -> ms_rom ms = seg_rom PSEGS ->
  getr (ms_regs ms) 10 = dst -> getr (ms_regs ms) 11 = src -> getr (ms_regs ms) 12 = Z_to_bv 64 n ->
  bv_unsigned (getr (ms_regs ms) 1) mod 2 = 0 ->
  bytes_at PSEGS (ms_mem ms) (bv_unsigned src) bs -> u8arr PSEGS (ms_mem ms) (bv_unsigned dst) old ->
  length old = length bs -> Z.of_nat (length bs) = n ->
  (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst) ->
  bv_unsigned dst + n < 2^64 -> bv_unsigned src + n < 2^64 ->
  lden E resl = dst ->
  (forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x -> bv_unsigned dst <= bv_unsigned x < bv_unsigned dst + n ->
     in_fp E (s_rgs L) fp x) ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (forall E' ms', agree (s_next L) E E' -> sden PSEGS E' (havoc_call L (bv_unsigned (getr (ms_regs ms) 1)) KEEP fp (Some resl)) ms' ->
      (forall x, ~ (bv_unsigned dst <= bv_unsigned x < bv_unsigned dst + n) -> ms_mem ms' x = ms_mem ms x) ->
      (forall x, ms_mem ms x <> None -> ms_mem ms' x <> None) ->
      bytes_at PSEGS (ms_mem ms') (bv_unsigned dst) bs -> ms_rom ms' = ms_rom ms ->
      realizes PSEGS (mkCfg ms' model) T) ->
  realizes PSEGS (mkCfg ms model) T.
Proof.
  intros E L ms model T dst src n bs old fp resl Hd Hpc Hrv Hok Hrom H10 H11 H12 Hra Hb Hu Hlo Hln Hdj Hw1 Hw2 Hres Hfp Hh Hl Hk.
  rewrite (sden_mkst PSEGS E L ms Hd Hrv). rewrite Hpc, Hrom.
  set (regs := ms_regs ms) in *. set (mem := ms_mem ms) in *. set (rom := seg_rom PSEGS) in *.
  set (fxs := mkFP (ms_fregs ms) (ms_fcsr ms)).
  pose proof (memcpy_spec (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
                (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
                (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
                (getr regs 29) (getr regs 30) (getr regs 31) (ms_fregs ms) (ms_fcsr ms) mem bs old) as HS.
  assert (Hn0 : bv_unsigned (getr regs 12) = n).
  { rewrite H12, Z_to_bv_unsigned. apply bv_wrap_small. pose proof (bv_unsigned_in_range _ dst). unfold bv_modulus in *. lia. }
  specialize (HS ltac:(rewrite H11; exact Hb) ltac:(rewrite H10; exact Hu) Hlo ltac:(rewrite Hn0; exact Hln)
                 ltac:(rewrite Hn0, H10, H11; exact Hdj) ltac:(rewrite Hn0, H10; exact Hw1) ltac:(rewrite Hn0, H11; exact Hw2) Hra).
  change (mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
                (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
                (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
                (getr regs 29) (getr regs 30) (getr regs 31)) with (mkR_of regs) in HS.
  destruct (evt_bridge PSEGS fxs regs (Z_to_bv 64 0x600a8) mem rom _ HS) as (st & Hrun & s0 & HQ & Heqv).
  eapply rz_msteps; [exact Hh | exact Hl | exact Hrun |].
  destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & Hmunch & Hwm & Hu8 & Hbs).
  destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ Heqv) as (fx' & regs' & -> & Hgr & _ & Hfc).
  assert (Hret : ret_pc (getr regs 1) = Z_to_bv 64 (bv_unsigned (getr regs 1))).
  { rewrite Z_to_bv_bv_unsigned. apply ret_pc_of_ret_ok. pose proof (ret_ok_even _ Hra) as R. unfold ret_ok, SeqExec.v_jalr, jalr_tgtZ in R. exact R. }
  set (ms' := @mkst fx' regs' (ret_pc (getr regs 1)) m' rom).
  assert (P1 : ms_pc_val ms' = Z_to_bv 64 (bv_unsigned (getr regs 1))) by exact Hret.
  assert (P2 : forall r : reg, existsb (Pos.eqb (rkey r)) KEEP = true -> rkey r <> 11%positive \/ Some resl = None ->
                 getr (ms_regs ms') r = getr regs r).
  { intros r Hr _. cbn [ms_regs ms']. rewrite Hgr. apply keep_mkR. apply keep_cs. exact Hr. }
  assert (P3 : forall l, Some resl = Some l -> getr (ms_regs ms') (Z_to_bv 5 10) = lden E l).
  { intros l Hl0. injection Hl0 as <-. cbn [ms_regs ms']. rewrite Hgr, Hres. exact H10. }
  assert (Hout : forall x : word, ~ (bv_unsigned dst <= bv_unsigned x < bv_unsigned dst + n) -> m' x = mem x).
  { intros x Hx. apply Hmunch. cbn [Frame.outside]. split; [|exact I]. rewrite H10, Hn0. exact Hx. }
  assert (P4 : forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x -> ~ in_fp E (s_rgs L) fp x -> ms_mem ms' x = ms_mem ms x).
  { intros i R x Hi Hin Hnf. cbn [ms_mem ms']. apply Hout. intros Hc. exact (Hnf (Hfp i R x Hi Hin Hc)). }
  assert (P5 : forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x -> ms_mem ms x <> None -> ms_mem ms' x <> None).
  { intros i R x Hi Hin Hm. cbn [ms_mem ms']. exact (Hwm x Hm). }
  assert (P6 : frm_zero (ms_fcsr ms')) by (unfold ms', mkst; cbn [ms_fcsr]; rewrite Hfc; exact (sden_frm _ _ _ _ Hd)).
  destruct (havoc_call_sound PSEGS E L ms ms' (bv_unsigned (getr regs 1)) KEEP fp (Some resl) Hok Hd P1 eq_refl eq_refl
              P6 P2 P3 P4 P5) as (E' & Ha' & Hd').
  apply (Hk E' ms' Ha' Hd'); [exact Hout | exact Hwm | | unfold ms', mkst; cbn [ms_rom]; symmetry; exact Hrom].
  cbn [ms_mem ms']. destruct Hu8 as [Hu8 _]. rewrite H10 in Hu8. exact Hu8.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_of_rdn : forall m (a : Z) bs, 0 <= a -> a + Z.of_nat (length bs) <= two64 ->
  rdn PSEGS m (Z_to_bv 64 a) (length bs) = Some bs -> bytes_at PSEGS m a bs.
Proof.
  intros m a bs Ha Hn H. split; [exact Ha|]. split; [unfold two64 in Hn; lia|].
  intros i Hi. destruct (nth_error bs i) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
  unfold mrd, wa. exact (rdn_rd1 PSEGS m a (length bs) bs Ha Hn H i b Hb).
Qed.

(* [comment removed for export] *)
Lemma u8arr_of_rg : forall E L ms i R (o : Z) (n : nat), sden PSEGS E L ms -> nth_error (s_rgs L) i = Some R ->
  wkind (rg_kind R) = true -> 0 <= o -> o + Z.of_nat n <= rsz E R ->
  exists old, length old = n /\ u8arr PSEGS (ms_mem ms) (bv_unsigned (lden E (rg_base R)) + o) old.
Proof.
  intros E L ms i R o n Hd Hi Hk Ho Hn.
  pose proof (sden_rg _ _ _ _ _ _ Hd Hi) as HR. pose proof HR as (_ & Hflat & _). pose proof (u_range E (rg_base R)) as RA.
  destruct (bytes_at_of_readable PSEGS (ms_mem ms) (bv_unsigned (lden E (rg_base R)) + o) n ltac:(lia) ltac:(unfold two64 in *; lia))
    as (old & Hlen & Hb).
  - intros j Hj. destruct (rg_ok_rw_byte PSEGS E _ R HR Hk (o + j) ltac:(lia)) as [Hr _].
    replace (bv_unsigned (lden E (rg_base R)) + (o + j)) with (bv_unsigned (lden E (rg_base R)) + o + j) in Hr by lia.
    rewrite rdn_unfold. unfold mrd, wa.
    destruct (rd1 PSEGS (ms_mem ms) (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o + j))) eqn:Hx; [|exfalso; exact (Hr eq_refl)].
    unfold rd1 in Hx. rewrite Hx. exists b. reflexivity.
  - exists old. split; [exact Hlen|]. split; [exact Hb|]. split; [lia|]. split; [unfold two64 in *; lia|].
    intros j Hj. destruct (rg_ok_rw_byte PSEGS E _ R HR Hk (o + j) ltac:(lia)) as [_ Hw]. unfold wa.
    replace (bv_unsigned (lden E (rg_base R)) + o + j) with (bv_unsigned (lden E (rg_base R)) + (o + j)) by lia. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma u8arr_ext : forall m m' (A : Z) bs, u8arr PSEGS m A bs ->
  (forall x, A <= bv_unsigned x < A + Z.of_nat (length bs) -> m' x = m x) -> u8arr PSEGS m' A bs.
Proof.
  intros m m' A bs [(Ha & Hl & Hb) (Ha' & Hn & Hw)] He. split.
  - split; [lia|]. split; [lia|]. intros i Hi. unfold mrd. rewrite He; [apply Hb; exact Hi|]. unfold wa. rewrite u_small64 by (unfold two64; lia). lia.
  - split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite He; [apply Hw; exact Hi|]. unfold wa. rewrite u_small64 by (unfold two64; lia). lia.
Qed.

Lemma bytes_at_ext_m : forall m m' (A : Z) bs, bytes_at PSEGS m A bs ->
  (forall x, A <= bv_unsigned x < A + Z.of_nat (length bs) -> m' x = m x) -> bytes_at PSEGS m' A bs.
Proof.
  intros m m' A bs (Ha & Hl & Hb) He. split; [lia|]. split; [lia|]. intros i Hi. unfold mrd. rewrite He; [apply Hb; exact Hi|].
  unfold wa. rewrite u_small64 by (unfold two64; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_of_bytes_at : forall m (a : Z) bs, bytes_at PSEGS m a bs -> rdn PSEGS m (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_rdn PSEGS m a bs 0 (length bs) H ltac:(lia)) as R.
  rewrite Z.add_0_r, skipn_O, firstn_all in R. exact R.
Qed.
