(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE23.v, with its module paths changed, names TfibSyms -> BoxregSyms and its addresses moved to libreac/fuzz_boxreg's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/AE23.v, with its module paths changed; 1496 of its 1558 lines of code are new or changed and 1613 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): musl mwrite 0x96cc0 on link's memory FILE WITHOUT
   AR, for the last flush at process exit (after the memory-checking runtime's module destructor), against
   LinkRwExitDefs.v.
   amw_noar_at K kmax : the contract of LinkRwDefs.v amwrite_mf_at with AR dropped: plain memory facts in the premise
     (aecall_pre_noar, the interceptor's cells, amf_block_noar, amf_buf_ok_noar), hs_kept added to the post.
   link_amwrite_k0_noar     : amw_noar_at (48 + ESTACK) 0, the walk at k = 0: +0x34 beq taken, +0x5c..+0x80, the
                              fit / ENOSPC arms, +0xc0 the memcpy interceptor (Section hypothesis AMEMCPY0), +0xc4..
   link_amwrite_noar_gen    : amw_noar_at (96 + ESTACK) 1024; at k > 0 the inner call +0x4c is link_amwrite_k0_noar
                              one frame lower.
   link_amwrite_flush_noar  : amwrite_mf_flush_noar_realizes, link_amwrite_noar_gen at x = 0 and no data.
   The symbolic states after the copy, the run lemmas, the store at +0xec and the value lemmas are LinkRwMwrite.v's. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE20 AsanNoAR AE2y.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFileSink AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkRwDefs LinkRwExitDefs LinkRwMwrite.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ==========================================================================
   1. Helpers: a block outside a range, the interceptor's cells carried across the walk
   ========================================================================== *)

Lemma nw_blk_sep : forall f n lo hi, 0 < n -> lo < hi -> (forall a, f <= a < f + n -> ~ (lo <= a < hi)) ->
  f + n <= lo \/ hi <= f.
Proof.
  intros f n lo hi Hn Hlh H. destruct (Z_le_gt_dec (f + n) lo) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec hi f) as [L2|L2]; [right; exact L2|]. exfalso. apply (H (Z.max f lo)); lia.
Qed.

(* every byte of every cell of l lies in [lo, hi) *)
Definition cells_in (lo hi : Z) (l : list (Z * Z * list (Z * N * Z))) : bool :=
  forallb (fun r => forallb (fun c => (lo <=? fst (fst r) + fst (fst c)) &&
    (fst (fst r) + fst (fst c) + Z.of_N (snd (fst c)) <=? hi)) (snd r)) l.

(* the interceptor's cells are image cells below g_said *)
Lemma nw_icpt_cells_in : cells_in 0x10000 0x62fee0 icpt_rodata = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nw_acells_xfer : forall (H : word -> bool) (m m' : word -> option byte) lo hi l,
  cells_in lo hi l = true ->
  (forall a, lo <= a < hi -> aview tfibsegs H m' a = aview tfibsegs H m a) ->
  acells_ok tfibsegs (mrestrict H m) l -> acells_ok tfibsegs (mrestrict H m') l.
Proof.
  intros H m m' lo hi l Hc Hv Hok. unfold acells_ok in *. unfold cells_in in Hc. rewrite forallb_forall in Hc.
  rewrite Forall_forall in Hok |- *. intros r Hr. specialize (Hc r Hr). specialize (Hok r Hr).
  rewrite forallb_forall in Hc. rewrite Forall_forall in Hok |- *. intros c Hc'. specialize (Hc c Hc'). specialize (Hok c Hc').
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply (mw_val_mem_xfer_av H m m'); [|exact Hok].
  intros i Hi. rewrite N_nat_Z in Hi. apply Hv. lia.
Qed.

(* linear arithmetic over the walk's constants, with the inner window *)
Ltac nwlia := unfold AMW0_STK, SHADOW_OFF in *; mwlia.

(* ==========================================================================
   2. The states of the walk at k = 0 (+0x00 to +0xc0), and their runs
   Atoms: 0..31 the entry registers; 33 pos, 34 len, 35 the flags, 36 wend, 37 wpos, 38 wbase. From +0x5c the code
   is the one the k > 0 walk runs after the inner call; after the copy it is the same state ssD.
   ========================================================================== *)

Definition RZ_wb : YP09.region := YP09.mkRegion (Some 10%nat) 56 160 56 64
  [YP09.mkChunk 56 (CVal 8 (SOff 38 0)); YP09.mkChunk 152 (CVal 8 (SOff 10 232))].
Definition rsZ : smem := [R_stkA; RF_fl; RF_win; RZ_wb; RF_ck; R_errno].
Definition ssZ : sstate := mkSS LA_MWRITE sr_atoms rsZ None (mkFacts [] [] []).
Definition ssZ_st1 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl_mw FUEL ssZ).
Lemma runZ1 : sym_runN tfibsegs tbl_mw FUEL ssZ = (ssZ_st1, RS_stopped (SR_branch BC_EQ (SOff 37 0) (SOff 38 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ssZ_eq : sstate := Eval vm_compute in YP06.add_cond ssZ_st1 (mkAC BC_EQ (SOff 37 0) (SOff 38 0)).
Definition ssZ_st2 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl_mw FUEL ssZ_eq).
Lemma runZ2 : sym_runN tfibsegs tbl_mw FUEL ssZ_eq = (ssZ_st2, RS_stopped (SR_branch BC_GEU SROOM (SOff 12 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ssZ_n : sstate := Eval vm_compute in YP06.add_cond ssZ_st2 (mkAC BC_GEU SROOM (SOff 12 0)).
Definition ssZ_e : sstate := Eval vm_compute in YP06.add_cond ssZ_st2 (mkAC BC_LTU SROOM (SOff 12 0)).
Lemma ssZ_e_eq : YP06.add_cond ssZ_st2 (mkAC (neg_bc BC_GEU) SROOM (SOff 12 0)) = ssZ_e.
Proof. vm_compute. reflexivity. Qed.
Definition ssZM1 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl_mw FUEL ssZ_n).
Lemma runZM1 : sym_runN tfibsegs tbl_mw FUEL ssZ_n = (ssZM1, RS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.
Definition ssZM2 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl_mw FUEL ssZ_e).
Lemma runZM2 : sym_runN tfibsegs tbl_mw FUEL ssZ_e = (ssZM2, RS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.
Lemma ssD_Z1 : mkSS 0x96d84 (sr_set (sr_sets (ss_regs ssZM1) (junk_upd 55 CLOB)) 8 (SOff 71 0)) rsD None (mkFacts [] [] []) = ssD.
Proof. vm_compute. reflexivity. Qed.
Lemma ssD_Z2 : mkSS 0x96d84 (sr_set (sr_sets (ss_regs ssZM2) (junk_upd 55 CLOB)) 8 (SOff 71 0)) rsD None (mkFacts [] [] []) = ssD.
Proof. vm_compute. reflexivity. Qed.

(* ==========================================================================
   3. What every step keeps, without AR: the bytes outside the written set, presence, the bytes the shadow map hides
   ========================================================================== *)

Section ninv. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variables (W : world tfibsegs) (Kw sp0 f : Z) (mem0 : word -> option byte) (md0 : Model).

Definition nchg (a : Z) : Prop :=
  (sp0 - Kw <= a < sp0) \/ (f <= a < f + AMF_ZEROED) \/
  (amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf) \/ (as_errno B <= a < as_errno B + 4).

Definition NINV (mem : word -> option byte) (md : Model) : Prop :=
  same_but_materialized md0 md /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ nchg a -> aview tfibsegs (w_H W) mem a = aview tfibsegs (w_H W) mem0 a) /\
  (forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mem a) /\
  (forall a, sp0 - Kw <= a < sp0 -> apresent (w_H W) mem a) /\
  hs_kept (w_H W) mem0 mem.

Lemma NINV_init : (forall a, sp0 - Kw <= a < sp0 -> apresent (w_H W) mem0 a) -> NINV mem0 md0.
Proof.
  intros Hp. split; [apply same_but_materialized_refl|]. split; [intros; reflexivity|].
  split; [intros a Ha; exact Ha|]. split; [exact Hp | apply hs_kept_refl].
Qed.

(* a symbolic phase whose writable windows lie in the written set, each byte present (so not hidden) or off the
   shadow band *)
Lemma NINV_run : forall (OKw : Z -> Prop) mem md mem' mat,
  NINV mem md ->
  (forall x : word, ~ OKw (bv_unsigned x) -> mem' x = mem x) ->
  (forall x : word, ~ OKw (bv_unsigned x) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  (forall a, OKw a -> nchg a /\ (w_H W (Z_to_bv 64 a) = false \/ ~ in_band_rw a)) ->
  NINV mem' (with_vm_backing (m_vm_lazy md) mat md).
Proof.
  intros OKw mem md mem' mat (Hsbm & Hfr & Hpr & Hwp & Hhs) Hraw Hres Hgr Hok.
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ OKw a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a).
  { intros a Ha Hn. apply aview_eq_of. apply Hres. rewrite unsigned_lit_small by lia. exact Hn. }
  split; [eapply same_but_materialized_trans; [exact Hsbm | apply with_vm_backing_same]|].
  split; [intros a Ha Hn; rewrite AV; [apply Hfr; assumption | exact Ha | intros Hk; exact (Hn (proj1 (Hok a Hk)))]|].
  split; [intros a Ha; apply (mw_grows_apresent _ _ _ _ Hgr); apply Hpr; exact Ha|].
  split; [intros a Ha; apply (mw_grows_apresent _ _ _ _ Hgr); apply Hwp; exact Ha|].
  apply (hs_kept_trans (w_H W) mem0 mem mem' Hhs).
  intros a Hb Hh. apply Hraw. rewrite unsigned_lit_small by (apply in_band_rw_u64; exact Hb).
  intros Hk. destruct (proj2 (Hok a Hk)) as [Hf | Hn]; [rewrite Hf in Hh; discriminate Hh | exact (Hn Hb)].
Qed.

(* a called contract whose written set lies in mwrite's *)
Lemma NINV_call : forall (Kc : Z -> Prop) mem md mem' md',
  NINV mem md -> same_but_materialized md md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Kc a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  (forall a, Kc a -> nchg a) -> hs_kept (w_H W) mem mem' ->
  NINV mem' md'.
Proof.
  intros Kc mem md mem' md' (Hsbm & Hfr & Hpr & Hwp & Hhs) Hsbm' Hk Hp HK Hhs'.
  split; [eapply same_but_materialized_trans; [exact Hsbm | exact Hsbm']|].
  split; [intros a Ha Hn; rewrite Hk; [apply Hfr; assumption | exact Ha | intros Hc; exact (Hn (HK a Hc))]|].
  split; [intros a Ha; apply Hp; apply Hpr; exact Ha|].
  split; [intros a Ha; apply Hp; apply Hwp; exact Ha | exact (hs_kept_trans _ _ _ _ Hhs Hhs')].
Qed.

(* the return: the post of the contract, with its FILE part P *)
Lemma nw_finish : forall regs0 extra E ss ms md (P : bvmap 5 word -> (word -> option byte) -> Prop),
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> clookup tbl_mw (ss_pc ss) = Some RET_WORD_r ->
  sr_get (ss_regs ss) 1 = SOff 1 0 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
  env_agree 32 (Ereg regs0 extra) E -> YK0s.ret_ok (getr regs0 1) ->
  NINV (ms_mem ms) md -> P (ms_regs ms) (ms_mem ms) ->
  SRr tfibsegs W (mkCfg ms md) (fun W' c' => W' = W /\ exists regs' mem' md',
     c' = cfg_at tfibsegs (raZ regs0) regs' mem' md' /\
     aregs_preserved regs0 regs' /\ same_but_materialized md0 md' /\
     P regs' mem' /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ nchg a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem0 a) /\
     hs_kept (w_H W) mem0 mem' /\
     (forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mem' a) /\
     (forall a, sp0 - Kw <= a < sp0 -> apresent (w_H W) mem' a)).
Proof.
  intros regs0 extra E ss ms md P HS Hrv Hpc Hra Hcs HAE Hret (Hsbm & Hfr & Hpr & Hwp & Hhs) HP.
  eapply (SRr_ret_at tfibsegs tbl_mw tbl_mw_ok AF0x.Hwx_tfa W E ss ms md _ HS Hrv Hpc).
  intros mat'. split; [reflexivity|].
  exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat' md).
  split.
  { unfold cfg_at. do 2 f_equal.
    rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms 1 HS), Hra. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    destruct HAE as [HA _]. rewrite (HA 1%nat ltac:(lia)). rewrite (ew_Ereg_nat regs0 extra 1 1%bv eq_refl).
    unfold raZ, YG0d.w64. rewrite Z_to_bv_bv_unsigned. exact Hret. }
  split; [exact (aregs_preserved_of_st_ok (w_H W) E ss ms regs0 extra HS HAE Hcs)|].
  split; [eapply same_but_materialized_trans; [exact Hsbm | apply with_vm_backing_same]|].
  split; [exact HP|]. split; [exact Hfr|]. split; [exact Hhs|]. split; [exact Hpr | exact Hwp].
Qed.

End ninv.

(* ==========================================================================
   4. The contract of mwrite without AR, at window K and up to kmax pending bytes
   ========================================================================== *)

Section D. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

Definition amw_noar_at (K kmax pc : Z) : Prop :=
  forall W regs mem md (f k fl om wend wpos wbase pos len x : Z) (pb ds : list Z),
  aecall_pre_noar tfibsegs B K W regs mem ->
  acells_ok tfibsegs (mrestrict (w_H W) mem) icpt_rodata ->
  getr regs 10 = w64 f -> getr regs 11 = w64 x -> getr regs 12 = w64 (Z.of_nat (length ds)) ->
  amf_block_noar tfibsegs W regs mem K f ->
  amf_k tfibsegs link_amf (mrestrict (w_H W) mem) f k -> k <= kmax ->
  amf_dyn tfibsegs link_amf (mrestrict (w_H W) mem) f fl om wend wpos wbase pos len ->
  amf_pend tfibsegs (mrestrict (w_H W) mem) f pb -> Z.of_nat (length pb) = k ->
  amf_buf_ok_noar tfibsegs link_amf K W regs mem ->
  azbytes tfibsegs (mrestrict (w_H W) mem) x ds -> 0 <= x -> x + Z.of_nat (length ds) <= 2 ^ 63 ->
  amem_range x (Z.of_nat (length ds)) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x (Z.of_nat (length ds)) ->
  (0 < Z.of_nat (length ds) -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x (Z.of_nat (length ds))) ->
  (forall a, x <= a < x + Z.of_nat (length ds) ->
     ~ (amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf) /\ ~ (f <= a < f + AMF_ZEROED) /\
     ~ (as_errno B <= a < as_errno B + 4) /\ ~ (spZ regs - K <= a < spZ regs)) ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       let n := Z.of_nat (length ds) in
       let n1 := amf_n1 link_amf k pos in
       let pos1 := amw_pos1 link_amf k pos in
       let n2 := amw_n2 link_amf k pos n in
       c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
       aregs_preserved regs regs' /\ same_but_materialized md md' /\
       amf_k tfibsegs link_amf (mrestrict (w_H W) mem') f 0 /\ amf_pend tfibsegs (mrestrict (w_H W) mem') f pb /\
       (n1 < k ->
          getr regs' 10 = w64 0 /\
          amf_dyn tfibsegs link_amf (mrestrict (w_H W) mem') f (Z.lor fl AF_ERR) om 0 0 0 pos1 (Z.max len pos1) /\
          azbytes tfibsegs (mrestrict (w_H W) mem') (amf_buf link_amf + pos) (firstn (Z.to_nat n1) pb)) /\
       (n1 = k ->
          getr regs' 10 = w64 n2 /\
          (exists fl' wend' wpos' wbase',
             amf_dyn tfibsegs link_amf (mrestrict (w_H W) mem') f fl' om wend' wpos' wbase' (pos1 + n2) (Z.max len (pos1 + n2)) /\
             (n2 < n -> fl' = Z.lor fl AF_ERR /\ wend' = 0 /\ wpos' = 0 /\ wbase' = 0) /\
             (n2 = n -> fl' = fl /\ wend' = wend /\ wpos' = wbase /\ wbase' = wbase)) /\
          azbytes tfibsegs (mrestrict (w_H W) mem') (amf_buf link_amf + pos) (pb ++ firstn (Z.to_nat n2) ds)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) -> ~ (f <= a < f + AMF_ZEROED) ->
          ~ (amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf) -> ~ (as_errno B <= a < as_errno B + 4) ->
          aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
       hs_kept (w_H W) mem mem' /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
       (forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem' a)).

End D.

(* ==========================================================================
   5. The walk
   ========================================================================== *)

Section NK. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : PcapSyms B.
Hypothesis AMEMCPY0 : aintrin_noar_realizes tfibsegs B OCpy icpt_rodata ESTACK (pc_wrap_memcpy (as_code B)).
Hypothesis HK0n : amw_noar_at B AMW0_STK 0 LA_MWRITE.

Variables (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (K f k fl om wend wpos wbase pos len x : Z) (pb ds : list Z).
Hypothesis HKw : AMW0_STK <= K.
Hypothesis HPRE : aecall_pre_noar tfibsegs B K W regs mem.
Hypothesis HCELL : acells_ok tfibsegs (mrestrict (w_H W) mem) icpt_rodata.
Hypothesis H10 : getr regs 10 = w64 f.
Hypothesis H11 : getr regs 11 = w64 x.
Hypothesis H12 : getr regs 12 = w64 (Z.of_nat (length ds)).
Hypothesis Hblkn : amf_block_noar tfibsegs W regs mem K f.
Hypothesis Hamk : amf_k tfibsegs link_amf (mrestrict (w_H W) mem) f k.
Hypothesis Hkmax : k <= AMF_BUFSIZ.
Hypothesis Hdyn : amf_dyn tfibsegs link_amf (mrestrict (w_H W) mem) f fl om wend wpos wbase pos len.
Hypothesis Hpend : amf_pend tfibsegs (mrestrict (w_H W) mem) f pb.
Hypothesis Hpbk : Z.of_nat (length pb) = k.
Hypothesis Hbuf : amf_buf_ok_noar tfibsegs link_amf K W regs mem.
Hypothesis Hds : azbytes tfibsegs (mrestrict (w_H W) mem) x ds.
Hypothesis Hx0 : 0 <= x.
Hypothesis Hxn : x + Z.of_nat (length ds) <= 2 ^ 63.
Hypothesis Hxam : amem_range x (Z.of_nat (length ds)).
Hypothesis Hxra : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x (Z.of_nat (length ds)).
Hypothesis Hxhull : 0 < Z.of_nat (length ds) -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x (Z.of_nat (length ds)).
Hypothesis Hxdisj : forall a, x <= a < x + Z.of_nat (length ds) ->
  ~ (amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf) /\ ~ (f <= a < f + AMF_ZEROED) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ ~ (spZ regs - K <= a < spZ regs).

Definition nE0 : env := Ereg regs [Z_to_bv 64 (f + 280 + k)].

(* the FILE part of the contract's post *)
Definition nPF (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let n := Z.of_nat (length ds) in
  let n1 := amf_n1 link_amf k pos in
  let pos1 := amw_pos1 link_amf k pos in
  let n2 := amw_n2 link_amf k pos n in
  amf_k tfibsegs link_amf (mrestrict (w_H W) mem') f 0 /\ amf_pend tfibsegs (mrestrict (w_H W) mem') f pb /\
  (n1 < k ->
     getr regs' 10 = w64 0 /\
     amf_dyn tfibsegs link_amf (mrestrict (w_H W) mem') f (Z.lor fl AF_ERR) om 0 0 0 pos1 (Z.max len pos1) /\
     azbytes tfibsegs (mrestrict (w_H W) mem') (amf_buf link_amf + pos) (firstn (Z.to_nat n1) pb)) /\
  (n1 = k ->
     getr regs' 10 = w64 n2 /\
     (exists fl' wend' wpos' wbase',
        amf_dyn tfibsegs link_amf (mrestrict (w_H W) mem') f fl' om wend' wpos' wbase' (pos1 + n2) (Z.max len (pos1 + n2)) /\
        (n2 < n -> fl' = Z.lor fl AF_ERR /\ wend' = 0 /\ wpos' = 0 /\ wbase' = 0) /\
        (n2 = n -> fl' = fl /\ wend' = wend /\ wpos' = wbase /\ wbase' = wbase)) /\
     azbytes tfibsegs (mrestrict (w_H W) mem') (amf_buf link_amf + pos) (pb ++ firstn (Z.to_nat n2) ds)).

Definition nFP : world tfibsegs -> config -> Prop := fun W' c' => W' = W /\ exists regs' mem' md',
  c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  aregs_preserved regs regs' /\ same_but_materialized md md' /\
  nPF regs' mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ nchg B K (spZ regs) f a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
  hs_kept (w_H W) mem mem' /\
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
  (forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem' a).

Local Notation NINVk := (NINV B W K (spZ regs) f mem md).

(* ---- the entry's facts ---- *)

Lemma nf_pre : YK0s.ret_ok (getr regs 1) /\ spZ regs mod 16 = 0 /\ kHighMemBeg + K <= spZ regs /\
  spZ regs <= kHighMemEnd /\ (forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B).
Proof.
  destruct HPRE as (A & M & L & T & P & G & Q).
  split; [exact A|]. split; [exact M|]. split; [exact L|]. split; [unfold kHighMemEnd; lia|].
  split; [exact P|]. split; [exact G | exact Q].
Qed.

Lemma nf_blk : f mod 16 = 0 /\ 0 < f /\ f + AMF_BLOCK <= 2 ^ 63 /\
  (f + AMF_BLOCK <= spZ regs - K \/ spZ regs <= f) /\
  (f + AMF_BLOCK <= kLowMemEnd - 1 \/ (kHighMemBeg <= f /\ f + AMF_BLOCK <= kHighMemEnd - 1)) /\
  (forall a, f <= a < f + AMF_BLOCK ->
     apresent (w_H W) mem a /\ writable_at tfibsegs (mrestrict (w_H W) mem) a /\ ~ YG0d.in_img tfibsegs a) /\
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF f AMF_BLOCK /\
  shadow_hull_vis (aview tfibsegs (w_H W) mem) f AMF_BLOCK.
Proof.
  destruct Hblkn as (A0 & A1 & A2 & Ab & Am & Ar & Ah).
  split; [exact A2|]. split; [exact A0|]. split; [exact A1|].
  split; [apply (nw_blk_sep f AMF_BLOCK (spZ regs - K) (spZ regs));
          [unfold AMF_BLOCK; lia | unfold AMW0_STK, ESTACK in HKw; lia | intros a Ha; exact (proj2 (proj2 (proj2 (Ab a Ha))))]|].
  split; [exact Am|].
  split; [intros a Ha; destruct (Ab a Ha) as (P & Wr & I & _); split; [exact P | split; [exact Wr | exact I]]|].
  split; [exact Ar | exact Ah].
Qed.

Lemma nf_fimg : f + AMF_BLOCK <= 0x10000 \/ 0x654000 <= f.
Proof.
  pose proof nf_blk as (_ & _ & _ & _ & _ & Bp & _).
  destruct (Z_le_gt_dec (f + AMF_BLOCK) 0x10000) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec 0x654000 f) as [L2|L2]; [right; exact L2|]. exfalso.
  apply (proj2 (proj2 (Bp (Z.max f 0x10000) ltac:(unfold AMF_BLOCK in *; lia)))). apply mw_img_full. lia.
Qed.

Lemma nf_winA : (k = 0 /\ wend = 0 /\ wpos = 0 /\ wbase = 0) \/ (wend = f + 1304 /\ wpos = f + 280 + k /\ wbase = f + 280).
Proof.
  pose proof nf_blk as (_ & B0 & B63 & _).
  destruct Hdyn as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & D0 & D136 & D32 & D40 & D56 & D232 & D240).
  destruct Hamk as (_ & [(Hk' & W32 & W40 & W56) | (Hk' & W32 & W40 & W56)]).
  - left. split; [exact Hk'|].
    split; [eapply mw_val_mem_det; [exact D32 | exact W32 | cbn; lia | cbn; lia]|].
    split; [eapply mw_val_mem_det; [exact D40 | exact W40 | cbn; lia | cbn; lia]|].
    eapply mw_val_mem_det; [exact D56 | exact W56 | cbn; lia | cbn; lia].
  - right. unfold AMF_BUF, AMF_BUFSIZ, AMF_BLOCK in *. split; [|split].
    + assert (E : wend = f + 280 + 1024) by (eapply mw_val_mem_det; [exact D32 | exact W32 | cbn; lia | cbn; lia]). lia.
    + eapply mw_val_mem_det; [exact D40 | exact W40 | cbn; lia | cbn; lia].
    + eapply mw_val_mem_det; [exact D56 | exact W56 | cbn; lia | cbn; lia].
Qed.

Lemma nf_win : 0 < k -> wend = f + 1304 /\ wpos = f + 280 + k /\ wbase = f + 280.
Proof. intros Hk. destruct nf_winA as [(Hk0 & _) | Hw]; [lia | exact Hw]. Qed.

Lemma nf_fl : fl = AF_NORD \/ fl = AF_NORD + AF_ERR.
Proof.
  destruct Hamk as ((_ & _ & _ & _ & Hfl & _) & _).
  destruct Hdyn as (R1 & _ & _ & _ & _ & _ & _ & D0 & _).
  unfold amemfile_flags in Hfl.
  destruct Hfl as [H|H]; [left | right]; (eapply mw_val_mem_det; [exact D0 | exact H | cbn; lia | cbn; unfold AF_NORD, AF_ERR; lia]).
Qed.

Lemma nf_lor : Z.lor fl AF_ERR = AF_NORD + AF_ERR.
Proof. destruct nf_fl as [-> | ->]; reflexivity. Qed.

Lemma nf_cookie : 0 <= pos <= len /\ len <= 4096 /\ 0 <= om < 2 ^ 32.
Proof. destruct Hdyn as (_ & R2 & _ & _ & _ & R6 & R7 & _). cbn [amf_size link_amf] in R7. lia. Qed.

Lemma nf_errno : as_errno B = 0x631b6c /\ as_tp B = 0x631c10.
Proof. rewrite (ts_errno B TB), (ts_tp B TB). split; reflexivity. Qed.

Lemma nk_E : forall E, env_agree 33 nE0 E ->
  bv_unsigned (ew E 2) = spZ regs /\ bv_unsigned (ew E 10) = f /\ ew E 32 = Z_to_bv 64 (f + 280 + k) /\
  ew E 1 = getr regs 1 /\ ew E 3 = getr regs 3 /\ ew E 4 = getr regs 4 /\ ew E 11 = getr regs 11 /\ ew E 12 = getr regs 12 /\
  bv_unsigned (ew E 4) = 0x631c10.
Proof.
  intros E [HA _]. pose proof nf_blk as (_ & B0 & B63 & _).
  pose proof nf_pre as (_ & _ & _ & _ & _ & _ & Htp). pose proof nf_errno as (_ & Etp).
  assert (G : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
  { intros n r Hn Hr. rewrite (HA n ltac:(lia)). unfold nE0. exact (ew_Ereg_nat regs _ n r Hr). }
  split; [rewrite (G 2%nat 2%bv ltac:(lia) eq_refl); reflexivity|].
  split; [rewrite (G 10%nat 10%bv ltac:(lia) eq_refl), H10; unfold w64; apply unsigned_lit_small; unfold AMF_BLOCK in *; lia|].
  split; [rewrite (HA 32%nat ltac:(lia)); unfold nE0; exact (ew_Ereg_extra regs _ 0)|].
  split; [exact (G 1%nat 1%bv ltac:(lia) eq_refl)|]. split; [exact (G 3%nat 3%bv ltac:(lia) eq_refl)|].
  split; [exact (G 4%nat 4%bv ltac:(lia) eq_refl)|]. split; [exact (G 11%nat 11%bv ltac:(lia) eq_refl)|].
  split; [exact (G 12%nat 12%bv ltac:(lia) eq_refl)|].
  rewrite (G 4%nat 4%bv ltac:(lia) eq_refl), Htp, Etp. reflexivity.
Qed.

(* every byte mwrite may write is in the contract's written set, and present (so not hidden) or off the shadow band *)
Lemma nf_safe : forall a,
  (spZ regs - K <= a < spZ regs) \/ (f <= a < f + AMF_ZEROED) \/ (as_errno B <= a < as_errno B + 4) \/
  (amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf) ->
  nchg B K (spZ regs) f a /\ (w_H W (Z_to_bv 64 a) = false \/ ~ in_band_rw a).
Proof.
  intros a Ha. pose proof nf_pre as (_ & _ & _ & _ & Hpw & _). pose proof nf_blk as (_ & _ & _ & _ & _ & Bp & _).
  pose proof nf_errno as (Ee & _).
  unfold nchg. destruct Ha as [Ha|[Ha|[Ha|Ha]]].
  - split; [left; exact Ha|]. left. exact (proj1 (Hpw a Ha)).
  - split; [right; left; exact Ha|]. left. exact (proj1 (proj1 (Bp a ltac:(unfold AMF_ZEROED, AMF_BLOCK in *; lia)))).
  - split; [right; right; right; exact Ha|]. right. rewrite Ee in Ha.
    unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia.
  - split; [right; right; left; exact Ha|]. right.
    cbn [amf_buf amf_size link_amf] in Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia.
Qed.

(* the shadow band (from kLowMemEnd) and the gap below the high memory hold no byte mwrite writes *)
Lemma nf_shadow : forall m md', NINVk m md' -> forall s, kLowMemEnd <= s < kHighMemBeg ->
  aview tfibsegs (w_H W) m s = aview tfibsegs (w_H W) mem s.
Proof.
  intros m md' (_ & Hfr & _) s Hs. pose proof nf_pre as (_ & _ & L3 & L4 & _).
  pose proof nf_blk as (_ & B0 & B63 & Bs & Bam & _).
  pose proof nf_errno as (Ee & _). apply Hfr; [unfold kLowMemEnd, kHighMemBeg in *; lia|].
  unfold nchg. rewrite Ee. cbn [amf_buf amf_size link_amf].
  unfold kLowMemEnd, kHighMemBeg, kHighMemEnd, AMF_ZEROED, AMF_BLOCK in *. lia.
Qed.

Lemma nf_ra_xfer : forall m md' a n, NINVk m md' -> 0 <= a -> a + n <= kHighMemEnd ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF a n -> range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF a n.
Proof.
  intros m md' a n HI Ha0 Han Hra z Hz. destruct (Hra z Hz) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite (nf_shadow m md' HI); [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *.
  pose proof (Z.div_pos z 8 ltac:(lia) ltac:(lia)). assert (z / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma nf_hull_xfer : forall m md' a n, NINVk m md' -> 0 <= a -> 0 < n -> a + n <= kHighMemEnd ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) a n -> shadow_hull_vis (aview tfibsegs (w_H W) m) a n.
Proof.
  intros m md' a n HI Ha0 Hn Han Hh s Hs. rewrite (nf_shadow m md' HI); [exact (Hh s Hs)|].
  unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *.
  pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
  assert ((a + n - 1) / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
  pose proof (Z.mod_pos_bound (2147450880 + a / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)).
  pose proof (Z.div_mod (2147450880 + a / 8) 8 ltac:(lia)).
  pose proof (Z.div_mod (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)). lia.
Qed.

(* the copy's source: unchanged since the entry *)
Lemma nf_src : forall m md', NINVk m md' -> forall i, (i < length ds)%nat ->
  aview tfibsegs (w_H W) m (x + Z.of_nat i) = Some (nth i ds 0).
Proof.
  intros m md' (_ & Hfr & _) i Hi. rewrite Hfr; [exact (Hds i Hi) | lia |].
  destruct (Hxdisj (x + Z.of_nat i) ltac:(lia)) as (N1 & N2 & N3 & N4). unfold nchg. tauto.
Qed.

(* the pending bytes: unchanged since the entry *)
Lemma nf_pend : forall m md', NINVk m md' -> amf_pend tfibsegs (mrestrict (w_H W) m) f pb.
Proof.
  intros m md' (_ & Hfr & _). pose proof nf_blk as (_ & B0 & B63 & Bs & _).
  pose proof nf_fimg as Fi. pose proof nf_errno as (Ee & _).
  apply (mw_azbytes_xfer (w_H W) mem m); [|exact Hpend].
  intros i Hi. apply Hfr; [nwlia|].
  unfold nchg. rewrite Ee. nwlia.
Qed.

(* the interceptor's cells: unchanged since the entry *)
Lemma nf_cells : forall m md', NINVk m md' -> acells_ok tfibsegs (mrestrict (w_H W) m) icpt_rodata.
Proof.
  intros m md' (_ & Hfr & _). pose proof nf_pre as (_ & _ & L3 & _). pose proof nf_fimg as Fi.
  pose proof nf_errno as (Ee & _).
  apply (nw_acells_xfer (w_H W) mem m 0x10000 0x62fee0 icpt_rodata nw_icpt_cells_in); [|exact HCELL].
  intros a Ha. apply Hfr; [lia|]. unfold nchg. rewrite Ee. nwlia.
Qed.

(* ---- one phase, with the windows of the shape after the copy (stack frame, the cookie's pos / len) ---- *)
Lemma nD_step : forall E ss ss' st ms md' Q,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> windows (ss_mem ss) = [(Some 2%nat, -48, 0); (Some 10%nat, 232, 248)] ->
  env_agree 33 nE0 E -> sym_runN tfibsegs tbl_mw FUEL ss = (ss', st) -> st <> RS_ecall ->
  NINVk (ms_mem ms) md' ->
  (forall ms1 mat1, st_ok tfibsegs E ss' (restrict (w_H W) ms1) ->
     NINVk (ms_mem ms1) (with_vm_backing (m_vm_lazy md') mat1 md') ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> ~ (f + 232 <= a < f + 248) ->
        aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) (ms_mem ms) a) ->
     SRr tfibsegs W (mkCfg ms1 (with_vm_backing (m_vm_lazy md') mat1 md')) Q) ->
  SRr tfibsegs W (mkCfg ms md') Q.
Proof.
  intros E ss ss' st ms md' Q HS Hw HAE Hrun Hne HI Hk.
  destruct (nk_E E HAE) as (E2 & E10 & _).
  eapply SRr_bind; [exact (mw_phase W E ss ss' st ms md' HS Hrun Hne)|].
  intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1 & HG1).
  assert (WIN : forall z, in_wrange E (ss_mem ss) z -> (spZ regs - 48 <= z < spZ regs) \/ (f + 232 <= z < f + 248)).
  { intros z Hz. destruct (mw_winD E (ss_mem ss) z Hw Hz) as [Hz'|Hz']; rewrite ?E2, ?E10 in Hz'; [left|right]; lia. }
  apply Hk; [exact HS1 | |].
  - apply (NINV_run B W K (spZ regs) f mem md (fun z => (spZ regs - 48 <= z < spZ regs) \/ (f + 232 <= z < f + 248))
      (ms_mem ms) md' (ms_mem ms1) mat1 HI).
    + intros y Hy. apply HF1. intros Hin. apply Hy. exact (WIN _ Hin).
    + intros y Hy. apply HFr1. intros Hin. apply Hy. exact (WIN _ Hin).
    + exact HG1.
    + intros z [Hz|Hz]; apply nf_safe; [left; nwlia | right; left; nwlia].
  - intros z Hz H1 H2. apply aview_eq_of. apply HFr1. rewrite unsigned_lit_small by lia. intros Hin. destruct (WIN _ Hin); lia.
Qed.

(* ---- one phase, with the windows of the shape after the inner call (and of the k = 0 entry) ---- *)
Lemma nC_step : forall E ss ss' st ms md' Q,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  windows (ss_mem ss) = [(Some 2%nat, -48, 0); (Some 10%nat, 0, 4); (Some 10%nat, 32, 48); (Some 10%nat, 56, 64);
                         (Some 10%nat, 232, 248); (Some 4%nat, -164, -160)] ->
  env_agree 33 nE0 E -> sym_runN tfibsegs tbl_mw FUEL ss = (ss', st) -> st <> RS_ecall ->
  NINVk (ms_mem ms) md' ->
  (forall ms1 mat1, st_ok tfibsegs E ss' (restrict (w_H W) ms1) ->
     NINVk (ms_mem ms1) (with_vm_backing (m_vm_lazy md') mat1 md') ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> ~ (f <= a < f + 4) -> ~ (f + 32 <= a < f + 48) ->
        ~ (f + 56 <= a < f + 64) -> ~ (f + 232 <= a < f + 248) -> ~ (as_errno B <= a < as_errno B + 4) ->
        aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) (ms_mem ms) a) ->
     SRr tfibsegs W (mkCfg ms1 (with_vm_backing (m_vm_lazy md') mat1 md')) Q) ->
  SRr tfibsegs W (mkCfg ms md') Q.
Proof.
  intros E ss ss' st ms md' Q HS Hw HAE Hrun Hne HI Hk.
  destruct (nk_E E HAE) as (E2 & E10 & _ & _ & _ & _ & _ & _ & E4).
  pose proof nf_errno as (Ee & _).
  eapply SRr_bind; [exact (mw_phase W E ss ss' st ms md' HS Hrun Hne)|].
  intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1 & HG1).
  set (OKw := fun z => (spZ regs - 48 <= z < spZ regs) \/ (f <= z < f + 4) \/ (f + 32 <= z < f + 48) \/
                       (f + 56 <= z < f + 64) \/ (f + 232 <= z < f + 248) \/ (as_errno B <= z < as_errno B + 4)).
  assert (WIN : forall z, in_wrange E (ss_mem ss) z -> OKw z).
  { intros z Hz. unfold OKw. rewrite Ee. destruct (mw_winC E (ss_mem ss) z Hw Hz) as [H|[H|[H|[H|[H|H]]]]];
      rewrite ?E2, ?E10, ?E4 in H; lia. }
  apply Hk; [exact HS1 | |].
  - apply (NINV_run B W K (spZ regs) f mem md OKw (ms_mem ms) md' (ms_mem ms1) mat1 HI).
    + intros y Hy. apply HF1. intros Hin. apply Hy. exact (WIN _ Hin).
    + intros y Hy. apply HFr1. intros Hin. apply Hy. exact (WIN _ Hin).
    + exact HG1.
    + intros z Hz. apply nf_safe. unfold OKw in Hz. nwlia.
  - intros z Hz H1 H2 H3 H4 H5 H6. apply aview_eq_of. apply HFr1. rewrite unsigned_lit_small by lia.
    intros Hin. pose proof (WIN _ Hin) as Hq. unfold OKw in Hq. lia.
Qed.

(* ---- the post at the three returns after the copy (the arm n1 = k) ---- *)
Lemma nD_post : forall (regs' : bvmap 5 word) (m m' : word -> option byte) md'' n2 flF wendF wposF wbaseF lenF,
  amf_n1 link_amf k pos = k -> n2 = Z.min (Z.of_nat (length ds)) (4096 - (pos + k)) ->
  (n2 < Z.of_nat (length ds) -> flF = Z.lor fl AF_ERR /\ wendF = 0 /\ wposF = 0 /\ wbaseF = 0) ->
  (n2 = Z.of_nat (length ds) -> flF = fl /\ wendF = wend /\ wposF = wbase /\ wbaseF = wbase) ->
  lenF = Z.max len (pos + k + n2) ->
  getr regs' 10 = Z_to_bv 64 n2 ->
  NINVk m' md'' ->
  amemfile_at tfibsegs link_amf (mrestrict (w_H W) m) f ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> ~ (f + 232 <= a < f + 248) ->
     a <> amf_buf link_amf + (pos + k + n2) -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  val_mem tfibsegs (mrestrict (w_H W) m) (f + 0) 4 flF -> val_mem tfibsegs (mrestrict (w_H W) m) (f + 32) 8 wendF ->
  val_mem tfibsegs (mrestrict (w_H W) m) (f + 40) 8 wposF -> val_mem tfibsegs (mrestrict (w_H W) m) (f + 56) 8 wbaseF ->
  val_mem tfibsegs (mrestrict (w_H W) m) (f + 136) 4 om ->
  azbytes tfibsegs (mrestrict (w_H W) m) (amf_buf link_amf + pos) (pb ++ firstn (Z.to_nat n2) ds) ->
  val_mem tfibsegs (mrestrict (w_H W) m') (f + 232) 8 (pos + k + n2) ->
  val_mem tfibsegs (mrestrict (w_H W) m') (f + 240) 8 lenF ->
  nPF regs' m'.
Proof.
  intros regs' m m' md'' n2 flF wendF wposF wbaseF lenF Hn1 Hn2 Hlt Heq HlenF Ha0 HI Hat Hfr V0 V32 V40 V56 V136 Hbz V232 V240.
  pose proof nf_blk as (_ & B0 & B63 & Bs & Bam & _). pose proof nf_pre as (_ & _ & L3 & L4 & _). pose proof nf_fimg as Fi.
  pose proof nf_cookie as (Hpl & Hls & Hom). pose proof nf_fl as Hfl.
  assert (Hpk : pos + k <= 4096) by (unfold amf_n1 in Hn1; cbn [amf_size link_amf] in Hn1; lia).
  assert (P1 : amw_pos1 link_amf k pos = pos + k) by (unfold amw_pos1; rewrite Hn1; reflexivity).
  assert (P2 : amw_n2 link_amf k pos (Z.of_nat (length ds)) = n2) by (unfold amw_n2; rewrite P1; cbn [amf_size link_amf]; lia).
  assert (TF : forall off (nb : nat) v, 0 <= off -> off + Z.of_nat nb <= 272 -> (off + Z.of_nat nb <= 232 \/ 248 <= off) ->
    val_mem tfibsegs (mrestrict (w_H W) m) (f + off) nb v -> val_mem tfibsegs (mrestrict (w_H W) m') (f + off) nb v).
  { intros off nb v H0 H1 H2 Hv. apply (mw_val_mem_xfer_av (w_H W) m m'); [|exact Hv].
    intros i Hi. apply Hfr; nwlia. }
  assert (Fl' : flF = AF_NORD \/ flF = AF_NORD + AF_ERR).
  { destruct (Z_lt_ge_dec n2 (Z.of_nat (length ds))) as [Hc|Hc].
    - right. rewrite (proj1 (Hlt Hc)). exact nf_lor.
    - assert (Hq : n2 = Z.of_nat (length ds)) by lia. rewrite (proj1 (Heq Hq)). exact Hfl. }
  assert (Wv : (wendF = 0 /\ wposF = 0 /\ wbaseF = 0) \/ (wendF = f + 1304 /\ wposF = f + 280 /\ wbaseF = f + 280)).
  { destruct (Z_lt_ge_dec n2 (Z.of_nat (length ds))) as [Hc|Hc].
    - left. destruct (Hlt Hc) as (_ & A2 & A3 & A4). auto.
    - assert (Hq : n2 = Z.of_nat (length ds)) by lia. destruct (Heq Hq) as (_ & A2 & A3 & A4).
      destruct nf_winA as [(_ & W1 & W2 & W3) | (W1 & W2 & W3)]; [left | right]; lia. }
  unfold nPF. cbv zeta. rewrite P1, P2.
  split.
  { apply (amf_at_rebuild (mrestrict (w_H W) m) (mrestrict (w_H W) m') f flF wendF wposF wbaseF (pos + k + n2) lenF Hat).
    - intros a Ha Hd. apply mbyte_of_aview. apply Hfr; unfold dynf in *; nwlia.
    - exact Fl'.
    - apply TF; [lia | cbn; lia | cbn; lia | exact V0].
    - destruct Wv as [W'|W']; [left; exact W' | right; unfold AMF_BUF, AMF_BUFSIZ; lia].
    - apply TF; [lia | cbn; lia | cbn; lia | exact V32].
    - apply TF; [lia | cbn; lia | cbn; lia | exact V40].
    - apply TF; [lia | cbn; lia | cbn; lia | exact V56].
    - lia.
    - cbn [amf_size link_amf]. lia.
    - exact V232.
    - exact V240. }
  split; [exact (nf_pend m' md'' HI)|].
  split; [intros Hc; lia|].
  intros _. split; [exact Ha0|]. split.
  - exists flF, wendF, wposF, wbaseF. split; [|split].
    + unfold amf_dyn. subst lenF.
      split; [destruct Fl' as [-> | ->]; unfold AF_NORD, AF_ERR; lia|].
      split; [exact Hom|].
      split; [destruct Wv as [(-> & -> & ->)|(-> & -> & ->)]; nwlia|].
      split; [destruct Wv as [(-> & -> & ->)|(-> & -> & ->)]; nwlia|].
      split; [destruct Wv as [(-> & -> & ->)|(-> & -> & ->)]; nwlia|].
      split; [lia|]. split; [cbn [amf_size link_amf]; lia|].
      split; [apply TF; [lia | cbn; lia | cbn; lia | exact V0]|].
      split; [apply TF; [lia | cbn; lia | cbn; lia | exact V136]|].
      split; [apply TF; [lia | cbn; lia | cbn; lia | exact V32]|].
      split; [apply TF; [lia | cbn; lia | cbn; lia | exact V40]|].
      split; [apply TF; [lia | cbn; lia | cbn; lia | exact V56]|].
      split; [exact V232 | exact V240].
    + intros Hc. destruct (Hlt Hc) as (A1 & A2 & A3 & A4). auto.
    + intros Hc. destruct (Heq Hc) as (A1 & A2 & A3 & A4). auto.
  - apply (mw_azbytes_xfer (w_H W) m m'); [|exact Hbz].
    intros i Hi. rewrite length_app, firstn_length_le in Hi by lia.
    apply Hfr; nwlia.
Qed.

(* ---- after the copy: +0xc4 to the return ---- *)
Lemma nD : forall E ms md' n2 flF wendF wposF wbaseF,
  st_ok tfibsegs E ssD (restrict (w_H W) ms) ->
  env_agree 33 nE0 E -> ew E 33 = Z_to_bv 64 (pos + k) -> ew E 34 = Z_to_bv 64 (Z.max len (pos + k)) ->
  ew E 71 = Z_to_bv 64 n2 ->
  amf_n1 link_amf k pos = k -> n2 = Z.min (Z.of_nat (length ds)) (4096 - (pos + k)) ->
  (n2 < Z.of_nat (length ds) -> flF = Z.lor fl AF_ERR /\ wendF = 0 /\ wposF = 0 /\ wbaseF = 0) ->
  (n2 = Z.of_nat (length ds) -> flF = fl /\ wendF = wend /\ wposF = wbase /\ wbaseF = wbase) ->
  NINVk (ms_mem ms) md' ->
  amemfile_at tfibsegs link_amf (mrestrict (w_H W) (ms_mem ms)) f ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 0) 4 flF ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 32) 8 wendF ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 40) 8 wposF ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 56) 8 wbaseF ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 136) 4 om ->
  azbytes tfibsegs (mrestrict (w_H W) (ms_mem ms)) (amf_buf link_amf + pos) (pb ++ firstn (Z.to_nat n2) ds) ->
  SRr tfibsegs W (mkCfg ms md') nFP.
Proof.
  intros E ms md' n2 flF wendF wposF wbaseF HS HAE E33 E34 E71 Hn1 Hn2 Hlt Heq HI Hat V0 V32 V40 V56 V136 Hbz.
  pose proof nf_blk as (_ & B0 & B63 & Bs & Bam & _). pose proof nf_pre as (Hra & _ & L3 & L4 & _). pose proof nf_fimg as Fi.
  pose proof nf_cookie as (Hpl & Hls & Hom).
  destruct (nk_E E HAE) as (E2 & E10 & _).
  assert (Hpk : pos + k <= 4096) by (unfold amf_n1 in Hn1; cbn [amf_size link_amf] in Hn1; lia).
  assert (Hn2r : 0 <= n2 <= Z.of_nat (length ds) /\ n2 <= 4096 - (pos + k)) by lia.
  assert (HAE32 : env_agree 32 (Ereg regs [Z_to_bv 64 (f + 280 + k)]) E) by exact (env_agree_le 33 32 _ _ ltac:(lia) HAE).
  assert (UL : U E (SOff 34 0) = Z.max len (pos + k)) by (apply (U_atom E 34); [exact E34 | lia]).
  assert (UN : U E SNP = pos + k + n2) by (unfold SNP; rewrite (vl_np E (pos + k) n2 0 E33 E71) by lia; lia).
  assert (DN : sv_denot E SNP = Z_to_bv 64 (pos + k + n2)) by (rewrite denot_lit_U, UN; reflexivity).
  assert (DL : sv_denot E (SOff 34 0) = Z_to_bv 64 (Z.max len (pos + k)))
    by (cbn [sv_denot]; rewrite E34, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
  assert (A10 : forall ss ms2, st_ok tfibsegs E ss (restrict (w_H W) ms2) -> sr_get (ss_regs ss) 10 = SOff 71 0 ->
     getr (ms_regs ms2) 10 = Z_to_bv 64 n2)
    by (intros ss ms2 HS2 Hr; rewrite (mw_reg_atom E ss ms2 (w_H W) 10 71 HS2 Hr); exact E71).
  apply (nD_step E ssD ssD_st1 _ ms md' nFP HS ltac:(vm_compute; reflexivity) HAE runD1 ltac:(discriminate) HI).
  intros ms1 mat1 HS1 HI1 HV1.
  destruct (Z_le_gt_dec (pos + k + n2) (Z.max len (pos + k))) as [Hge | Hlt1].
  - (* +0xd4 bgeu taken: len stays *)
    pose proof (st_ok_add_cond tfibsegs E ssD_st1 _ BC_GEU (SOff 34 0) SNP HS1
      ltac:(rewrite branch_geu_U, UL, UN; apply negb_true_iff, Z.ltb_ge; lia)) as HS2.
    change (YP06.add_cond ssD_st1 (mkAC BC_GEU (SOff 34 0) SNP)) with ssD_ge in HS2.
    apply (nD_step E ssD_ge ssD_ret1 _ ms1 _ nFP HS2 ltac:(vm_compute; reflexivity) HAE runD_ge ltac:(discriminate) HI1).
    intros ms2 mat2 HS3 HI2 HV2.
    pose proof (mw_ret_word ssD_ret1 (or_intror (or_introl eq_refl))) as (Rv & Rp & Rr & Rc).
    apply (nw_finish B W K (spZ regs) f mem md regs _ E ssD_ret1 ms2 _ nPF HS3 Rv Rp Rr Rc HAE32 Hra HI2).
    pose proof (mw_cval E ssD_ret1 ms2 (w_H W) 1 _ 0 232 8 SNP (pos + k + n2) HS3 eq_refl eq_refl DN
      ltac:(cbn; lia) ltac:(cbn; lia)) as VP.
    pose proof (mw_cval E ssD_ret1 ms2 (w_H W) 1 _ 1 240 8 (SOff 34 0) (Z.max len (pos + k)) HS3 eq_refl eq_refl DL
      ltac:(cbn; lia) ltac:(cbn; lia)) as VL.
    cbn [base_val YP09.r_base] in VP, VL. rewrite E10 in VP, VL.
    apply (nD_post (ms_regs ms2) (ms_mem ms) (ms_mem ms2) _ n2 flF wendF wposF wbaseF (Z.max len (pos + k))
      Hn1 Hn2 Hlt Heq ltac:(lia) (A10 _ _ HS3 eq_refl) HI2 Hat); try assumption.
    intros a Ha H1 H2 H3. rewrite HV2 by assumption. apply HV1; assumption.
  - (* +0xd4 not taken: len = pos *)
    pose proof (st_ok_add_cond_neg tfibsegs E ssD_st1 _ BC_GEU (SOff 34 0) SNP HS1
      ltac:(rewrite branch_geu_U, UL, UN; apply negb_false_iff, Z.ltb_lt; lia)) as HS2.
    rewrite ssD_lt_eq in HS2.
    apply (nD_step E ssD_lt ssD_st2 _ ms1 _ nFP HS2 ltac:(vm_compute; reflexivity) HAE runD2 ltac:(discriminate) HI1).
    intros ms2 mat2 HS3 HI2 HV2.
    assert (U4 : U E (SLit 4096) = 4096) by (apply U_lit; lia).
    destruct (Z_le_gt_dec 4096 (pos + k + n2)) as [Hge2 | Hlt2].
    + (* +0xe0 bgeu taken: pos = size, no NUL *)
      pose proof (st_ok_add_cond tfibsegs E ssD_st2 _ BC_GEU SNP (SLit 4096) HS3
        ltac:(rewrite branch_geu_U, UN, U4; apply negb_true_iff, Z.ltb_ge; lia)) as HS4.
      change (YP06.add_cond ssD_st2 (mkAC BC_GEU SNP (SLit 4096))) with ssD_ge2 in HS4.
      apply (nD_step E ssD_ge2 ssD_ret2 _ ms2 _ nFP HS4 ltac:(vm_compute; reflexivity) HAE runD_ge2 ltac:(discriminate) HI2).
      intros ms3 mat3 HS5 HI3 HV3.
      pose proof (mw_ret_word ssD_ret2 (or_intror (or_intror (or_introl eq_refl)))) as (Rv & Rp & Rr & Rc).
      apply (nw_finish B W K (spZ regs) f mem md regs _ E ssD_ret2 ms3 _ nPF HS5 Rv Rp Rr Rc HAE32 Hra HI3).
      pose proof (mw_cval E ssD_ret2 ms3 (w_H W) 1 _ 1 232 8 SNP (pos + k + n2) HS5 eq_refl eq_refl DN
        ltac:(cbn; lia) ltac:(cbn; lia)) as VP.
      pose proof (mw_cval E ssD_ret2 ms3 (w_H W) 1 _ 0 240 8 SNP (pos + k + n2) HS5 eq_refl eq_refl DN
        ltac:(cbn; lia) ltac:(cbn; lia)) as VL.
      cbn [base_val YP09.r_base] in VP, VL. rewrite E10 in VP, VL.
      apply (nD_post (ms_regs ms3) (ms_mem ms) (ms_mem ms3) _ n2 flF wendF wposF wbaseF (pos + k + n2)
        Hn1 Hn2 Hlt Heq ltac:(lia) (A10 _ _ HS5 eq_refl) HI3 Hat); try assumption.
      intros a Ha H1 H2 H3. rewrite HV3 by assumption. rewrite HV2 by assumption. apply HV1; assumption.
    + (* +0xe0 not taken: +0xec buf[pos] = 0 *)
      pose proof (st_ok_add_cond_neg tfibsegs E ssD_st2 _ BC_GEU SNP (SLit 4096) HS3
        ltac:(rewrite branch_geu_U, UN, U4; apply negb_false_iff, Z.ltb_lt; lia)) as HS4.
      rewrite ssD_lt2_eq in HS4.
      apply (nD_step E ssD_lt2 ssD_sb _ ms2 _ nFP HS4 ltac:(vm_compute; reflexivity) HAE runD_sb ltac:(discriminate) HI2).
      intros ms3 mat3 HS5 HI3 HV3.
      set (aN := amf_buf link_amf + (pos + k + n2)).
      assert (HaN : aN = 0x62fee0 + (pos + k + n2)) by reflexivity.
      destruct Hbuf as (_ & _ & _ & Hbw & _).
      apply (mw_sb_zero W E ssD_sb ms3 _ nFP aN HS5 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
      * replace (sr_get (ss_regs ssD_sb) 10) with (SAlu ALU_ADD (SOff 33 6487776) (SOff 71 0)) by (vm_compute; reflexivity).
        rewrite denot_lit_U, (vl_np E (pos + k) n2 6487776 E33 E71) by lia. rewrite HaN. f_equal. lia.
      * rewrite HaN. lia.
      * destruct HI3 as (_ & _ & Hpr3 & _).
        apply (mw_writable_grows (w_H W) mem (ms_mem ms3) aN (mw_apresent_restrict (w_H W) mem (ms_mem ms3) Hpr3)).
        apply (proj1 (Hbw aN ltac:(rewrite HaN; cbn [amf_buf amf_size link_amf]; lia))).
      * intros r Hr. vm_compute in Hr. destruct Hr as [<- | [<- | []]]; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi];
          rewrite ?E2, ?E10, HaN; nwlia.
      * intros ms4 mat4 HS6 HR1 HR2 HG4.
        assert (HI4 : NINVk (ms_mem ms4) (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy (with_vm_backing
                        (m_vm_lazy (with_vm_backing (m_vm_lazy md') mat1 md')) mat2 (with_vm_backing (m_vm_lazy md') mat1 md')))
                        mat3 (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md') mat1 md')) mat2
                        (with_vm_backing (m_vm_lazy md') mat1 md')))) mat4 (with_vm_backing (m_vm_lazy (with_vm_backing
                        (m_vm_lazy (with_vm_backing (m_vm_lazy md') mat1 md')) mat2 (with_vm_backing (m_vm_lazy md') mat1 md')))
                        mat3 (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md') mat1 md')) mat2
                        (with_vm_backing (m_vm_lazy md') mat1 md'))))).
        { apply (NINV_run B W K (spZ regs) f mem md (fun z => z = aN) (ms_mem ms3) _ (ms_mem ms4) mat4 HI3).
          - intros y Hy. exact (HR1 y Hy).
          - intros y Hy. exact (HR2 y Hy).
          - exact HG4.
          - intros z ->. apply nf_safe. right; right; right. rewrite HaN. cbn [amf_buf amf_size link_amf]. lia. }
        change (mkSS (ss_pc ssD_sb + 4) (ss_regs ssD_sb) (ss_mem ssD_sb) None (ss_facts ssD_sb)) with ssD_af in HS6.
        apply (nD_step E ssD_af ssD_ret3 _ ms4 _ nFP HS6 ltac:(vm_compute; reflexivity) HAE runD_af ltac:(discriminate) HI4).
        intros ms5 mat5 HS7 HI5 HV5.
        pose proof (mw_ret_word ssD_ret3 (or_intror (or_intror (or_intror eq_refl)))) as (Rv & Rp & Rr & Rc).
        apply (nw_finish B W K (spZ regs) f mem md regs _ E ssD_ret3 ms5 _ nPF HS7 Rv Rp Rr Rc HAE32 Hra HI5).
        pose proof (mw_cval E ssD_ret3 ms5 (w_H W) 1 _ 1 232 8 SNP (pos + k + n2) HS7 eq_refl eq_refl DN
          ltac:(cbn; lia) ltac:(cbn; lia)) as VP.
        pose proof (mw_cval E ssD_ret3 ms5 (w_H W) 1 _ 0 240 8 SNP (pos + k + n2) HS7 eq_refl eq_refl DN
          ltac:(cbn; lia) ltac:(cbn; lia)) as VL.
        cbn [base_val YP09.r_base] in VP, VL. rewrite E10 in VP, VL.
        apply (nD_post (ms_regs ms5) (ms_mem ms) (ms_mem ms5) _ n2 flF wendF wposF wbaseF (pos + k + n2)
          Hn1 Hn2 Hlt Heq ltac:(lia) (A10 _ _ HS7 eq_refl) HI5 Hat); try assumption.
        intros a Ha H1 H2 H3. rewrite HV5 by assumption.
        rewrite (aview_eq_of (w_H W) (ms_mem ms3) (ms_mem ms4) a)
          by (apply HR2; rewrite unsigned_lit_small by lia; exact H3).
        rewrite HV3 by assumption. rewrite HV2 by assumption. apply HV1; assumption.
Qed.

(* ---- +0xc0 jal 0x52d74: the copy (the memory-checking runtime's memcpy interceptor, no-AR form); then nD ---- *)
Lemma nM : forall E ss ms md' e2 n2 flF wendF wposF wbaseF,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  ss_pc ss = 0x52d74 -> ss_resv ss = None -> ss_atoms_lt 55 ss = true ->
  sr_get (ss_regs ss) 1 = SLit 0x96d84 -> sr_get (ss_regs ss) 2 = SOff 2 (-48) ->
  sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
  sr_get (ss_regs ss) 10 = SOff 33 6487776 -> sr_get (ss_regs ss) 11 = SOff 11 0 ->
  sr_get (ss_regs ss) 12 = e2 -> sr_get (ss_regs ss) 8 = e2 ->
  submem rsD (ss_mem ss) -> ss_atoms_lt 71 (ss_after_call ss rsD 55 0x96d84) = true ->
  mkSS 0x96d84 (sr_set (sr_sets (ss_regs ss) (junk_upd 55 CLOB)) 8 (SOff 71 0)) rsD None (mkFacts [] [] []) = ssD ->
  env_agree 33 nE0 E -> ew E 33 = Z_to_bv 64 (pos + k) -> ew E 34 = Z_to_bv 64 (Z.max len (pos + k)) ->
  sv_denot E e2 = Z_to_bv 64 n2 ->
  amf_n1 link_amf k pos = k -> n2 = Z.min (Z.of_nat (length ds)) (4096 - (pos + k)) ->
  (n2 < Z.of_nat (length ds) -> flF = Z.lor fl AF_ERR /\ wendF = 0 /\ wposF = 0 /\ wbaseF = 0) ->
  (n2 = Z.of_nat (length ds) -> flF = fl /\ wendF = wend /\ wposF = wbase /\ wbaseF = wbase) ->
  NINVk (ms_mem ms) md' ->
  amemfile_at tfibsegs link_amf (mrestrict (w_H W) (ms_mem ms)) f ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 0) 4 flF ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 32) 8 wendF ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 40) 8 wposF ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 56) 8 wbaseF ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 136) 4 om ->
  azbytes tfibsegs (mrestrict (w_H W) (ms_mem ms)) (amf_buf link_amf + pos) pb ->
  SRr tfibsegs W (mkCfg ms md') nFP.
Proof.
  intros E ss ms md' e2 n2 flF wendF wposF wbaseF HS Hpc Hrv Hat R1 R2 R3 R4 R10 R11 R12 R8 Hsub HatD HD
    HAE E33 E34 Hn2v Hn1 Hn2 Hlt Heq HI Hfa V0 V32 V40 V56 V136 Hbz.
  pose proof nf_blk as (_ & B0 & B63 & Bs & Bam & _). pose proof nf_fimg as Fi.
  pose proof nf_cookie as (Hpl & Hls & Hom). pose proof nf_pre as (_ & Hal & L3 & L4 & _ & Hgp & Htp).
  destruct (nk_E E HAE) as (E2 & E10 & _ & _ & E3 & E4 & E11 & _).
  assert (Hpk : pos + k <= 4096) by (unfold amf_n1 in Hn1; cbn [amf_size link_amf] in Hn1; lia).
  assert (Hn2r : 0 <= n2 <= Z.of_nat (length ds) /\ n2 <= 4096 - (pos + k)) by lia.
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E ss ms HS Hrv) as Hshape. rewrite Hpc in Hshape.
  pose proof HI as (Hsbm & Hfr & Hpr & Hwp & Hhs).
  destruct Hbuf as (Hb0 & Hb1 & Hb2 & Hbw & Hbam & Hbra & Hbhull).
  set (d := amf_buf link_amf + (pos + k)).
  assert (Hd : d = 0x62fee0 + (pos + k)) by reflexivity.
  assert (G1 : getr (ms_regs ms) 1 = Z_to_bv 64 0x96d84) by (rewrite (mw_reg_sv E ss ms (w_H W) 1 _ HS R1); reflexivity).
  assert (G2 : getr (ms_regs ms) 2 = Z_to_bv 64 (spZ regs - 48))
    by (rewrite (mw_reg_sv E ss ms (w_H W) 2 _ HS R2); cbn [sv_denot]; rewrite E2; f_equal; lia).
  assert (G3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite (mw_reg_atom E ss ms (w_H W) 3 3 HS R3), E3; exact Hgp).
  assert (G4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite (mw_reg_atom E ss ms (w_H W) 4 4 HS R4), E4; exact Htp).
  assert (G10 : getr (ms_regs ms) 10 = w64 d).
  { rewrite (mw_reg_sv E ss ms (w_H W) 10 _ HS R10). cbn [sv_denot]. rewrite E33, unsigned_lit_small by lia.
    unfold w64. rewrite Hd. f_equal. lia. }
  assert (G11 : getr (ms_regs ms) 11 = w64 x) by (rewrite (mw_reg_atom E ss ms (w_H W) 11 11 HS R11), E11; exact H11).
  assert (G12 : getr (ms_regs ms) 12 = w64 n2) by (rewrite (mw_reg_sv E ss ms (w_H W) 12 _ HS R12); exact Hn2v).
  assert (G8 : getr (ms_regs ms) 8 = Z_to_bv 64 n2) by (rewrite (mw_reg_sv E ss ms (w_H W) 8 _ HS R8); exact Hn2v).
  assert (Hsp1 : spZ (ms_regs ms) = spZ regs - 48)
    by (unfold spZ at 1; rewrite G2; apply unsigned_lit_small; nwlia).
  assert (BUFI : forall a, d <= a < d + n2 -> amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf)
    by (intros a Ha; rewrite Hd in Ha; cbn [amf_buf amf_size link_amf]; lia).
  set (regs1 := ms_regs ms) in *. set (m1 := ms_mem ms) in *.
  pose proof AMEMCPY0 as AM. unfold aintrin_noar_realizes, cfg_at in AM. rewrite (ts_code B TB) in AM.
  cbn [pc_wrap_memcpy Tfib_code] in AM.
  rewrite Hshape. eapply SRr_bind.
  { apply (AM W regs1 m1 md' d x n2).
    - split; [rewrite G1; apply YK0s.ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity|].
      rewrite Hsp1. split; [rewrite Zminus_mod, Hal; reflexivity|]. split; [nwlia|]. split; [nwlia|].
      split; [intros a Ha; apply Hwp; nwlia|]. split; [exact G3 | exact G4].
    - exact (nf_cells m1 md' HI).
    - exact G10. - exact G11. - exact G12.
    - lia. - rewrite Hd. lia. - rewrite Hd. lia.
    - intros a Ha. rewrite Hsp1. pose proof (Hbw a (BUFI a Ha)) as (Hw & Hs).
      split; [exact (mw_writable_grows (w_H W) mem m1 a (mw_apresent_restrict _ _ _ Hpr) Hw)|]. nwlia.
    - left. rewrite Hd. nwlia.
    - apply (nf_ra_xfer m1 md' d n2 HI); [rewrite Hd; lia | rewrite Hd; nwlia |].
      intros z Hz. apply Hbra. pose proof (BUFI z Hz). lia.
    - intros Hn. apply (nf_hull_xfer m1 md' d n2 HI); [rewrite Hd; lia | exact Hn | rewrite Hd; nwlia |].
      intros s Hs. apply Hbhull. cbn [amf_buf amf_size link_amf] in *. unfold shadow_addr, SHADOW_OFF in *. rewrite Hd in Hs.
      assert (Q1 : (2147450880 + 6487776 / 8) / 8 * 8 <= (2147450880 + (6487776 + (pos + k)) / 8) / 8 * 8).
      { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
      assert (Q2 : (2147450880 + (0x62fee0 + (pos + k) + n2 - 1) / 8) / 8 * 8 <= (2147450880 + (6487776 + 4096 - 1) / 8) / 8 * 8).
      { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
      lia.
    - split; [lia|]. split; [lia|]. split.
      + intros a Ha. rewrite Hsp1. split.
        * pose proof (nf_src m1 md' HI (Z.to_nat (a - x)) ltac:(lia)) as Hv. rewrite Z2Nat.id in Hv by lia.
          replace (x + (a - x)) with a in Hv by lia. rewrite Hv. discriminate.
        * destruct (Hxdisj a ltac:(lia)) as (_ & _ & _ & N4). nwlia.
      + split.
        { destruct (Z_le_gt_dec (d + n2) x) as [Q|Q]; [left; exact Q|].
          destruct (Z_le_gt_dec (x + n2) d) as [Q'|Q']; [right; exact Q'|]. exfalso.
          destruct (Hxdisj (Z.max x d) ltac:(lia)) as (N1 & _). apply N1. apply BUFI. lia. }
        split; [destruct Hxam as [Q|[Q1 Q2]]; [left; lia | right; lia]|].
        split.
        * apply (nf_ra_xfer m1 md' x n2 HI); [lia | destruct Hxam as [Q|[Q1 Q2]]; nwlia |].
          intros z Hz. apply Hxra. lia.
        * intros Hn. apply (nf_hull_xfer m1 md' x n2 HI); [lia | exact Hn | destruct Hxam as [Q|[Q1 Q2]]; nwlia |].
          intros s Hs. apply (Hxhull ltac:(lia)). unfold shadow_addr, SHADOW_OFF in *.
          assert (Q2 : (2147450880 + (x + n2 - 1) / 8) / 8 * 8 <= (2147450880 + (x + Z.of_nat (length ds) - 1) / 8) / 8 * 8).
          { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
          lia. }
  intros W2 c2 _ (-> & regs2 & m2 & md2 & -> & HP2 & Hsbm2 & Ha02 & Heff & Hfr2 & Hpr2 & Hhs2).
  cbv beta iota in Heff.
  assert (Hra1 : raZ regs1 = 0x96d84) by (unfold raZ; rewrite G1; apply unsigned_lit_small; lia).
  unfold cfg_at. rewrite Hra1. change (w64 0x96d84) with (Z_to_bv 64 0x96d84).
  assert (FR : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n2) -> ~ (spZ regs - 48 - ESTACK <= a < spZ regs - 48) ->
     aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) m1 a).
  { intros a Ha H1 H2. apply Hfr2; [exact Ha | exact H1 | rewrite Hsp1; exact H2]. }
  assert (PG : forall y, mrestrict (w_H W) m1 y <> None -> mrestrict (w_H W) m2 y <> None)
    by exact (mw_apresent_restrict _ _ _ Hpr2).
  assert (KEPT : Forall (region_kept tfibsegs E (mrestrict (w_H W) m1) (mrestrict (w_H W) m2)) rsD).
  { unfold rsD. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; apply (mw_region_kept E (w_H W) m1 m2); try exact PG;
      intros a Ha; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi] in Ha; rewrite ?E2, ?E10 in Ha; apply FR;
      rewrite ?Hd; nwlia. }
  rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
  pose proof (st_ok_after_call tfibsegs 55 E ss _ regs2 (mrestrict (w_H W) m2) rsD 0x96d84 HS Hrv Hat
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hsub R1 HP2 KEPT) as HSa.
  pose proof (st_ok_abstract_reg tfibsegs 71 _ _ _ 8 HSa HatD eq_refl) as HSb.
  pose proof (mw_st_ok_nofacts _ _ _ HSb) as HSc.
  cbn [ms_regs mkst] in HSc.
  set (E1 := havoc E 55 (map (getr regs2) CLOB)) in HSc.
  set (E2' := ewset E1 71 (getr regs2 8)) in HSc.
  assert (HSD : st_ok tfibsegs E2' ssD (restrict (w_H W) (mkst regs2 (Z_to_bv 64 0x96d84) m2 (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. rewrite <- HD. exact HSc. }
  assert (AG55 : env_agree 55 E E2').
  { apply (env_agree_trans 55 E E1 E2'); [exact (env_agree_havoc E 55 _)|].
    exact (env_agree_le 71 55 _ _ ltac:(lia) (env_agree_ewset E1 71 _)). }
  assert (HAE2 : env_agree 33 nE0 E2') by (apply (env_agree_trans 33 nE0 E E2'); [exact HAE | exact (env_agree_le 55 33 _ _ ltac:(lia) AG55)]).
  assert (P8 : getr regs2 8 = getr regs1 8) by exact (regs_preserved_frame regs1 regs2 HP2 8 eq_refl).
  assert (E71 : ew E2' 71 = Z_to_bv 64 n2).
  { unfold E2'. cbn [ew ewset]. try rewrite Nat.eqb_refl. rewrite P8. exact G8. }
  assert (HI2 : NINVk m2 md2).
  { apply (NINV_call B W K (spZ regs) f mem md (fun a => (d <= a < d + n2) \/ (spZ regs - 48 - ESTACK <= a < spZ regs - 48))
      m1 md' m2 md2 HI Hsbm2).
    - intros a Ha Hn. apply FR; [exact Ha | intros Q; apply Hn; left; exact Q | intros Q; apply Hn; right; exact Q].
    - exact Hpr2.
    - intros a [Ha|Ha]; [apply (nf_safe a); right; right; right; exact (BUFI a Ha) | apply (nf_safe a); left; nwlia].
    - exact Hhs2. }
  assert (TF : forall off (nb : nat) v, 0 <= off -> off + Z.of_nat nb <= 272 ->
    val_mem tfibsegs (mrestrict (w_H W) m1) (f + off) nb v -> val_mem tfibsegs (mrestrict (w_H W) m2) (f + off) nb v).
  { intros off nb v H0 H1 Hv. apply (mw_val_mem_xfer_av (w_H W) m1 m2); [|exact Hv].
    intros i Hi. apply FR; rewrite ?Hd; nwlia. }
  apply (nD E2' _ md2 n2 flF wendF wposF wbaseF HSD HAE2).
  - destruct AG55 as [A _]. rewrite (A 33%nat ltac:(lia)). exact E33.
  - destruct AG55 as [A _]. rewrite (A 34%nat ltac:(lia)). exact E34.
  - exact E71.
  - exact Hn1. - exact Hn2. - exact Hlt. - exact Heq.
  - exact HI2.
  - apply (amemfile_at_frame tfibsegs link_amf (mrestrict (w_H W) m1)); [|exact Hfa].
    intros z Hz. apply mbyte_of_aview. apply FR; rewrite ?Hd; nwlia.
  - apply TF; [lia | cbn; lia | exact V0].
  - apply TF; [lia | cbn; lia | exact V32].
  - apply TF; [lia | cbn; lia | exact V40].
  - apply TF; [lia | cbn; lia | exact V56].
  - apply TF; [lia | cbn; lia | exact V136].
  - apply mw_azbytes_app.
    + apply (mw_azbytes_xfer (w_H W) m1 m2); [|exact Hbz].
      intros i Hi. apply FR; rewrite ?Hd; nwlia.
    + intros i Hi. rewrite firstn_length_le in Hi by lia.
      change (aview tfibsegs (w_H W) m2 (amf_buf link_amf + pos + Z.of_nat (length pb) + Z.of_nat i) =
              Some (nth i (firstn (Z.to_nat n2) ds) 0)).
      rewrite mw_nth_firstn by exact Hi.
      replace (amf_buf link_amf + pos + Z.of_nat (length pb) + Z.of_nat i) with (d + Z.of_nat i) by (rewrite Hd; cbn [amf_buf link_amf]; lia).
      rewrite Heff by lia. exact (nf_src m1 md' HI i ltac:(lia)).
Qed.

(* ---- after the inner call (k > 0): +0x50 to the copy, or to the return when the inner call stopped at g_said's end ---- *)
Lemma nC : forall E ms md' fl1 wend1 wpos1 wbase1,
  0 < k ->
  st_ok tfibsegs E ssC (restrict (w_H W) ms) ->
  env_agree 33 nE0 E ->
  ew E 33 = Z_to_bv 64 (pos + amf_n1 link_amf k pos) ->
  ew E 34 = Z_to_bv 64 (Z.max len (pos + amf_n1 link_amf k pos)) ->
  ew E 35 = Z_to_bv 64 fl1 -> ew E 36 = Z_to_bv 64 wend1 -> ew E 37 = Z_to_bv 64 wpos1 -> ew E 38 = Z_to_bv 64 wbase1 ->
  ew E 43 = Z_to_bv 64 (amf_n1 link_amf k pos) ->
  (amf_n1 link_amf k pos < k -> fl1 = Z.lor fl AF_ERR /\ wend1 = 0 /\ wpos1 = 0 /\ wbase1 = 0) ->
  (amf_n1 link_amf k pos = k -> fl1 = fl /\ wend1 = f + 1304 /\ wpos1 = f + 280 /\ wbase1 = f + 280) ->
  NINVk (ms_mem ms) md' ->
  amemfile_at tfibsegs link_amf (mrestrict (w_H W) (ms_mem ms)) f ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 136) 4 om ->
  azbytes tfibsegs (mrestrict (w_H W) (ms_mem ms)) (amf_buf link_amf + pos) (firstn (Z.to_nat (amf_n1 link_amf k pos)) pb) ->
  SRr tfibsegs W (mkCfg ms md') nFP.
Proof.
  intros E ms md' fl1 wend1 wpos1 wbase1 Hkp HS HAE E33 E34 E35 E36 E37 E38 E43 Hlt Heq HI Hfa V136 Hbz.
  pose proof nf_blk as (_ & B0 & B63 & Bs & Bam & _). pose proof nf_pre as (Hra & _ & L3 & L4 & _). pose proof nf_fimg as Fi.
  pose proof nf_cookie as (Hpl & Hls & Hom). pose proof nf_fl as Hfl.
  pose proof (nf_win Hkp) as (Wend & Wpos & Wbase).
  destruct (nk_E E HAE) as (E2 & E10 & E32 & _ & _ & _ & _ & E12 & E4).
  set (n1 := amf_n1 link_amf k pos) in *.
  assert (Hn1r : 0 <= n1 <= k /\ (n1 < k -> n1 = 4096 - pos)) by (unfold n1, amf_n1; cbn [amf_size link_amf]; lia).
  assert (HAE32 : env_agree 32 (Ereg regs [Z_to_bv 64 (f + 280 + k)]) E) by exact (env_agree_le 33 32 _ _ ltac:(lia) HAE).
  assert (U43 : U E (SOff 43 0) = n1) by (apply (U_atom E 43); [exact E43 | nwlia]).
  assert (UK : U E SK3 = k) by (exact (proj1 (vl_k E f k E10 E32 ltac:(lia) ltac:(lia) ltac:(nwlia)))).
  assert (DA : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
  set (CW := fun a => (spZ regs - 48 <= a < spZ regs) \/ (f <= a < f + 4) \/ (f + 32 <= a < f + 48) \/
                      (f + 56 <= a < f + 64) \/ (f + 232 <= a < f + 248) \/ (as_errno B <= a < as_errno B + 4)).
  assert (FW : forall a, f <= a < f + AMF_ZEROED -> ~ dynf (a - f) -> ~ CW a).
  { intros a Ha Hd Hc. pose proof nf_errno as (Ee & _). unfold CW in Hc. rewrite Ee in Hc. unfold dynf in *. nwlia. }
  apply (nC_step E ssC ssC_st1 _ ms md' nFP HS ltac:(vm_compute; reflexivity) HAE runC1 ltac:(discriminate) HI).
  intros ms1 mat1 HS1 HI1 HV1.
  destruct (Z_lt_ge_dec n1 k) as [Hlt1 | Hge1].
  - (* +0x50 bgeu not taken: s0 = 0, return 0 *)
    destruct (Hlt Hlt1) as (F1 & F2 & F3 & F4).
    pose proof (st_ok_add_cond_neg tfibsegs E ssC_st1 _ BC_GEU (SOff 43 0) SK3 HS1
      ltac:(rewrite branch_geu_U, U43, UK; apply negb_false_iff, Z.ltb_lt; lia)) as HS2.
    rewrite ssC_lt_eq in HS2.
    apply (nC_step E ssC_lt ssC_ret _ ms1 _ nFP HS2 ltac:(vm_compute; reflexivity) HAE runC_lt ltac:(discriminate) HI1).
    intros ms2 mat2 HS3 HI2 HV2.
    pose proof (mw_ret_word ssC_ret (or_introl eq_refl)) as (Rv & Rp & Rr & Rc).
    apply (nw_finish B W K (spZ regs) f mem md regs _ E ssC_ret ms2 _ nPF HS3 Rv Rp Rr Rc HAE32 Hra HI2).
    assert (Hfl1 : fl1 = AF_NORD + AF_ERR) by (rewrite F1; exact nf_lor).
    pose proof (mw_cval E ssC_ret ms2 (w_H W) 1 _ 0 0 4 (SOff 35 0) fl1 HS3 eq_refl eq_refl (DA 35%nat fl1 E35 ltac:(rewrite Hfl1; unfold AF_NORD, AF_ERR; lia))
      ltac:(cbn; rewrite Hfl1; unfold AF_NORD, AF_ERR; lia) ltac:(cbn; lia)) as VF.
    pose proof (mw_cval E ssC_ret ms2 (w_H W) 2 _ 0 32 8 (SOff 36 0) wend1 HS3 eq_refl eq_refl (DA 36%nat wend1 E36 ltac:(lia))
      ltac:(cbn; lia) ltac:(cbn; lia)) as VW1.
    pose proof (mw_cval E ssC_ret ms2 (w_H W) 2 _ 1 40 8 (SOff 37 0) wpos1 HS3 eq_refl eq_refl (DA 37%nat wpos1 E37 ltac:(lia))
      ltac:(cbn; lia) ltac:(cbn; lia)) as VW2.
    pose proof (mw_cval E ssC_ret ms2 (w_H W) 3 _ 0 56 8 (SOff 38 0) wbase1 HS3 eq_refl eq_refl (DA 38%nat wbase1 E38 ltac:(lia))
      ltac:(cbn; lia) ltac:(cbn; lia)) as VW3.
    pose proof (mw_cval E ssC_ret ms2 (w_H W) 4 _ 0 232 8 (SOff 33 0) (pos + n1) HS3 eq_refl eq_refl (DA 33%nat _ E33 ltac:(lia))
      ltac:(cbn; lia) ltac:(cbn; lia)) as VP.
    pose proof (mw_cval E ssC_ret ms2 (w_H W) 4 _ 1 240 8 (SOff 34 0) (Z.max len (pos + n1)) HS3 eq_refl eq_refl (DA 34%nat _ E34 ltac:(lia))
      ltac:(cbn; lia) ltac:(cbn; lia)) as VL.
    cbn [base_val YP09.r_base] in VF, VW1, VW2, VW3, VP, VL. rewrite E10 in VF, VW1, VW2, VW3, VP, VL.
    rewrite F2 in VW1. rewrite F3 in VW2. rewrite F4 in VW3.
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ CW a -> aview tfibsegs (w_H W) (ms_mem ms2) a = aview tfibsegs (w_H W) (ms_mem ms) a).
    { intros a Ha Hc. unfold CW in Hc. rewrite HV2 by (try exact Ha; intros Q; apply Hc; tauto). apply HV1; try exact Ha; intros Q; apply Hc; tauto. }
    unfold nPF. cbv zeta. change (amw_pos1 link_amf k pos) with (pos + n1).
    split.
    { apply (amf_at_rebuild (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms2)) f fl1 0 0 0 (pos + n1) (Z.max len (pos + n1)) Hfa).
      - intros a Ha Hd. apply mbyte_of_aview. apply KEEP; [nwlia | exact (FW a Ha Hd)].
      - right. exact Hfl1.
      - exact VF.
      - left. auto.
      - exact VW1. - exact VW2. - exact VW3.
      - lia.
      - cbn [amf_size link_amf]. lia.
      - exact VP. - exact VL. }
    split; [exact (nf_pend _ _ HI2)|].
    split.
    + intros _. split; [rewrite (mw_reg_sv E ssC_ret ms2 (w_H W) 10 (SLit 0) HS3 eq_refl); reflexivity|].
      split.
      * rewrite <- F1. unfold amf_dyn. split; [rewrite Hfl1; unfold AF_NORD, AF_ERR; lia|]. split; [exact Hom|].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [cbn [amf_size link_amf]; lia|].
        split; [exact VF|]. split.
        { apply (mw_val_mem_xfer_av (w_H W) (ms_mem ms) (ms_mem ms2)); [|exact V136].
          intros i Hi. apply KEEP; [nwlia|]. apply (FW (f + 136 + i)); [unfold AMF_ZEROED; cbn in Hi; lia | unfold dynf; cbn in Hi; lia]. }
        split; [exact VW1|]. split; [exact VW2|]. split; [exact VW3|]. split; [exact VP | exact VL].
      * apply (mw_azbytes_xfer (w_H W) (ms_mem ms) (ms_mem ms2)); [|exact Hbz].
        intros i Hi. rewrite firstn_length_le in Hi by lia. apply KEEP; [nwlia|].
        pose proof nf_errno as (Ee & _). unfold CW. rewrite Ee. nwlia.
    + intros Hc. lia.
  - (* +0x50 bgeu taken: n1 = k, the k = 0 path from +0x5c *)
    assert (Hn1k : n1 = k) by lia. destruct (Heq Hn1k) as (F1 & F2 & F3 & F4).
    pose proof (st_ok_add_cond tfibsegs E ssC_st1 _ BC_GEU (SOff 43 0) SK3 HS1
      ltac:(rewrite branch_geu_U, U43, UK; apply negb_true_iff, Z.ltb_ge; lia)) as HS2.
    change (YP06.add_cond ssC_st1 (mkAC BC_GEU (SOff 43 0) SK3)) with ssC_ge in HS2.
    apply (nC_step E ssC_ge ssC_st2 _ ms1 _ nFP HS2 ltac:(vm_compute; reflexivity) HAE runC2 ltac:(discriminate) HI1).
    intros ms2 mat2 HS3 HI2 HV2.
    assert (E33' : ew E 33 = Z_to_bv 64 (pos + k)) by (rewrite E33, Hn1k; reflexivity).
    assert (E34' : ew E 34 = Z_to_bv 64 (Z.max len (pos + k))) by (rewrite E34, Hn1k; reflexivity).
    assert (Hpk : pos + k <= 4096) by (unfold n1, amf_n1 in Hn1k; cbn [amf_size link_amf] in Hn1k; lia).
    assert (UR : U E SROOM = 4096 - (pos + k)) by (apply vl_room; [exact E33' | lia]).
    assert (U12 : U E (SOff 12 0) = Z.of_nat (length ds)) by (apply (U_atom E 12); [rewrite E12, H12; reflexivity | lia]).
    assert (KEEP2 : forall ms3, (forall a, 0 <= a < 2 ^ 64 -> ~ CW a ->
        aview tfibsegs (w_H W) (ms_mem ms3) a = aview tfibsegs (w_H W) (ms_mem ms2) a) ->
        forall a, 0 <= a < 2 ^ 64 -> ~ CW a -> aview tfibsegs (w_H W) (ms_mem ms3) a = aview tfibsegs (w_H W) (ms_mem ms) a).
    { intros ms3 H3 a Ha Hc. rewrite H3 by assumption. unfold CW in Hc.
      rewrite HV2 by (try exact Ha; intros Q; apply Hc; tauto). apply HV1; try exact Ha; intros Q; apply Hc; tauto. }
    assert (Hpb : firstn (Z.to_nat n1) pb = pb) by (apply firstn_all2; lia).
    rewrite Hpb in Hbz.
    destruct (Z_le_gt_dec (Z.of_nat (length ds)) (4096 - (pos + k))) as [Hfit | Hover].
    + (* +0x80 bgeu taken: the data fits *)
      pose proof (st_ok_add_cond tfibsegs E ssC_st2 _ BC_GEU SROOM (SOff 12 0) HS3
        ltac:(rewrite branch_geu_U, UR, U12; apply negb_true_iff, Z.ltb_ge; lia)) as HS4.
      change (YP06.add_cond ssC_st2 (mkAC BC_GEU SROOM (SOff 12 0))) with ssC_n in HS4.
      apply (nC_step E ssC_n ssM1 _ ms2 _ nFP HS4 ltac:(vm_compute; reflexivity) HAE runM1 ltac:(discriminate) HI2).
      intros ms3 mat3 HS5 HI3 HV3.
      pose proof (KEEP2 ms3 ltac:(intros a Ha Hc; unfold CW in Hc; apply HV3; try exact Ha; intros Q; apply Hc; tauto)) as KP.
      pose proof (mw_cval E ssM1 ms3 (w_H W) 1 _ 0 0 4 (SOff 35 0) fl1 HS5 eq_refl eq_refl (DA 35%nat fl1 E35 ltac:(rewrite F1; destruct Hfl as [-> | ->]; unfold AF_NORD, AF_ERR; lia))
        ltac:(cbn; rewrite F1; destruct Hfl as [-> | ->]; unfold AF_NORD, AF_ERR; lia) ltac:(cbn; lia)) as VF.
      pose proof (mw_cval E ssM1 ms3 (w_H W) 2 _ 0 32 8 (SOff 36 0) wend1 HS5 eq_refl eq_refl (DA 36%nat wend1 E36 ltac:(rewrite F2; nwlia))
        ltac:(cbn; rewrite F2; nwlia) ltac:(cbn; lia)) as VW1.
      pose proof (mw_cval E ssM1 ms3 (w_H W) 2 _ 1 40 8 (SOff 37 0) wpos1 HS5 eq_refl eq_refl (DA 37%nat wpos1 E37 ltac:(rewrite F3; nwlia))
        ltac:(cbn; rewrite F3; nwlia) ltac:(cbn; lia)) as VW2.
      pose proof (mw_cval E ssM1 ms3 (w_H W) 3 _ 0 56 8 (SOff 38 0) wbase1 HS5 eq_refl eq_refl (DA 38%nat wbase1 E38 ltac:(rewrite F4; nwlia))
        ltac:(cbn; rewrite F4; nwlia) ltac:(cbn; lia)) as VW3.
      pose proof (mw_cval E ssM1 ms3 (w_H W) 4 _ 0 232 8 (SOff 33 0) (pos + k) HS5 eq_refl eq_refl (DA 33%nat _ E33' ltac:(lia))
        ltac:(cbn; lia) ltac:(cbn; lia)) as VP.
      pose proof (mw_cval E ssM1 ms3 (w_H W) 4 _ 1 240 8 (SOff 34 0) (Z.max len (pos + k)) HS5 eq_refl eq_refl (DA 34%nat _ E34' ltac:(lia))
        ltac:(cbn; lia) ltac:(cbn; lia)) as VL.
      cbn [base_val YP09.r_base] in VF, VW1, VW2, VW3, VP, VL. rewrite E10 in VF, VW1, VW2, VW3, VP, VL.
      rewrite F1 in VF. rewrite F2 in VW1. rewrite F3 in VW2. rewrite F4 in VW3.
      assert (Hat3 : amf_k tfibsegs link_amf (mrestrict (w_H W) (ms_mem ms3)) f 0).
      { apply (amf_at_rebuild (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms3)) f fl (f + 1304) (f + 280) (f + 280)
          (pos + k) (Z.max len (pos + k)) Hfa).
        - intros a Ha Hd. apply mbyte_of_aview. apply KP; [nwlia | exact (FW a Ha Hd)].
        - exact Hfl. - exact VF.
        - right. unfold AMF_BUF, AMF_BUFSIZ. lia.
        - exact VW1. - exact VW2. - exact VW3.
        - lia. - cbn [amf_size link_amf]. lia. - exact VP. - exact VL. }
      apply (nM E ssM1 ms3 _ (SOff 12 0) (Z.of_nat (length ds)) fl (f + 1304) (f + 280) (f + 280) HS5 eq_refl eq_refl
        ltac:(vm_compute; reflexivity) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
        ltac:(vm_compute; submem_tac) ltac:(vm_compute; reflexivity) ssD_1 HAE E33' E34').
      * cbn [sv_denot]. rewrite E12, H12, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
      * unfold n1 in Hn1k. exact Hn1k.
      * lia.
      * intros Hc. lia.
      * intros _. repeat split; lia.
      * exact HI3.
      * exact (proj1 Hat3).
      * exact VF. * exact VW1. * exact VW2. * exact VW3.
      * apply (mw_val_mem_xfer_av (w_H W) (ms_mem ms) (ms_mem ms3)); [|exact V136].
        intros i Hi. apply KP; [nwlia|]. apply (FW (f + 136 + i)); [unfold AMF_ZEROED; cbn in Hi; lia | unfold dynf; cbn in Hi; lia].
      * apply (mw_azbytes_xfer (w_H W) (ms_mem ms) (ms_mem ms3)); [|exact Hbz].
        intros i Hi. apply KP; [nwlia|]. pose proof nf_errno as (Ee & _). unfold CW. rewrite Ee. nwlia.
    + (* +0x80 bgeu not taken: ENOSPC, errno, F_ERR, the window emptied, n2 = size - pos1 *)
      pose proof (st_ok_add_cond_neg tfibsegs E ssC_st2 _ BC_GEU SROOM (SOff 12 0) HS3
        ltac:(rewrite branch_geu_U, UR, U12; apply negb_false_iff, Z.ltb_lt; lia)) as HS4.
      rewrite ssC_e_eq in HS4.
      apply (nC_step E ssC_e ssM2 _ ms2 _ nFP HS4 ltac:(vm_compute; reflexivity) HAE runM2 ltac:(discriminate) HI2).
      intros ms3 mat3 HS5 HI3 HV3.
      pose proof (KEEP2 ms3 ltac:(intros a Ha Hc; unfold CW in Hc; apply HV3; try exact Ha; intros Q; apply Hc; tauto)) as KP.
      assert (D0 : sv_denot E (SLit 0) = Z_to_bv 64 0) by reflexivity.
      pose proof (mw_cval E ssM2 ms3 (w_H W) 1 _ 0 0 4 (SAlu ALU_OR (SExt true 32 (SOff 35 0)) (SLit 32)) (AF_NORD + AF_ERR) HS5 eq_refl eq_refl
        (vl_flags E fl1 E35 ltac:(rewrite F1; exact Hfl)) ltac:(cbn; unfold AF_NORD, AF_ERR; lia) ltac:(cbn; lia)) as VF.
      pose proof (mw_cval E ssM2 ms3 (w_H W) 2 _ 1 32 8 (SLit 0) 0 HS5 eq_refl eq_refl D0 ltac:(cbn; lia) ltac:(cbn; lia)) as VW1.
      pose proof (mw_cval E ssM2 ms3 (w_H W) 2 _ 0 40 8 (SLit 0) 0 HS5 eq_refl eq_refl D0 ltac:(cbn; lia) ltac:(cbn; lia)) as VW2.
      pose proof (mw_cval E ssM2 ms3 (w_H W) 3 _ 0 56 8 (SLit 0) 0 HS5 eq_refl eq_refl D0 ltac:(cbn; lia) ltac:(cbn; lia)) as VW3.
      pose proof (mw_cval E ssM2 ms3 (w_H W) 4 _ 0 232 8 (SOff 33 0) (pos + k) HS5 eq_refl eq_refl (DA 33%nat _ E33' ltac:(lia))
        ltac:(cbn; lia) ltac:(cbn; lia)) as VP.
      pose proof (mw_cval E ssM2 ms3 (w_H W) 4 _ 1 240 8 (SOff 34 0) (Z.max len (pos + k)) HS5 eq_refl eq_refl (DA 34%nat _ E34' ltac:(lia))
        ltac:(cbn; lia) ltac:(cbn; lia)) as VL.
      cbn [base_val YP09.r_base] in VF, VW1, VW2, VW3, VP, VL. rewrite E10 in VF, VW1, VW2, VW3, VP, VL.
      assert (Hat3 : amf_k tfibsegs link_amf (mrestrict (w_H W) (ms_mem ms3)) f 0).
      { apply (amf_at_rebuild (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms3)) f (AF_NORD + AF_ERR) 0 0 0
          (pos + k) (Z.max len (pos + k)) Hfa).
        - intros a Ha Hd. apply mbyte_of_aview. apply KP; [nwlia | exact (FW a Ha Hd)].
        - right. reflexivity. - exact VF.
        - left. auto.
        - exact VW1. - exact VW2. - exact VW3.
        - lia. - cbn [amf_size link_amf]. lia. - exact VP. - exact VL. }
      apply (nM E ssM2 ms3 _ SROOM (4096 - (pos + k)) (Z.lor fl AF_ERR) 0 0 0 HS5 eq_refl eq_refl
        ltac:(vm_compute; reflexivity) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
        ltac:(vm_compute; submem_tac) ltac:(vm_compute; reflexivity) ssD_2 HAE E33' E34').
      * rewrite denot_lit_U, UR. reflexivity.
      * unfold n1 in Hn1k. exact Hn1k.
      * lia.
      * intros _. auto.
      * intros Hc. lia.
      * exact HI3.
      * exact (proj1 Hat3).
      * rewrite nf_lor. exact VF. * exact VW1. * exact VW2. * exact VW3.
      * apply (mw_val_mem_xfer_av (w_H W) (ms_mem ms) (ms_mem ms3)); [|exact V136].
        intros i Hi. apply KP; [nwlia|]. apply (FW (f + 136 + i)); [unfold AMF_ZEROED; cbn in Hi; lia | unfold dynf; cbn in Hi; lia].
      * apply (mw_azbytes_xfer (w_H W) (ms_mem ms) (ms_mem ms3)); [|exact Hbz].
        intros i Hi. apply KP; [nwlia|]. pose proof nf_errno as (Ee & _). unfold CW. rewrite Ee. nwlia.
Qed.

(* ---- the walk at k = 0: +0x00 to +0x80 (no inner call), then the two arms to the copy ---- *)
Definition EZ : env := Ereg regs [Z_to_bv 64 (f + 280 + k); Z_to_bv 64 pos; Z_to_bv 64 len; Z_to_bv 64 fl;
  Z_to_bv 64 wend; Z_to_bv 64 wpos; Z_to_bv 64 wbase].

Lemma EZ_agree : env_agree 33 nE0 EZ.
Proof.
  split; [|reflexivity]. intros n Hn. unfold nE0, EZ, Ereg. cbn [ew].
  destruct (n <? 32)%nat eqn:Hc; [reflexivity|]. apply Nat.ltb_ge in Hc. replace n with 32%nat by lia. reflexivity.
Qed.

Lemma nZ_entry : st_ok tfibsegs EZ ssZ (restrict (w_H W) (mkst regs (Z_to_bv 64 LA_MWRITE) mem (seg_rom tfibsegs))).
Proof.
  pose proof nf_pre as (_ & _ & L3 & L4 & Hpw & _ & Htp). pose proof nf_blk as (B16 & B0 & B63 & Bs & Bam & Bp & _).
  pose proof nf_fimg as Fi. pose proof nf_errno as (Ee & Etp). pose proof nf_cookie as (Hpl & Hls & Hom).
  pose proof Hamk as ((_ & _ & _ & Hst & _) & _).
  destruct Hst as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S152 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ssz & Sbuf & Smode).
  pose proof Hdyn as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & D0 & D136 & D32 & D40 & D56 & D232 & D240).
  destruct (nk_E EZ EZ_agree) as (E2 & E10 & _ & _ & _ & _ & _ & _ & E4v).
  assert (DA : forall n v, ew EZ n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot EZ (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
  rewrite restrict_mkst_fx. unfold ssZ. apply (entry_st_ok_full tfibsegs); fold EZ.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold rsZ.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]].
    + apply (region_ok_stack tfibsegs EZ _ 2 (spZ regs) (-48)); [exact E2 | nwlia | nwlia |].
      intros a Ha. apply apresent_writable. apply Hpw. nwlia.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val RF_fl]. rewrite E10.
      split; [lia|]. split; [nwlia|]. split; [intros o Ho; exact (proj1 (proj2 (Bp (f + o) ltac:(nwlia))))|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs EZ _ f 0 4 (SOff 35 0) fl); [apply DA; [exact (ew_Ereg_extra regs _ 3) | lia] | cbn; lia | cbn; lia | exact D0].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val RF_win]. rewrite E10.
      split; [lia|]. split; [nwlia|]. split; [intros o Ho; exact (proj1 (proj2 (Bp (f + o) ltac:(nwlia))))|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val tfibsegs EZ _ f 32 8 (SOff 36 0) wend); [apply DA; [exact (ew_Ereg_extra regs _ 4) | lia] | cbn; lia | cbn; lia | exact D32].
      * apply (chunk_ok_val tfibsegs EZ _ f 40 8 (SOff 37 0) wpos); [apply DA; [exact (ew_Ereg_extra regs _ 5) | lia] | cbn; lia | cbn; lia | exact D40].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val RZ_wb]. rewrite E10.
      split; [lia|]. split; [nwlia|]. split; [intros o Ho; exact (proj1 (proj2 (Bp (f + o) ltac:(nwlia))))|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val tfibsegs EZ _ f 56 8 (SOff 38 0) wbase); [apply DA; [exact (ew_Ereg_extra regs _ 6) | lia] | cbn; lia | cbn; lia | exact D56].
      * apply (chunk_ok_val tfibsegs EZ _ f 152 8 (SOff 10 232) (f + 232)); [cbn [sv_denot]; rewrite E10; reflexivity | cbn; nwlia | cbn; lia |].
        exact S152.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val RF_ck]. rewrite E10.
      split; [lia|]. split; [nwlia|]. split; [intros o Ho; exact (proj1 (proj2 (Bp (f + o) ltac:(nwlia))))|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
      * apply (chunk_ok_val tfibsegs EZ _ f 232 8 (SOff 33 0) pos); [apply DA; [exact (ew_Ereg_extra regs _ 1) | lia] | cbn; lia | cbn; lia | exact D232].
      * apply (chunk_ok_val tfibsegs EZ _ f 240 8 (SOff 34 0) len); [apply DA; [exact (ew_Ereg_extra regs _ 2) | lia] | cbn; lia | cbn; lia | exact D240].
      * apply (chunk_ok_val tfibsegs EZ _ f 248 8 (SLit 4096) 4096); [reflexivity | cbn; lia | cbn; lia | exact Ssz].
      * apply (chunk_ok_val tfibsegs EZ _ f 256 8 (SLit 0x62fee0) 0x62fee0); [reflexivity | cbn; lia | cbn; lia | exact Sbuf].
      * apply (chunk_ok_val tfibsegs EZ _ f 264 4 (SLit 119) 119); [reflexivity | cbn; lia | cbn; lia | exact Smode].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val R_errno]. rewrite E4v.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply mw_errno_writable; lia | apply Forall_nil].
  - apply pairwise_disjoint_of_extents. unfold rsZ, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val R_stkA RF_fl RF_win RZ_wb RF_ck R_errno]. rewrite E2, E10, E4v.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; nwlia.
  - split; [cbn; exact I | split; exact I].
Qed.

Lemma nZ : k = 0 -> SRr tfibsegs W (cfg_at tfibsegs LA_MWRITE regs mem md) nFP.
Proof.
  intros Hk0.
  pose proof nf_pre as (Hra & Hal & L3 & L4 & Hpw & Hgp & Htp). pose proof nf_blk as (B16 & B0 & B63 & Bs & Bam & Bp & Bra & Bhull).
  pose proof nf_fimg as Fi. pose proof nf_cookie as (Hpl & Hls & Hom). pose proof nf_fl as Hfl. pose proof nf_errno as (Ee & Etp).
  pose proof Hdyn as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & D0 & D136 & D32 & D40 & D56 & D232 & D240).
  assert (Wz : wpos = wbase /\ ((wend = 0 /\ wbase = 0) \/ (wend = f + 1304 /\ wbase = f + 280))).
  { destruct nf_winA as [(_ & W1 & W2 & W3) | (W1 & W2 & W3)]; [split; [lia | left; lia] | split; [lia | right; lia]]. }
  destruct Wz as (Wpb & Wv).
  assert (Hpb0 : pb = []) by (destruct pb as [|b pb']; [reflexivity | cbn [length] in Hpbk; lia]).
  assert (HAE := EZ_agree).
  destruct (nk_E EZ HAE) as (E2 & E10 & E32 & _ & _ & _ & _ & E12 & E4).
  assert (E33 : ew EZ 33 = Z_to_bv 64 pos) by exact (ew_Ereg_extra regs _ 1).
  assert (E34 : ew EZ 34 = Z_to_bv 64 len) by exact (ew_Ereg_extra regs _ 2).
  assert (E35 : ew EZ 35 = Z_to_bv 64 fl) by exact (ew_Ereg_extra regs _ 3).
  assert (E36 : ew EZ 36 = Z_to_bv 64 wend) by exact (ew_Ereg_extra regs _ 4).
  assert (E37 : ew EZ 37 = Z_to_bv 64 wpos) by exact (ew_Ereg_extra regs _ 5).
  assert (E38 : ew EZ 38 = Z_to_bv 64 wbase) by exact (ew_Ereg_extra regs _ 6).
  assert (E33' : ew EZ 33 = Z_to_bv 64 (pos + k)) by (rewrite E33, Hk0, Z.add_0_r; reflexivity).
  assert (E34' : ew EZ 34 = Z_to_bv 64 (Z.max len (pos + k))) by (rewrite E34, Hk0, Z.add_0_r, Z.max_l by lia; reflexivity).
  assert (DA : forall n v, ew EZ n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot EZ (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
  set (CW := fun a => (spZ regs - 48 <= a < spZ regs) \/ (f <= a < f + 4) \/ (f + 32 <= a < f + 48) \/
                      (f + 56 <= a < f + 64) \/ (f + 232 <= a < f + 248) \/ (as_errno B <= a < as_errno B + 4)).
  assert (FW : forall a, f <= a < f + AMF_ZEROED -> ~ dynf (a - f) -> ~ CW a).
  { intros a Ha Hd Hc. unfold CW in Hc. rewrite Ee in Hc. unfold dynf in *. nwlia. }
  unfold cfg_at. change (w64 LA_MWRITE) with (Z_to_bv 64 LA_MWRITE).
  assert (HI0 : NINVk mem md) by (apply NINV_init; exact Hpw).
  apply (nC_step EZ ssZ ssZ_st1 _ _ md nFP nZ_entry ltac:(vm_compute; reflexivity) HAE runZ1 ltac:(discriminate) HI0).
  intros ms1 mat1 HS1 HI1 HV1.
  change (ms_mem (mkst regs (Z_to_bv 64 LA_MWRITE) mem (seg_rom tfibsegs))) with mem in HV1.
  assert (U37 : U EZ (SOff 37 0) = wpos) by (apply (U_atom EZ 37); [exact E37 | lia]).
  assert (U38 : U EZ (SOff 38 0) = wbase) by (apply (U_atom EZ 38); [exact E38 | lia]).
  pose proof (st_ok_add_cond tfibsegs EZ ssZ_st1 _ BC_EQ (SOff 37 0) (SOff 38 0) HS1
    ltac:(rewrite branch_eq_U, U37, U38; apply Z.eqb_eq; exact Wpb)) as HS2.
  change (YP06.add_cond ssZ_st1 (mkAC BC_EQ (SOff 37 0) (SOff 38 0))) with ssZ_eq in HS2.
  apply (nC_step EZ ssZ_eq ssZ_st2 _ ms1 _ nFP HS2 ltac:(vm_compute; reflexivity) HAE runZ2 ltac:(discriminate) HI1).
  intros ms2 mat2 HS3 HI2 HV2.
  assert (Hpk : pos + k <= 4096) by lia.
  assert (UR : U EZ SROOM = 4096 - (pos + k)) by (apply vl_room; [exact E33' | lia]).
  assert (U12 : U EZ (SOff 12 0) = Z.of_nat (length ds)) by (apply (U_atom EZ 12); [rewrite E12, H12; reflexivity | lia]).
  assert (KEEP2 : forall ms3, (forall a, 0 <= a < 2 ^ 64 -> ~ CW a ->
      aview tfibsegs (w_H W) (ms_mem ms3) a = aview tfibsegs (w_H W) (ms_mem ms2) a) ->
      forall a, 0 <= a < 2 ^ 64 -> ~ CW a -> aview tfibsegs (w_H W) (ms_mem ms3) a = aview tfibsegs (w_H W) mem a).
  { intros ms3 H3 a Ha Hc. rewrite H3 by assumption. unfold CW in Hc.
    rewrite HV2 by (try exact Ha; intros Q; apply Hc; tauto). apply HV1; try exact Ha; intros Q; apply Hc; tauto. }
  assert (Hbz : azbytes tfibsegs (mrestrict (w_H W) mem) (amf_buf link_amf + pos) pb)
    by (rewrite Hpb0; intros i Hi; cbn in Hi; lia).
  assert (Hn1 : amf_n1 link_amf k pos = k) by (rewrite Hk0; unfold amf_n1; cbn [amf_size link_amf]; lia).
  destruct (Z_le_gt_dec (Z.of_nat (length ds)) (4096 - (pos + k))) as [Hfit | Hover].
  - (* +0x80 bgeu taken: the data fits *)
    pose proof (st_ok_add_cond tfibsegs EZ ssZ_st2 _ BC_GEU SROOM (SOff 12 0) HS3
      ltac:(rewrite branch_geu_U, UR, U12; apply negb_true_iff, Z.ltb_ge; lia)) as HS4.
    change (YP06.add_cond ssZ_st2 (mkAC BC_GEU SROOM (SOff 12 0))) with ssZ_n in HS4.
    apply (nC_step EZ ssZ_n ssZM1 _ ms2 _ nFP HS4 ltac:(vm_compute; reflexivity) HAE runZM1 ltac:(discriminate) HI2).
    intros ms3 mat3 HS5 HI3 HV3.
    pose proof (KEEP2 ms3 ltac:(intros a Ha Hc; unfold CW in Hc; apply HV3; try exact Ha; intros Q; apply Hc; tauto)) as KP.
    pose proof (mw_cval EZ ssZM1 ms3 (w_H W) 1 _ 0 0 4 (SOff 35 0) fl HS5 eq_refl eq_refl (DA 35%nat fl E35 ltac:(lia))
      ltac:(cbn; lia) ltac:(cbn; lia)) as VF.
    pose proof (mw_cval EZ ssZM1 ms3 (w_H W) 2 _ 0 32 8 (SOff 36 0) wend HS5 eq_refl eq_refl (DA 36%nat wend E36 ltac:(lia))
      ltac:(cbn; lia) ltac:(cbn; lia)) as VW1.
    pose proof (mw_cval EZ ssZM1 ms3 (w_H W) 2 _ 1 40 8 (SOff 37 0) wpos HS5 eq_refl eq_refl (DA 37%nat wpos E37 ltac:(lia))
      ltac:(cbn; lia) ltac:(cbn; lia)) as VW2.
    pose proof (mw_cval EZ ssZM1 ms3 (w_H W) 3 _ 0 56 8 (SOff 38 0) wbase HS5 eq_refl eq_refl (DA 38%nat wbase E38 ltac:(lia))
      ltac:(cbn; lia) ltac:(cbn; lia)) as VW3.
    pose proof (mw_cval EZ ssZM1 ms3 (w_H W) 4 _ 0 232 8 (SOff 33 0) (pos + k) HS5 eq_refl eq_refl (DA 33%nat _ E33' ltac:(lia))
      ltac:(cbn; lia) ltac:(cbn; lia)) as VP.
    pose proof (mw_cval EZ ssZM1 ms3 (w_H W) 4 _ 1 240 8 (SOff 34 0) (Z.max len (pos + k)) HS5 eq_refl eq_refl (DA 34%nat _ E34' ltac:(lia))
      ltac:(cbn; lia) ltac:(cbn; lia)) as VL.
    cbn [base_val YP09.r_base] in VF, VW1, VW2, VW3, VP, VL. rewrite E10 in VF, VW1, VW2, VW3, VP, VL.
    assert (Hat3 : amf_k tfibsegs link_amf (mrestrict (w_H W) (ms_mem ms3)) f 0).
    { apply (amf_at_rebuild (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms3)) f fl wend wpos wbase
        (pos + k) (Z.max len (pos + k)) (proj1 Hamk)).
      - intros a Ha Hd. apply mbyte_of_aview. apply KP; [nwlia | exact (FW a Ha Hd)].
      - exact Hfl. - exact VF.
      - destruct Wv as [(W1 & W3) | (W1 & W3)]; [left | right]; unfold AMF_BUF, AMF_BUFSIZ; lia.
      - exact VW1. - exact VW2. - exact VW3.
      - lia. - cbn [amf_size link_amf]. lia. - exact VP. - exact VL. }
    apply (nM EZ ssZM1 ms3 _ (SOff 12 0) (Z.of_nat (length ds)) fl wend wpos wbase HS5 eq_refl eq_refl
      ltac:(vm_compute; reflexivity) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
      ltac:(vm_compute; submem_tac) ltac:(vm_compute; reflexivity) ssD_Z1 HAE E33' E34').
    + cbn [sv_denot]. rewrite E12, H12, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + exact Hn1.
    + lia.
    + intros Hc. lia.
    + intros _. repeat split; lia.
    + exact HI3.
    + exact (proj1 Hat3).
    + exact VF. + exact VW1. + exact VW2. + exact VW3.
    + apply (mw_val_mem_xfer_av (w_H W) mem (ms_mem ms3)); [|exact D136].
      intros i Hi. apply KP; [nwlia|]. apply (FW (f + 136 + i)); [unfold AMF_ZEROED; cbn in Hi; lia | unfold dynf; cbn in Hi; lia].
    + rewrite Hpb0. intros i Hi. cbn in Hi. lia.
  - (* +0x80 bgeu not taken: ENOSPC, errno, F_ERR, the window emptied, n2 = size - pos *)
    pose proof (st_ok_add_cond_neg tfibsegs EZ ssZ_st2 _ BC_GEU SROOM (SOff 12 0) HS3
      ltac:(rewrite branch_geu_U, UR, U12; apply negb_false_iff, Z.ltb_lt; lia)) as HS4.
    rewrite ssZ_e_eq in HS4.
    apply (nC_step EZ ssZ_e ssZM2 _ ms2 _ nFP HS4 ltac:(vm_compute; reflexivity) HAE runZM2 ltac:(discriminate) HI2).
    intros ms3 mat3 HS5 HI3 HV3.
    pose proof (KEEP2 ms3 ltac:(intros a Ha Hc; unfold CW in Hc; apply HV3; try exact Ha; intros Q; apply Hc; tauto)) as KP.
    assert (D0z : sv_denot EZ (SLit 0) = Z_to_bv 64 0) by reflexivity.
    pose proof (mw_cval EZ ssZM2 ms3 (w_H W) 1 _ 0 0 4 (SAlu ALU_OR (SExt true 32 (SOff 35 0)) (SLit 32)) (AF_NORD + AF_ERR) HS5 eq_refl eq_refl
      (vl_flags EZ fl E35 Hfl) ltac:(cbn; unfold AF_NORD, AF_ERR; lia) ltac:(cbn; lia)) as VF.
    pose proof (mw_cval EZ ssZM2 ms3 (w_H W) 2 _ 1 32 8 (SLit 0) 0 HS5 eq_refl eq_refl D0z ltac:(cbn; lia) ltac:(cbn; lia)) as VW1.
    pose proof (mw_cval EZ ssZM2 ms3 (w_H W) 2 _ 0 40 8 (SLit 0) 0 HS5 eq_refl eq_refl D0z ltac:(cbn; lia) ltac:(cbn; lia)) as VW2.
    pose proof (mw_cval EZ ssZM2 ms3 (w_H W) 3 _ 0 56 8 (SLit 0) 0 HS5 eq_refl eq_refl D0z ltac:(cbn; lia) ltac:(cbn; lia)) as VW3.
    pose proof (mw_cval EZ ssZM2 ms3 (w_H W) 4 _ 0 232 8 (SOff 33 0) (pos + k) HS5 eq_refl eq_refl (DA 33%nat _ E33' ltac:(lia))
      ltac:(cbn; lia) ltac:(cbn; lia)) as VP.
    pose proof (mw_cval EZ ssZM2 ms3 (w_H W) 4 _ 1 240 8 (SOff 34 0) (Z.max len (pos + k)) HS5 eq_refl eq_refl (DA 34%nat _ E34' ltac:(lia))
      ltac:(cbn; lia) ltac:(cbn; lia)) as VL.
    cbn [base_val YP09.r_base] in VF, VW1, VW2, VW3, VP, VL. rewrite E10 in VF, VW1, VW2, VW3, VP, VL.
    assert (Hat3 : amf_k tfibsegs link_amf (mrestrict (w_H W) (ms_mem ms3)) f 0).
    { apply (amf_at_rebuild (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms3)) f (AF_NORD + AF_ERR) 0 0 0
        (pos + k) (Z.max len (pos + k)) (proj1 Hamk)).
      - intros a Ha Hd. apply mbyte_of_aview. apply KP; [nwlia | exact (FW a Ha Hd)].
      - right. reflexivity. - exact VF.
      - left. auto.
      - exact VW1. - exact VW2. - exact VW3.
      - lia. - cbn [amf_size link_amf]. lia. - exact VP. - exact VL. }
    apply (nM EZ ssZM2 ms3 _ SROOM (4096 - (pos + k)) (Z.lor fl AF_ERR) 0 0 0 HS5 eq_refl eq_refl
      ltac:(vm_compute; reflexivity) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
      ltac:(vm_compute; submem_tac) ltac:(vm_compute; reflexivity) ssD_Z2 HAE E33' E34').
    + rewrite denot_lit_U, UR. reflexivity.
    + exact Hn1.
    + lia.
    + intros _. auto.
    + intros Hc. lia.
    + exact HI3.
    + exact (proj1 Hat3).
    + rewrite nf_lor. exact VF. + exact VW1. + exact VW2. + exact VW3.
    + apply (mw_val_mem_xfer_av (w_H W) mem (ms_mem ms3)); [|exact D136].
      intros i Hi. apply KP; [nwlia|]. apply (FW (f + 136 + i)); [unfold AMF_ZEROED; cbn in Hi; lia | unfold dynf; cbn in Hi; lia].
    + rewrite Hpb0. intros i Hi. cbn in Hi. lia.
Qed.

(* ---- k > 0: the values the inner call leaves: atoms 33..38 of the walk, fixed in the entry environment ---- *)
Definition nkn1 : Z := amf_n1 link_amf k pos.
Definition nkfl1 : Z := if nkn1 <? k then Z.lor fl AF_ERR else fl.
Definition nkwe1 : Z := if nkn1 <? k then 0 else f + 1304.
Definition nkwb1 : Z := if nkn1 <? k then 0 else f + 280.
Definition nEK : env := Ereg regs [Z_to_bv 64 (f + 280 + k); Z_to_bv 64 (pos + nkn1); Z_to_bv 64 (Z.max len (pos + nkn1));
  Z_to_bv 64 nkfl1; Z_to_bv 64 nkwe1; Z_to_bv 64 nkwb1; Z_to_bv 64 nkwb1].

Lemma nEK_agree : env_agree 33 nE0 nEK.
Proof.
  split; [|reflexivity]. intros n Hn. unfold nE0, nEK, Ereg. cbn [ew].
  destruct (n <? 32)%nat eqn:Hc; [reflexivity|]. apply Nat.ltb_ge in Hc. replace n with 32%nat by lia. reflexivity.
Qed.

Lemma nkn1_facts : 0 <= nkn1 <= k /\ (nkn1 < k -> nkn1 = 4096 - pos) /\ (nkn1 = k -> pos + k <= 4096).
Proof. pose proof nf_cookie as (Hpl & Hls & _). unfold nkn1, amf_n1. cbn [amf_size link_amf]. lia. Qed.

(* ---- one phase, with the windows of the entry shape (stack frame, f->wpos) ---- *)
Lemma nA_gen : forall E ss ss' ms md' Q,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> windows (ss_mem ss) = [(Some 2%nat, -48, 0); (Some 10%nat, 40, 48)] ->
  env_agree 33 nE0 E -> NINVk (ms_mem ms) md' ->
  SRr tfibsegs W (mkCfg ms md')
    (fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md') mat1 md') /\
       st_ok tfibsegs E ss' (restrict (w_H W) ms1) /\
       frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
       frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1)) /\
       mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))) ->
  (forall ms1 mat1, st_ok tfibsegs E ss' (restrict (w_H W) ms1) ->
     NINVk (ms_mem ms1) (with_vm_backing (m_vm_lazy md') mat1 md') ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> ~ (f + 40 <= a < f + 48) ->
        aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) (ms_mem ms) a) ->
     SRr tfibsegs W (mkCfg ms1 (with_vm_backing (m_vm_lazy md') mat1 md')) Q) ->
  SRr tfibsegs W (mkCfg ms md') Q.
Proof.
  intros E ss ss' ms md' Q HS Hw HAE HI Hph Hk.
  destruct (nk_E E HAE) as (E2 & E10 & _).
  eapply SRr_bind; [exact Hph|].
  intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1 & HG1).
  assert (WIN : forall z, in_wrange E (ss_mem ss) z -> (spZ regs - 48 <= z < spZ regs) \/ (f + 40 <= z < f + 48)).
  { intros z Hz. destruct (mw_winA E (ss_mem ss) z Hw Hz) as [Hz'|Hz']; rewrite ?E2, ?E10 in Hz'; [left|right]; lia. }
  apply Hk; [exact HS1 | |].
  - apply (NINV_run B W K (spZ regs) f mem md (fun z => (spZ regs - 48 <= z < spZ regs) \/ (f + 40 <= z < f + 48))
      (ms_mem ms) md' (ms_mem ms1) mat1 HI).
    + intros y Hy. apply HF1. intros Hin. apply Hy. exact (WIN _ Hin).
    + intros y Hy. apply HFr1. intros Hin. apply Hy. exact (WIN _ Hin).
    + exact HG1.
    + intros z [Hz|Hz]; apply nf_safe; [left; nwlia | right; left; nwlia].
  - intros z Hz H1 H2. apply aview_eq_of. apply HFr1. rewrite unsigned_lit_small by lia. intros Hin. destruct (WIN _ Hin); lia.
Qed.

(* ---- the entry state (k > 0): the frame mwrite pushes, f->wpos, f->wbase, f->cookie ---- *)
Lemma nA_entry : 0 < k -> st_ok tfibsegs nEK ssA (restrict (w_H W) (mkst regs (Z_to_bv 64 LA_MWRITE) mem (seg_rom tfibsegs))).
Proof.
  intros Hkp.
  pose proof nf_blk as (B16 & B0 & B63 & Bs & Bam & Bp & _). pose proof nf_pre as (_ & _ & L3 & L4 & Hpw & _).
  pose proof (nf_win Hkp) as (Wend & Wpos & Wbase).
  pose proof Hamk as ((_ & _ & _ & Hst & _) & _).
  destruct Hst as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S152 & _).
  pose proof Hdyn as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D40 & D56 & _).
  assert (EK2 : bv_unsigned (ew nEK 2) = spZ regs) by (unfold nEK; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  assert (EK10 : bv_unsigned (ew nEK 10) = f) by (destruct (nk_E nEK nEK_agree) as (_ & E10 & _); exact E10).
  assert (EK32 : ew nEK 32 = Z_to_bv 64 (f + 280 + k)) by exact (ew_Ereg_extra regs _ 0).
  rewrite restrict_mkst_fx. unfold ssA. apply (entry_st_ok_full tfibsegs); fold nEK.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (region_ok_stack tfibsegs nEK _ 2 (spZ regs) (-48)); [exact EK2 | nwlia | nwlia |].
      intros a Ha. apply apresent_writable. apply Hpw. nwlia.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val R_fileA]. rewrite EK10.
      split; [lia|]. split; [nwlia|].
      split; [intros o Ho; exact (proj1 (proj2 (Bp (f + o) ltac:(nwlia))))|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * apply (chunk_ok_val tfibsegs nEK _ f 40 8 (SOff 32 0) (f + 280 + k));
          [cbn [sv_denot]; rewrite EK32, unsigned_lit_small, Z.add_0_r by nwlia; reflexivity | cbn; nwlia | cbn; lia |].
        rewrite <- Wpos. exact D40.
      * apply (chunk_ok_val tfibsegs nEK _ f 56 8 (SOff 10 280) (f + 280)); [cbn [sv_denot]; rewrite EK10; reflexivity | cbn; nwlia | cbn; lia |].
        rewrite <- Wbase. exact D56.
      * apply (chunk_ok_val tfibsegs nEK _ f 152 8 (SOff 10 232) (f + 232)); [cbn [sv_denot]; rewrite EK10; reflexivity | cbn; nwlia | cbn; lia |].
        exact S152.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val R_stkA R_fileA]. rewrite EK2, EK10.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; nwlia.
  - split; [cbn; exact I | split; exact I].
Qed.

(* ---- +0x4c jal 0x96cc0: the inner call (the no-AR k = 0 contract HK0n, one frame lower), then the state after it ---- *)
Lemma nB : forall ms md', 0 < k -> AMW_STK <= K ->
  st_ok tfibsegs nEK ssA_end (restrict (w_H W) ms) ->
  NINVk (ms_mem ms) md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> ~ (f + 40 <= a < f + 48) ->
     aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) mem a) ->
  SRr tfibsegs W (mkCfg ms md') nFP.
Proof.
  intros ms md' Hkp HKb HS HI HV.
  pose proof nf_blk as (B16 & B0 & B63 & Bs & Bam & Bp & Bra & Bhull). pose proof nf_fimg as Fi.
  pose proof nf_cookie as (Hpl & Hls & Hom). pose proof nf_pre as (_ & Hal & L3 & L4 & _ & Hgp & Htp).
  pose proof (nf_win Hkp) as (Wend & Wpos & Wbase). pose proof nf_errno as (Ee & Etp). pose proof nkn1_facts as (N1a & N1b & N1c).
  pose proof nf_fl as Hfl.
  destruct (nk_E nEK nEK_agree) as (E2 & E10 & E32 & _ & E3 & E4 & _ & _ & E4v).
  pose proof HI as (Hsbm & Hfr & Hpr & Hwp & Hhs).
  pose proof Hdyn as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & D0 & D136 & D32 & D40 & D56 & D232 & D240).
  pose proof Hbuf as (Hb0 & Hb1 & Hb2 & Hbw & Hbam & Hbra & Hbhull).
  pose proof HS as HS0.
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) nEK ssA_end ms HS eq_refl) as Hshape.
  change (ss_pc ssA_end) with LA_MWRITE in Hshape.
  assert (DA : forall n v, ew nEK n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot nEK (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
  assert (G1 : getr (ms_regs ms) 1 = Z_to_bv 64 0x96d10)
    by (rewrite (mw_reg_sv nEK ssA_end ms (w_H W) 1 (SLit 617744) HS ltac:(vm_compute; reflexivity)); reflexivity).
  assert (G2 : getr (ms_regs ms) 2 = Z_to_bv 64 (spZ regs - 48))
    by (rewrite (mw_reg_sv nEK ssA_end ms (w_H W) 2 (SOff 2 (-48)) HS ltac:(vm_compute; reflexivity)); cbn [sv_denot];
        rewrite E2; f_equal; lia).
  assert (G3 : getr (ms_regs ms) 3 = w64 (as_gp B))
    by (rewrite (mw_reg_atom nEK ssA_end ms (w_H W) 3 3 HS ltac:(vm_compute; reflexivity)), E3; exact Hgp).
  assert (G4 : getr (ms_regs ms) 4 = w64 (as_tp B))
    by (rewrite (mw_reg_atom nEK ssA_end ms (w_H W) 4 4 HS ltac:(vm_compute; reflexivity)), E4; exact Htp).
  assert (G10 : getr (ms_regs ms) 10 = w64 f)
    by (rewrite (mw_reg_atom nEK ssA_end ms (w_H W) 10 10 HS ltac:(vm_compute; reflexivity));
        unfold nEK; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (G11 : getr (ms_regs ms) 11 = w64 (f + 280))
    by (rewrite (mw_reg_sv nEK ssA_end ms (w_H W) 11 (SOff 10 280) HS ltac:(vm_compute; reflexivity)); cbn [sv_denot];
        rewrite E10; reflexivity).
  assert (G12 : getr (ms_regs ms) 12 = w64 (Z.of_nat (length pb))).
  { rewrite (mw_reg_sv nEK ssA_end ms (w_H W) 12 SKA2 HS ltac:(vm_compute; reflexivity)), denot_lit_U.
    rewrite (proj2 (vl_k nEK f k E10 E32 ltac:(lia) ltac:(lia) ltac:(nwlia))), Hpbk. reflexivity. }
  assert (Hsp : spZ (ms_regs ms) = spZ regs - 48) by (unfold spZ at 1; rewrite G2; apply unsigned_lit_small; nwlia).
  assert (Hra1 : raZ (ms_regs ms) = 0x96d10) by (unfold raZ; rewrite G1; apply unsigned_lit_small; lia).
  assert (TF1 : forall off (nb : nat) v, 0 <= off -> off + Z.of_nat nb <= 272 -> (off + Z.of_nat nb <= 40 \/ 48 <= off) ->
    val_mem tfibsegs (mrestrict (w_H W) mem) (f + off) nb v -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + off) nb v).
  { intros off nb v H0 H1 H2 Hv. apply (mw_val_mem_xfer_av (w_H W) mem (ms_mem ms)); [|exact Hv].
    intros i Hi. apply HV; nwlia. }
  pose proof (mw_cval nEK ssA_end ms (w_H W) 1 _ 0 40 8 (SOff 10 280) (f + 280) HS eq_refl eq_refl
    ltac:(cbn [sv_denot]; rewrite E10; reflexivity) ltac:(cbn; nwlia) ltac:(cbn; lia)) as V40.
  cbn [base_val YP09.r_base] in V40. rewrite E10 in V40.
  set (regs1 := ms_regs ms) in *. set (m1 := ms_mem ms) in *.
  rewrite Hshape. pose proof HK0n as K0. unfold amw_noar_at, cfg_at in K0.
  eapply SRr_bind.
  { apply (K0 W regs1 m1 md' f 0 fl om (f + 1304) (f + 280) (f + 280) pos len (f + 280) [] pb).
    - split; [rewrite G1; apply YK0s.ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity|].
      rewrite Hsp. split; [rewrite Zminus_mod, Hal; reflexivity|]. split; [nwlia|]. split; [nwlia|].
      split; [intros a Ha; apply Hwp; nwlia|]. split; [exact G3 | exact G4].
    - exact (nf_cells m1 md' HI).
    - exact G10.
    - exact G11.
    - exact G12.
    - split; [exact B0|]. split; [exact B63|]. split; [exact B16|].
      split; [intros a Ha; destruct (Bp a Ha) as (P & Wr & I); split; [exact (Hpr a P)|];
              split; [exact (mw_writable_grows (w_H W) mem m1 a (mw_apresent_restrict _ _ _ Hpr) Wr)|];
              split; [exact I | rewrite Hsp; nwlia]|].
      split; [exact Bam|].
      split; [apply (nf_ra_xfer m1 md' _ _ HI); [lia | nwlia | exact Bra]|].
      apply (nf_hull_xfer m1 md' _ _ HI); [lia | nwlia | nwlia | exact Bhull].
    - apply (amf_at_rebuild (mrestrict (w_H W) mem) (mrestrict (w_H W) m1) f fl (f + 1304) (f + 280) (f + 280) pos len (proj1 Hamk)).
      + intros a Ha Hd. apply mbyte_of_aview. unfold dynf in Hd. apply HV; nwlia.
      + exact Hfl.
      + apply TF1; [lia | cbn; lia | cbn; lia | exact D0].
      + right. unfold AMF_BUF, AMF_BUFSIZ. lia.
      + rewrite <- Wend. apply TF1; [lia | cbn; lia | cbn; lia | exact D32].
      + exact V40.
      + rewrite <- Wbase. apply TF1; [lia | cbn; lia | cbn; lia | exact D56].
      + lia.
      + cbn [amf_size link_amf]. lia.
      + apply TF1; [nwlia | cbn; nwlia | cbn; nwlia | exact D232].
      + apply TF1; [nwlia | cbn; nwlia | cbn; nwlia | exact D240].
    - lia.
    - unfold amf_dyn. split; [exact R1|]. split; [exact R2|]. split; [nwlia|]. split; [nwlia|]. split; [nwlia|].
      split; [exact R6|]. split; [exact R7|].
      split; [apply TF1; [lia | cbn; lia | cbn; lia | exact D0]|].
      split; [apply TF1; [lia | cbn; lia | cbn; lia | exact D136]|].
      split; [rewrite <- Wend; apply TF1; [lia | cbn; lia | cbn; lia | exact D32]|].
      split; [exact V40|].
      split; [rewrite <- Wbase; apply TF1; [lia | cbn; lia | cbn; lia | exact D56]|].
      split; [apply TF1; [nwlia | cbn; nwlia | cbn; nwlia | exact D232] | apply TF1; [nwlia | cbn; nwlia | cbn; nwlia | exact D240]].
    - intros i Hi. cbn in Hi. lia.
    - reflexivity.
    - split; [exact Hb0|]. split; [exact Hb1|]. split; [exact Hb2|].
      split; [intros a Ha; destruct (Hbw a Ha) as (Hw & Hs);
              split; [exact (mw_writable_grows (w_H W) mem m1 a (mw_apresent_restrict _ _ _ Hpr) Hw)|];
              rewrite Hsp; nwlia|].
      split; [exact Hbam|].
      split; [apply (nf_ra_xfer m1 md' _ _ HI); [nwlia | nwlia | exact Hbra]|].
      apply (nf_hull_xfer m1 md' _ _ HI); [nwlia | nwlia | nwlia | exact Hbhull].
    - exact (nf_pend m1 md' HI).
    - lia.
    - nwlia.
    - unfold amem_range. destruct Bam as [Q|Q]; [left | right]; nwlia.
    - apply (nf_ra_xfer m1 md' _ _ HI); [lia | nwlia |].
      apply (range_addressable_sub _ _ f AMF_BLOCK); [exact Bra | lia | nwlia].
    - intros Hn. apply (nf_hull_xfer m1 md' _ _ HI); [lia | exact Hn | nwlia |].
      apply (mw_hull_sub _ f AMF_BLOCK); [exact Bhull | lia | exact Hn | nwlia | lia].
    - intros a Ha. split; [nwlia|]. split; [nwlia|]. split; [rewrite Ee; nwlia|]. rewrite Hsp. nwlia. }
  intros W2 c2 _ (-> & regs2 & m2 & md2 & HP). cbv zeta in HP.
  destruct HP as (-> & HP2 & Hsbm2 & Hk2 & Hpend2 & _ & Heq2 & Hfr2 & Hhs2 & Hpr2 & Hwp2).
  assert (Hi0 : amf_n1 link_amf 0 pos = 0) by (unfold amf_n1; cbn [amf_size link_amf]; lia).
  assert (Hp0 : amw_pos1 link_amf 0 pos = pos) by (unfold amw_pos1; rewrite Hi0; lia).
  assert (Hn2i : amw_n2 link_amf 0 pos (Z.of_nat (length pb)) = nkn1)
    by (unfold amw_n2, nkn1, amf_n1; rewrite Hp0; cbn [amf_size link_amf]; lia).
  destruct (Heq2 Hi0) as (Ha2 & (fl' & we' & wp' & wb' & Hdyn2 & Hlt2 & Heq2') & Hbz2).
  rewrite Hp0, Hn2i in Hdyn2. rewrite Hn2i in Ha2, Hlt2, Heq2', Hbz2.
  assert (FV : fl' = nkfl1 /\ we' = nkwe1 /\ wp' = nkwb1 /\ wb' = nkwb1).
  { unfold nkfl1, nkwe1, nkwb1. destruct (Z.ltb_spec nkn1 k) as [Hl|Hg].
    - destruct (Hlt2 ltac:(lia)) as (A1 & A2 & A3 & A4). auto.
    - destruct (Heq2' ltac:(lia)) as (A1 & A2 & A3 & A4). auto. }
  destruct FV as (-> & -> & -> & ->).
  pose proof Hdyn2 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & P0 & P136 & P32 & P40 & P56 & P232 & P240).
  destruct Hk2 as (Hat2 & _). pose proof Hat2 as (_ & _ & _ & Hst2 & _).
  destruct Hst2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ssz & Sbuf & Smode).
  assert (PG2 : forall y, mrestrict (w_H W) m1 y <> None -> mrestrict (w_H W) m2 y <> None) by exact (mw_apresent_restrict _ _ _ Hpr2).
  assert (PR2 : forall a, f <= a < f + AMF_BLOCK -> apresent (w_H W) m2 a) by (intros a Ha; apply Hpr2, Hpr, (proj1 (Bp a Ha))).
  (* the stack frame mwrite pushed: outside the inner call's window *)
  assert (HR0 : region_ok tfibsegs nEK (mrestrict (w_H W) m1) R_stkC) by exact (mw_region_ok nEK ssA_end ms (w_H W) 0 R_stkC HS0 eq_refl).
  assert (KEPT0 : region_kept tfibsegs nEK (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) R_stkC).
  { apply (mw_region_kept nEK (w_H W) m1 m2 R_stkC); [|exact PG2].
    intros a Ha. cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi R_stkC] in Ha. rewrite E2 in Ha.
    apply Hfr2; [nwlia | rewrite Hsp; nwlia | nwlia | nwlia | rewrite Ee; nwlia]. }
  assert (HM0 : mem_ok tfibsegs nEK (mrestrict (w_H W) m1) [R_stkC]).
  { split; [vm_compute; reflexivity|]. split; [apply Forall_cons; [exact HR0 | apply Forall_nil] | split; exact I]. }
  pose proof (mem_ok_kept tfibsegs nEK (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) [R_stkC] HM0
    ltac:(vm_compute; reflexivity) ltac:(apply Forall_cons; [exact KEPT0 | apply Forall_nil])) as (_ & HR0' & _).
  assert (HM : mem_ok tfibsegs nEK (mrestrict (w_H W) m2) rsC).
  { split; [vm_compute; reflexivity|]. split.
    - unfold rsC. apply Forall_cons; [exact (Forall_inv HR0')|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
      + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val RF_fl]. rewrite E10.
        split; [lia|]. split; [nwlia|]. split; [intros o Ho; apply apresent_writable; apply PR2; nwlia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs nEK _ f 0 4 (SOff 35 0) nkfl1); [apply DA; [exact (ew_Ereg_extra regs _ 3) | lia] | cbn; lia | cbn; lia | exact P0].
      + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val RF_win]. rewrite E10.
        split; [lia|]. split; [nwlia|]. split; [intros o Ho; apply apresent_writable; apply PR2; nwlia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        * apply (chunk_ok_val tfibsegs nEK _ f 32 8 (SOff 36 0) nkwe1); [apply DA; [exact (ew_Ereg_extra regs _ 4) | lia] | cbn; lia | cbn; lia | exact P32].
        * apply (chunk_ok_val tfibsegs nEK _ f 40 8 (SOff 37 0) nkwb1); [apply DA; [exact (ew_Ereg_extra regs _ 5) | lia] | cbn; lia | cbn; lia | exact P40].
      + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val RF_wb]. rewrite E10.
        split; [lia|]. split; [nwlia|]. split; [intros o Ho; apply apresent_writable; apply PR2; nwlia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs nEK _ f 56 8 (SOff 38 0) nkwb1); [apply DA; [exact (ew_Ereg_extra regs _ 6) | lia] | cbn; lia | cbn; lia | exact P56].
      + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val RF_ck]. rewrite E10.
        split; [lia|]. split; [nwlia|]. split; [intros o Ho; apply apresent_writable; apply PR2; nwlia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
        * apply (chunk_ok_val tfibsegs nEK _ f 232 8 (SOff 33 0) (pos + nkn1));
            [apply DA; [exact (ew_Ereg_extra regs _ 1) | lia] | cbn; lia | cbn; lia | exact P232].
        * apply (chunk_ok_val tfibsegs nEK _ f 240 8 (SOff 34 0) (Z.max len (pos + nkn1)));
            [apply DA; [exact (ew_Ereg_extra regs _ 2) | lia] | cbn; lia | cbn; lia | exact P240].
        * apply (chunk_ok_val tfibsegs nEK _ f 248 8 (SLit 4096) 4096); [reflexivity | cbn; lia | cbn; lia | exact Ssz].
        * apply (chunk_ok_val tfibsegs nEK _ f 256 8 (SLit 0x62fee0) 0x62fee0); [reflexivity | cbn; lia | cbn; lia | exact Sbuf].
        * apply (chunk_ok_val tfibsegs nEK _ f 264 4 (SLit 119) 119); [reflexivity | cbn; lia | cbn; lia | exact Smode].
      + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val R_errno]. rewrite E4v.
        split; [lia|]. split; [lia|]. split; [intros o Ho; apply mw_errno_writable; lia | apply Forall_nil].
    - apply pairwise_disjoint_of_extents. unfold rsC, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val R_stkC RF_fl RF_win RF_wb RF_ck R_errno]. rewrite E2, E10, E4v.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; nwlia. }
  rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
  pose proof (st_ok_splice_havoc tfibsegs 39 nEK ssA_end regs1 regs2 (Z_to_bv 64 LA_MWRITE) 0x96d10
    (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) rsC [] CLOB HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
    (fun r Hr => regs_preserved_frame regs1 regs2 HP2 r Hr) (Forall_nil _) HM) as HSC.
  rewrite ssC_eq in HSC.
  unfold cfg_at. rewrite Hra1. change (w64 0x96d10) with (Z_to_bv 64 0x96d10).
  apply (nC (havoc nEK 39 (map (getr regs2) CLOB)) (mkst regs2 (Z_to_bv 64 0x96d10) m2 (seg_rom tfibsegs)) md2 nkfl1 nkwe1 nkwb1 nkwb1 Hkp).
  - rewrite restrict_mkst_fx. exact HSC.
  - exact (env_agree_trans 33 nE0 nEK _ nEK_agree (env_agree_le 39 33 _ _ ltac:(lia) (env_agree_havoc nEK 39 _))).
  - rewrite ew_havoc_old by lia. exact (ew_Ereg_extra regs _ 1).
  - rewrite ew_havoc_old by lia. exact (ew_Ereg_extra regs _ 2).
  - rewrite ew_havoc_old by lia. exact (ew_Ereg_extra regs _ 3).
  - rewrite ew_havoc_old by lia. exact (ew_Ereg_extra regs _ 4).
  - rewrite ew_havoc_old by lia. exact (ew_Ereg_extra regs _ 5).
  - rewrite ew_havoc_old by lia. exact (ew_Ereg_extra regs _ 6).
  - change 43%nat with (39 + 4)%nat.
    rewrite (ew_havoc_new nEK 39 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (rewrite length_map; unfold CLOB; cbn; lia).
    exact Ha2.
  - intros Hl. unfold nkfl1, nkwe1, nkwb1. replace (nkn1 <? k) with true by (symmetry; apply Z.ltb_lt; exact Hl). auto.
  - intros He. unfold nkfl1, nkwe1, nkwb1. replace (nkn1 <? k) with false by (symmetry; apply Z.ltb_ge; unfold nkn1; lia). auto.
  - apply (NINV_call B W K (spZ regs) f mem md
      (fun a => (spZ regs - 48 - AMW0_STK <= a < spZ regs - 48) \/ (f <= a < f + AMF_ZEROED) \/
                (amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf) \/ (as_errno B <= a < as_errno B + 4))
      m1 md' m2 md2 HI Hsbm2).
    + intros a Ha Hn. apply Hfr2; [exact Ha | rewrite Hsp; intros Q; apply Hn; left; exact Q
        | intros Q; apply Hn; right; left; exact Q | intros Q; apply Hn; right; right; left; exact Q
        | intros Q; apply Hn; right; right; right; exact Q].
    + exact Hpr2.
    + intros a Hk. unfold nchg. unfold AMW0_STK in Hk. unfold AMW_STK in HKb. lia.
    + exact Hhs2.
  - exact Hat2.
  - exact P136.
  - exact Hbz2.
Qed.

(* ---- the walk at k > 0: +0x00 to the inner call, then nB ---- *)
Lemma nA : 0 < k -> AMW_STK <= K -> SRr tfibsegs W (cfg_at tfibsegs LA_MWRITE regs mem md) nFP.
Proof.
  intros Hkp HKb.
  pose proof nf_pre as (_ & _ & L3 & L4 & Hpw & _). pose proof nf_blk as (B16 & B0 & B63 & Bs & _).
  destruct (nk_E nEK nEK_agree) as (E2 & E10 & E32 & _).
  unfold cfg_at. change (w64 LA_MWRITE) with (Z_to_bv 64 LA_MWRITE).
  assert (HI0 : NINVk mem md) by (apply NINV_init; exact Hpw).
  apply (nA_gen nEK ssA ssA_st1 _ md nFP (nA_entry Hkp) ltac:(vm_compute; reflexivity) nEK_agree HI0
           (mw_phase W nEK ssA ssA_st1 _ _ md (nA_entry Hkp) runA1 ltac:(discriminate))).
  intros ms1 mat1 HS1 HI1 HV1.
  assert (U32 : U nEK (SOff 32 0) = f + 280 + k) by (apply (U_atom nEK 32); [exact E32 | nwlia]).
  assert (U10 : U nEK (SOff 10 280) = f + 280) by (rewrite U_SOff, E10; apply (zc_eq _ 0); nwlia).
  pose proof (st_ok_add_cond_neg tfibsegs nEK ssA_st1 _ BC_EQ (SOff 32 0) (SOff 10 280) HS1
    ltac:(rewrite branch_eq_U, U32, U10; apply Z.eqb_neq; lia)) as HS2.
  rewrite ssA1_eq in HS2.
  apply (nA_gen nEK ssA1 ssA_end _ _ nFP HS2 ltac:(vm_compute; reflexivity) nEK_agree HI1
           (mw_phase_to W nEK LA_MWRITE ssA1 ssA_end _ _ _ HS2 runA2 ltac:(discriminate))).
  intros ms2 mat2 HS3 HI2 HV2.
  apply (nB ms2 _ Hkp HKb HS3 HI2). intros a Ha H1 H2. rewrite HV2 by assumption. exact (HV1 a Ha H1 H2).
Qed.

End NK.

(* ==========================================================================
   6. The theorems
   ========================================================================== *)

Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : PcapSyms B.
Hypothesis AMEMCPY0 : aintrin_noar_realizes tfibsegs B OCpy icpt_rodata ESTACK (pc_wrap_memcpy (as_code B)).

(* the k = 0 contract (the one the inner call uses), at window 48 + ESTACK *)
Theorem link_amwrite_k0_noar : amw_noar_at B AMW0_STK 0 LA_MWRITE.
Proof.
  intros W regs mem md f k fl om wend wpos wbase pos len x pb ds HPRE HCELL H10 H11 H12 Hblkn Hamk Hk0 Hdyn Hpend Hpbk Hbuf
    Hds Hx0 Hxn Hxam Hxra Hxhull Hxdisj.
  assert (Hkz : k = 0) by (destruct Hamk as (_ & [(Hk & _) | (Hk & _)]); lia).
  assert (HKw : AMW0_STK <= AMW0_STK) by lia.
  assert (Hkmax : k <= AMF_BUFSIZ) by (unfold AMF_BUFSIZ; lia).
  eapply SRr_bind; [eapply (nZ B TB AMEMCPY0); eassumption|].
  intros W' c' _ (-> & regs' & mem' & md' & Hc & HP' & Hsbm & HPF & Hfr & Hhs & Hpr & Hwp).
  unfold nPF in HPF. cbv zeta in HPF. destruct HPF as (Hk' & Hpend' & Hlt & Heq).
  apply SRr_ret. split; [reflexivity|]. exists regs', mem', md'. cbv zeta.
  split; [exact Hc|]. split; [exact HP'|]. split; [exact Hsbm|]. split; [exact Hk'|].
  split; [exact Hpend'|]. split; [exact Hlt|]. split; [exact Heq|]. split; [|split; [exact Hhs | split; [exact Hpr | exact Hwp]]].
  intros a Ha H1 H2 H3 H4. apply Hfr; [exact Ha|]. unfold nchg. tauto.
Qed.

(* the general contract, at window 96 + ESTACK and up to 1024 pending bytes *)
Theorem link_amwrite_noar_gen : amw_noar_at B AMW_STK AMF_BUFSIZ LA_MWRITE.
Proof.
  intros W regs mem md f k fl om wend wpos wbase pos len x pb ds HPRE HCELL H10 H11 H12 Hblkn Hamk Hkmax Hdyn Hpend Hpbk Hbuf
    Hds Hx0 Hxn Hxam Hxra Hxhull Hxdisj.
  assert (HKw : AMW0_STK <= AMW_STK) by (unfold AMW0_STK, AMW_STK; lia).
  assert (HKb : AMW_STK <= AMW_STK) by lia.
  eapply SRr_bind.
  { destruct (Z.eq_dec k 0) as [Hk0 | Hk0].
    - eapply (nZ B TB AMEMCPY0); eassumption.
    - assert (Hkp : 0 < k) by (destruct Hamk as (_ & [(Hk & _) | (Hk & _)]); lia).
      eapply (nA B TB AMEMCPY0 (link_amwrite_k0_noar)); eassumption. }
  intros W' c' _ (-> & regs' & mem' & md' & Hc & HP' & Hsbm & HPF & Hfr & Hhs & Hpr & Hwp).
  unfold nPF in HPF. cbv zeta in HPF. destruct HPF as (Hk' & Hpend' & Hlt & Heq).
  apply SRr_ret. split; [reflexivity|]. exists regs', mem', md'. cbv zeta.
  split; [exact Hc|]. split; [exact HP'|]. split; [exact Hsbm|]. split; [exact Hk'|].
  split; [exact Hpend'|]. split; [exact Hlt|]. split; [exact Heq|]. split; [|split; [exact Hhs | split; [exact Hpr | exact Hwp]]].
  intros a Ha H1 H2 H3 H4. apply Hfr; [exact Ha|]. unfold nchg. tauto.
Qed.

(* the last flush f->write(f, 0, 0) at process exit: the general contract at x = 0, no data *)
Theorem link_amwrite_flush_noar : amwrite_mf_flush_noar_realizes tfibsegs B link_amf icpt_rodata LA_MWRITE.
Proof.
  intros W regs mem md f k fl om wend wpos wbase pos len pb HPRE HCELL H10 H11 H12 Hblkn Hamk Hdyn Hpend Hpbk Hbuf.
  assert (Hkmax : k <= AMF_BUFSIZ) by (destruct Hamk as (_ & [(-> & _) | (Hk & _)]); unfold AMF_BUFSIZ in *; lia).
  assert (Hpl : 0 <= pos <= len /\ len <= 4096)
    by (destruct Hdyn as (_ & _ & _ & _ & _ & H6 & H7 & _); cbn [amf_size link_amf] in H7; lia).
  eapply SRr_bind.
  { apply (link_amwrite_noar_gen W regs mem md f k fl om wend wpos wbase pos len 0 pb [] HPRE HCELL H10 H11 H12 Hblkn Hamk
             Hkmax Hdyn Hpend Hpbk Hbuf).
    - intros i Hi. cbn in Hi. lia.
    - lia.
    - cbn. lia.
    - unfold amem_range. left. cbn. unfold kLowMemEnd. lia.
    - apply range_addressable_nil. cbn. lia.
    - intros Hc. cbn in Hc. lia.
    - intros a Ha. cbn in Ha. lia. }
  intros W' c' _ (-> & regs' & mem' & md' & HP). apply SRr_ret. split; [reflexivity|]. exists regs', mem', md'.
  cbv zeta in HP |- *. destruct HP as (Hc & HP' & Hsbm & Hk' & Hpend' & Hlt & Heq & Hfr & Hhs & Hpr & Hwp).
  change (Z.of_nat (length (@nil Z))) with 0 in Hlt, Heq.
  split; [exact Hc|]. split; [exact HP'|]. split; [exact Hsbm|].
  destruct (Z_lt_ge_dec (amf_n1 link_amf k pos) k) as [Hl | Hg].
  - destruct (Hlt Hl) as (R0 & D & Z0).
    split; [exact R0|]. split; [exact Hk'|]. split; [exact Hpend'|]. split; [exact Z0|].
    split; [intros _; exact D|]. split; [intros He; lia|]. split; [exact Hfr|]. split; [exact Hhs|]. split; [exact Hpr | exact Hwp].
  - assert (He : amf_n1 link_amf k pos = k) by (unfold amf_n1 in *; lia).
    assert (N2 : amw_n2 link_amf k pos 0 = 0)
      by (unfold amw_n2, amw_pos1; rewrite He; unfold amf_n1 in He; cbn [amf_size link_amf] in *; lia).
    assert (P1 : amw_pos1 link_amf k pos = pos + k) by (unfold amw_pos1; rewrite He; reflexivity).
    destruct (Heq He) as (R0 & (fl' & we' & wp' & wb' & D & _ & Hn) & Z0).
    rewrite N2 in R0, D, Hn, Z0. rewrite P1, Z.add_0_r in D.
    destruct (Hn eq_refl) as (-> & -> & -> & ->).
    cbn [firstn app] in Z0. rewrite app_nil_r in Z0.
    split; [exact R0|]. split; [exact Hk'|]. split; [exact Hpend'|].
    split; [rewrite He, firstn_all2 by lia; exact Z0|].
    split; [intros Hlk; lia|]. split; [intros _; exact D|]. split; [exact Hfr|]. split; [exact Hhs|]. split; [exact Hpr | exact Hwp].
Qed.

End T.

About link_amwrite_flush_noar.
Print Assumptions link_amwrite_flush_noar.
