(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE23.v, with its module paths changed, names TfibSyms -> BoxregSyms and its addresses moved to libreac/fuzz_boxreg's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/AE23.v, with its module paths changed; 372 of its 416 lines of code are new or changed and 1631 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/LinkExitFile.v, with its module paths and module names changed; 217 of its 261 lines of code are new or changed and 372 lines of the source are left out. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m YA0e.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE2y AsanNoAR.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AE2p AE3i AE3h AE3m AE23.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AD2j AD2i AD1t AD20 AD1v AD2h AD2f AD1u AD1w.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AD2l.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AD1y AD1k.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFileSink AMemFile LinkExitFile LinkDrvExitF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkRwDefs LinkRwRewind.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkRwExitDefs LinkRwExitOk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* exf_loop_pend_tfa (LinkDrvExitF.v): __stdio_exit's loop body on link's memory FILE when its write window
   holds bytes. The run is LinkExitFile.v's: xf_head to the call of f->write = mwrite 0x96cc0 with a0 = f and
   a1 = a2 = 0, then mwrite's flush, then xf_tail from the return 0x969e8 to 0x96890 with s0 = 0. The flush is
   the no-AR contract (lib/A/Rt/LinkRwExitOk.v amwrite_mf_flush_noar_ok, B = PcapB),
   whose premises are read from exf_mid and its exf_noar part. Its post keeps every byte outside the stack
   window below sp, the FILE's first 272 bytes, g_said and errno, which is how exf_mid is carried across.
   A window that holds nothing (the FILE's window words all 0, or wpos = wbase) takes LinkDrvExitF.v's
   exf_loop_empty instead. *)

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.

(* the cells of exf_consts are image bytes, apart from g_said and errno *)
Definition fp_cell_ok (a n : Z) : bool :=
  (0x10000 <=? a) && (a + n <=? 0x654000) && ((a + n <=? 0x62fee0) || (0x630ee0 <=? a)) &&
  ((a + n <=? 0x631b6c) || (0x631b70 <=? a)).
Lemma fp_cells_chk : forallb (fun c => fp_cell_ok (fst (fst c)) (Z.of_N (snd (fst c)))) exf_consts = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fp_cells_kept : forall (H : word -> bool) (m m' : word -> option byte),
(forall a, 0x10000 <= a < 0x654000 -> ~ (0x62fee0 <= a < 0x630ee0) -> ~ (0x631b6c <= a < 0x631b70) ->
   aview tfibsegs H m' a = aview tfibsegs H m a) ->
cells_are exf_consts (mrestrict H m) -> cells_are exf_consts (mrestrict H m').
Proof.
intros H m m' Hfr HC. unfold cells_are in *. rewrite Forall_forall in HC |- *.
intros [[a n] v] Hin. specialize (HC _ Hin). cbv beta iota in HC |- *.
pose proof (proj1 (forallb_forall _ _) fp_cells_chk _ Hin) as Cc. cbn [fst snd] in Cc. unfold fp_cell_ok in Cc.
apply andb_prop in Cc as [Cc C4]. apply andb_prop in Cc as [Cc C3]. apply andb_prop in Cc as [C1 C2].
apply Z.leb_le in C1. apply Z.leb_le in C2.
apply (val_mem_kept H H m m'); [|exact HC].
intros kk Hk. rewrite N_nat_Z in Hk. apply Hfr; [lia | |].
- apply orb_prop in C3 as [C3|C3]; apply Z.leb_le in C3; lia.
- apply orb_prop in C4 as [C4|C4]; apply Z.leb_le in C4; lia.
Qed.

(* the four ranges the flush may change (AMW_STK = 4192 below sp = usp - 80, the FILE's first AMF_ZEROED = 272
   bytes, g_said, errno), against the shadow of g_said and of the FILE's block *)
Lemma fp_said_shadow_off : forall (usp f s : Z),
2 ^ 46 <= usp -> amem_range f AMF_BLOCK -> 0 <= f ->
shadow_addr 0x62fee0 / 8 * 8 <= s < shadow_addr (0x62fee0 + 4096 - 1) / 8 * 8 + 8 ->
0 <= s < 2 ^ 64 /\ ~ (usp - 80 - 4192 <= s < usp - 80) /\ ~ (f <= s < f + 272) /\
~ (0x62fee0 <= s < 0x62fee0 + 4096) /\ ~ (0x631b6c <= s < 0x631b6c + 4).
Proof.
intros usp f s Hu Hr Hf Hs. unfold shadow_addr, SHADOW_OFF in Hs.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, AMF_BLOCK in Hr. lia.
Qed.

Lemma fp_block_shadow_off : forall (usp f x : Z),
2 ^ 46 <= usp -> amem_range f AMF_BLOCK -> 0 <= f -> f <= x < f + AMF_BLOCK ->
0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64 /\ ~ (usp - 80 - 4192 <= shadow_of_addr SHADOW_OFF x < usp - 80) /\
~ (f <= shadow_of_addr SHADOW_OFF x < f + 272) /\
~ (0x62fee0 <= shadow_of_addr SHADOW_OFF x < 0x62fee0 + 4096) /\
~ (0x631b6c <= shadow_of_addr SHADOW_OFF x < 0x631b6c + 4).
Proof.
intros usp f x Hu Hr Hf Hx. unfold shadow_of_addr, SHADOW_OFF.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, AMF_BLOCK in Hr. unfold AMF_BLOCK in Hx. lia.
Qed.

Lemma fp_block_hull_off : forall (usp f s : Z),
2 ^ 46 <= usp -> amem_range f AMF_BLOCK -> 0 <= f ->
shadow_addr f / 8 * 8 <= s < shadow_addr (f + AMF_BLOCK - 1) / 8 * 8 + 8 ->
0 <= s < 2 ^ 64 /\ ~ (usp - 80 - 4192 <= s < usp - 80) /\ ~ (f <= s < f + 272) /\
~ (0x62fee0 <= s < 0x62fee0 + 4096) /\ ~ (0x631b6c <= s < 0x631b6c + 4).
Proof.
intros usp f s Hu Hr Hf Hs. unfold shadow_addr, SHADOW_OFF, AMF_BLOCK in Hs.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, AMF_BLOCK in Hr. lia.
Qed.

Section t.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.

Theorem exf_loop_pend_ok : exf_loop_pend_tfa PcapB xst.
Proof.
intros W regs mem md usp code f k fs tid cval sew wpos0 wbase0 MID G8 _ _ _.
pose proof MID as (Msp & M16 & Musp & Mgp & Mtp & Mtpx & Mpres & Mcode & Mc02 & Mra & Mra2 &
  Mcells & Mtid & Mtidr & Mgot & Mcan & Mcanr & Msew1 & Msew2 & Msewr & Mso & Mfds & Mfs & Mgi & Mf4 & Mf16 & Mfh &
  Mnoar).
pose proof Mnoar as (Nicpt & Nsra & Nshull & Nby & Nrange & Nbelow & Nfra & Nfhull).
pose proof Musp as [Ulo Uhi]. unfold sp_window_lo, sp_window_hi in Ulo, Uhi.
assert (KS : AMW_STK = 4192 /\ ESTACK = 4096 /\ AMF_BLOCK = 1304 /\ AMF_ZEROED = 272 /\ AMF_BUF = 280 /\
  AMF_BUFSIZ = 1024 /\ as_errno PcapB = 0x631b6c) by (rewrite (ts_errno PcapB PcapB_syms); repeat split; reflexivity).
destruct KS as (KA & KE & KB & KZ & KBF & KBS & KERR).
(* the FILE at f, from the GI conjunct *)
pose proof Mgi as Hgi.
destruct Hgi as [(_ & Hnil) | (f' & Hheads & Hl & Hat)]; [discriminate Hnil|].
injection Hl as Hff. subst f'.
pose proof Hat as (_ & _ & _ & _ & Hfl & Hom & Hwin & Hck).
pose proof (amemfile_close_reads tfibsegs link_amf _ f Hat) as (V140 & V72 & V8 & V16 & V112).
destruct Hwin as (_ & _ & Hw).
destruct Hw as [(W32 & W40 & W56) | (kk & Hkk & W32 & W40 & W56)].
{ (* the window words are all 0: nothing pending *)
  exact (exf_loop_empty PcapB xst W regs mem md usp code f k fs tid cval sew 0 0 MID G8 W40 W56 eq_refl
    ltac:(lia) ltac:(lia)). }
destruct (Z.eq_dec kk 0) as [Hk0 | Hkn].
{ (* wpos = wbase: nothing pending *)
  subst kk. rewrite Z.add_0_r in W40.
  exact (exf_loop_empty PcapB xst W regs mem md usp code f k fs tid cval sew (f + AMF_BUF) (f + AMF_BUF) MID G8
    W40 W56 eq_refl ltac:(unfold AMF_BUF, AMF_BLOCK in *; lia) ltac:(unfold AMF_BUF, AMF_BLOCK in *; lia)). }
(* kk bytes pending: f->write (f, 0, 0) is mwrite's flush *)
assert (Rk : 0 < kk <= AMF_BUFSIZ) by lia.
assert (Rp : 0 <= f + AMF_BUF + kk < 2 ^ 64) by (unfold AMF_BUF, AMF_BUFSIZ, AMF_BLOCK in *; lia).
assert (Rb : 0 <= f + AMF_BUF < 2 ^ 64) by (unfold AMF_BUF, AMF_BLOCK in *; lia).
assert (Rw : 0 <= f + AMF_BUF + AMF_BUFSIZ < 2 ^ 64) by (unfold AMF_BUF, AMF_BUFSIZ, AMF_BLOCK in *; lia).
assert (FL : exists fl, 0 <= fl < 2 ^ 32 /\ val_mem tfibsegs (mrestrict (w_H W) mem) (f + 0) 4 fl).
{ destruct Hfl as [Hx|Hx]; eexists; (split; [|exact Hx]); unfold AF_NORD, AF_ERR; lia. }
assert (OM : exists om, 0 <= om < 2 ^ 32 /\ val_mem tfibsegs (mrestrict (w_H W) mem) (f + 136) 4 om).
{ destruct Hom as [Hx|Hx]; eexists; (split; [|exact Hx]); unfold AU32M1; lia. }
destruct FL as (fl & Rfl & Vfl). destruct OM as (om & Rom & Vom).
destruct Hck as (pos & len & Hpl & Hlen & Vpos & Vlen).
eapply SRr_bind; [exact (xf_head W regs mem md f (f + AMF_BUF + kk) (f + AMF_BUF) G8 Mf4 Mfh Mf16 W40 W56 V72 V140
  Rp Rb)|].
cbv beta. intros W1 c1 _ (-> & regs1 & md1 & Hsb1 & HP1 & [(Heq & _) | (_ & -> & R1 & R10 & R11 & R12)]);
  [exfalso; lia|].
assert (SP1 : spZ regs1 = usp - 80)
  by (unfold spZ; rewrite (ap_lit regs regs1 2%bv 2 HP1 ltac:(unfold acallee_saved; lia) eq_refl); exact Msp).
assert (P1 : aecall_pre_noar tfibsegs PcapB AMW_STK W regs1 mem).
{ split; [rewrite R1; unfold w64; apply ret_ok_lit; [unfold A_SX_RET; lia | reflexivity]|].
  rewrite SP1. split; [lia|]. split; [unfold kHighMemBeg; lia|]. split; [lia|].
  split; [intros a Ha; apply Mpres; lia|].
  split; [rewrite (ap_lit regs regs1 3%bv 3 HP1 ltac:(unfold acallee_saved; lia) eq_refl); exact Mgp|].
  rewrite (ap_lit regs regs1 4%bv 4 HP1 ltac:(unfold acallee_saved; lia) eq_refl); exact Mtp. }
assert (PB : amf_block_noar tfibsegs W regs1 mem AMW_STK f).
{ unfold amf_block_noar. rewrite SP1. split; [lia|]. split; [lia|]. split; [exact Mf16|].
  split; [|split; [exact Nrange | split; [exact Nfra | exact Nfhull]]].
  intros a Ha. destruct (Nby a Ha) as [Hp Hni].
  split; [exact Hp|]. split; [exact (AE2y.apresent_writable _ _ _ Hp)|]. split; [exact Hni|]. lia. }
assert (Hwk : amf_win tfibsegs (mrestrict (w_H W) mem) f kk)
  by (right; split; [lia|]; split; [exact W32|]; split; [exact W40 | exact W56]).
assert (Hk : amf_k tfibsegs link_amf (mrestrict (w_H W) mem) f kk) by (split; [exact Hat | exact Hwk]).
assert (Hdyn : amf_dyn tfibsegs link_amf (mrestrict (w_H W) mem) f fl om (f + AMF_BUF + AMF_BUFSIZ)
  (f + AMF_BUF + kk) (f + AMF_BUF) pos len).
{ unfold amf_dyn. split; [exact Rfl|]. split; [exact Rom|]. split; [exact Rw|]. split; [exact Rp|].
  split; [exact Rb|]. split; [exact Hpl|]. split; [exact Hlen|].
  split; [exact Vfl|]. split; [exact Vom|]. split; [exact W32|]. split; [exact W40|]. split; [exact W56|].
  split; [exact Vpos | exact Vlen]. }
set (pbf := fun i : nat => match aview tfibsegs (w_H W) mem (f + AMF_BUF + Z.of_nat i) with
                           | Some v => v | None => 0 end).
set (pb := map pbf (seq 0 (Z.to_nat kk))).
assert (Hlenpb : Z.of_nat (length pb) = kk) by (unfold pb; rewrite length_map, length_seq; lia).
assert (Hpend : amf_pend tfibsegs (mrestrict (w_H W) mem) f pb).
{ unfold amf_pend, azbytes. intros i Hi.
  assert (Hik : (i < Z.to_nat kk)%nat) by (unfold pb in Hi; rewrite length_map, length_seq in Hi; exact Hi).
  change (amf_rd tfibsegs (mrestrict (w_H W) mem) (f + AMF_BUF + Z.of_nat i))
    with (aview tfibsegs (w_H W) mem (f + AMF_BUF + Z.of_nat i)).
  unfold pb. erewrite nth_indep with (d' := pbf 0%nat) by (rewrite length_map, length_seq; exact Hik).
  rewrite map_nth, seq_nth by exact Hik. unfold pbf. cbn [Nat.add].
  assert (Hp : apresent (w_H W) mem (f + AMF_BUF + Z.of_nat i))
    by (apply (proj1 (Nby (f + AMF_BUF + Z.of_nat i) ltac:(unfold AMF_BUF, AMF_BUFSIZ, AMF_BLOCK in *; lia)))).
  pose proof (aview_some_of_apresent (w_H W) mem _ Hp) as Hs.
  destruct (aview tfibsegs (w_H W) mem (f + AMF_BUF + Z.of_nat i)) as [v|]; [reflexivity | exfalso; exact (Hs eq_refl)]. }
assert (Hbuf : amf_buf_ok_noar tfibsegs link_amf AMW_STK W regs1 mem).
{ unfold amf_buf_ok_noar. cbn [amf_buf amf_size link_amf]. rewrite SP1.
  split; [lia|]. split; [lia|]. split; [lia|]. split.
  - intros a Ha. split; [exact (xf_said_writable _ a Ha) | lia].
  - split; [unfold amem_range, kLowMemEnd; lia|]. split; [exact Nsra | exact Nshull]. }
eapply SRr_bind; [exact (amwrite_mf_flush_noar_ok W regs1 mem md1 f kk fl om (f + AMF_BUF + AMF_BUFSIZ)
  (f + AMF_BUF + kk) (f + AMF_BUF) pos len pb P1 Nicpt R10 R11 R12 PB Hk Hdyn Hpend Hlenpb Hbuf)|].
intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hpost). cbv zeta in Hpost.
destruct Hpost as (-> & HP2 & Hsb2 & _ & Hk2 & _ & _ & _ & _ & Hfr2 & _ & Hpm2 & _).
rewrite SP1, KA, KZ, KERR in Hfr2. cbn [amf_buf amf_size link_amf] in Hfr2.
assert (RA1 : raZ regs1 = A_SX_RET)
  by (unfold raZ; rewrite R1; unfold w64; apply unsigned_lit_small; unfold A_SX_RET; lia).
rewrite RA1.
assert (G8_2 : getr regs2 8%bv = w64 f)
  by (rewrite (ap_lit regs1 regs2 8%bv 8 HP2 ltac:(unfold acallee_saved; lia) eq_refl),
        (ap_lit regs regs1 8%bv 8 HP1 ltac:(unfold acallee_saved; lia) eq_refl); exact G8).
pose proof (amemfile_close_reads tfibsegs link_amf _ f (proj1 Hk2)) as (_ & _ & V8' & V16' & V112').
eapply SRr_bind; [exact (xf_tail W regs2 mem2 md2 f G8_2 Mf4 Mfh Mf16 V8' V16' V112')|].
cbv beta. intros W3 c3 _ (-> & regs3 & md3 & -> & Hsb3 & R8 & HP3).
assert (SB : same_but_materialized md md3)
  by exact (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ Hsb1 Hsb2) Hsb3).
assert (KEEP : forall (r : bv 5) (z : Z), acallee_saved z -> z <> 8 -> bv_unsigned r = z ->
  getr regs3 r = getr regs r).
{ intros r z Hz H8 Hr. subst z.
  pose proof (HP3 (bv_unsigned r) Hz H8) as X3. pose proof (HP2 (bv_unsigned r) Hz) as X2.
  pose proof (HP1 (bv_unsigned r) Hz) as X1.
  rewrite !Z_to_bv_bv_unsigned in X3, X2, X1. rewrite X3, X2. exact X1. }
(* the bytes the flush keeps *)
assert (IMGK : forall a, 0x10000 <= a < 0x654000 -> ~ (0x62fee0 <= a < 0x630ee0) -> ~ (0x631b6c <= a < 0x631b70) ->
  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem a).
{ intros a Ha H1 H2. apply Hfr2; [lia | lia | | lia | lia].
  intros Hb. apply (proj2 (Nby a ltac:(rewrite KB; lia))). apply AD1y.in_img_hull. unfold pcap_img_end, YImgTop.IMG_TOP. lia. }
assert (STKK : forall a, usp - 80 <= a < usp -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem a)
  by (intros a Ha; apply Hfr2; lia).
assert (Hu46 : 2 ^ 46 <= usp) by lia.
apply SRr_ret. split; [reflexivity|]. exists regs3, mem2, md3.
split; [reflexivity|]. split; [exact R8|].
unfold exf_mid.
split; [unfold spZ; rewrite (KEEP 2%bv 2 ltac:(unfold acallee_saved; lia) ltac:(lia) eq_refl); exact Msp|].
split; [exact M16|]. split; [exact Musp|].
split; [rewrite (KEEP 3%bv 3 ltac:(unfold acallee_saved; lia) ltac:(lia) eq_refl); exact Mgp|].
split; [rewrite (KEEP 4%bv 4 ltac:(unfold acallee_saved; lia) ltac:(lia) eq_refl); exact Mtp|].
split; [exact Mtpx|].
split; [intros a Ha; exact (Hpm2 a (Mpres a Ha))|].
split; [apply (val_mem_kept (w_H W) (w_H W) mem mem2); [intros j Hj; apply STKK; lia | exact Mcode]|].
split; [exact Mc02|].
split; [apply (val_mem_kept (w_H W) (w_H W) mem mem2); [intros j Hj; apply STKK; lia | exact Mra]|].
split; [apply (val_mem_kept (w_H W) (w_H W) mem mem2); [intros j Hj; apply STKK; lia | exact Mra2]|].
split; [exact (fp_cells_kept (w_H W) mem mem2 IMGK Mcells)|].
split; [apply (val_mem_kept (w_H W) (w_H W) mem mem2); [intros j Hj; cbn in Hj; apply IMGK; rewrite Mtpx;
  unfold TFIB_TPX; lia | exact Mtid]|].
split; [exact Mtidr|].
split; [apply (val_mem_kept (w_H W) (w_H W) mem mem2); [intros j Hj; cbn in Hj; apply IMGK; unfold A_GOT_canary;
  lia | exact Mgot]|].
split; [apply (val_mem_kept (w_H W) (w_H W) mem mem2); [intros j Hj; cbn in Hj; apply IMGK; unfold A_canary;
  lia | exact Mcan]|].
split; [exact Mcanr|].
split; [apply (val_mem_kept (w_H W) (w_H W) mem mem2); [intros j Hj; cbn in Hj; apply IMGK; unfold F_STDERR;
  lia | exact Msew1]|].
split; [apply (val_mem_kept (w_H W) (w_H W) mem mem2); [intros j Hj; cbn in Hj; apply IMGK; unfold F_STDERR;
  lia | exact Msew2]|].
split; [exact Msewr|].
split.
{ destruct Mso as [[Hk0 HSI] | [Hk1 HX]].
  - left. split; [exact Hk0|]. intros a Ha. rewrite IMGK by (unfold STDOUT_LO, STDOUT_HI in Ha; lia). exact (HSI a Ha).
  - right. split; [exact Hk1|]. apply (XFR k (w_H W) (w_H W) mem mem2 HX). intros a Ha. apply IMGK;
    unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha; lia. }
split; [intros fd; rewrite (proj1 (sbm_fds_fs md md3 SB)); exact (Mfds fd)|].
split; [rewrite (proj2 (sbm_fds_fs md md3 SB)); exact Mfs|].
split.
{ right. exists f. split; [|split; [reflexivity | exact (proj1 Hk2)]].
  apply (amf_heads_frame tfibsegs link_amf (mrestrict (w_H W) mem) (mrestrict (w_H W) mem2) f); [|exact Hheads].
  intros a Ha. apply xf_mbyte_of_aview. apply IMGK;
  cbv [amf_head_addr amf_ofl_head amf_sink_addr amf_say_addr amf_ofl_lock link_amf] in Ha; lia. }
split; [exact Mf4|]. split; [exact Mf16|]. split; [exact Mfh|].
(* exf_noar after the flush *)
split.
{ apply (icpt_cells_kept (w_H W) (w_H W) mem mem2); [intros a Ha _ _; apply IMGK; lia | exact Nicpt]. }
split.
{ apply (range_addressable_agree (aview tfibsegs (w_H W) mem)); [|exact Nsra].
  intros x Hx.
  assert (Hs : shadow_addr 0x62fee0 / 8 * 8 <= shadow_of_addr SHADOW_OFF x <
               shadow_addr (0x62fee0 + 4096 - 1) / 8 * 8 + 8)
    by (unfold shadow_addr, shadow_of_addr, SHADOW_OFF; lia).
  destruct (fp_said_shadow_off usp f _ Hu46 Nrange ltac:(lia) Hs) as (S1 & S2 & S3 & S4 & S5).
  apply Hfr2; [exact S1 | exact S2 | exact S3 | exact S4 | exact S5]. }
split.
{ apply (hull_kept (aview tfibsegs (w_H W) mem)); [|exact Nshull].
  intros s Hs. destruct (fp_said_shadow_off usp f s Hu46 Nrange ltac:(lia) Hs) as (S1 & S2 & S3 & S4 & S5).
  apply Hfr2; [exact S1 | exact S2 | exact S3 | exact S4 | exact S5]. }
split; [intros a Ha; destruct (Nby a Ha) as [Hp Hni]; exact (conj (Hpm2 a Hp) Hni)|].
split; [exact Nrange|]. split; [exact Nbelow|].
split.
{ apply (range_addressable_agree (aview tfibsegs (w_H W) mem)); [|exact Nfra].
  intros x Hx.
  destruct (fp_block_shadow_off usp f x Hu46 Nrange ltac:(lia) Hx) as (S1 & S2 & S3 & S4 & S5).
  apply Hfr2; [exact S1 | exact S2 | exact S3 | exact S4 | exact S5]. }
{ apply (hull_kept (aview tfibsegs (w_H W) mem)); [|exact Nfhull].
  intros s Hs. destruct (fp_block_hull_off usp f s Hu46 Nrange ltac:(lia) Hs) as (S1 & S2 & S3 & S4 & S5).
  apply Hfr2; [exact S1 | exact S2 | exact S3 | exact S4 | exact S5]. }
Qed.

End t.

(* at the driver's stdout state AD1k.xst, as lib/A/AD2o.v takes it *)
Theorem exf_loop_pend_link : exf_loop_pend_tfa PcapB AD1k.xst.
Proof. exact (exf_loop_pend_ok AD1k.xst AD1k.tfib_xst_frame). Qed.

End p.

Print Assumptions exf_loop_pend_link.
