(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YI08.v:162-174, 176-180;
   projects/cgif/cgif_file_fuzzer/proofs/lib/YN13.v:121-125; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC1n.v:201-203, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D1.v, with its addresses and numbers changed; 351 of its 444 lines of code are new or changed and 5972 lines of the source are left out. *)
(* g_stores of seg_G (LLVMFuzzerTestOneInput_seg_G_hand2_stmt.v, g_stores_stmt): the four stores at
   0x81928..0x81934 (+0x11b4 .. +0x11c4). Three byte stores of zero through x23 = shadow_addr (SFa g pos) at
   offsets 58, 62 and 63 (the shadow cell of `f` at SF+464 and the two of `ef` at SF+496), and one 8-byte store
   of zero through x9 = mf at offset 208. The run is the plain symbolic run from +0x11b4 to +0x11c4 with two
   write regions (x23 + 58 .. 64 in the frame's shadow, x9 + 208 .. 216 in the stack window); the end is the
   boundary file's inv_G_end. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo IdentBlkTail YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
buf_of check_str reac_identity_fw_str reac_identity_reac_ver_str.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_identity_fw_str_c reac_identity_reac_ver_str_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput_seg_G_hand2_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at +0x11b4: the two write windows ------------------------------------------- *)
Definition gs_rsh : YP09.region := YP09.mkRegion (Some 23%nat) 58 64 58 64 [].
Definition gs_rmf : YP09.region := YP09.mkRegion (Some 9%nat) 208 216 208 216 [].
Definition gs_ss : sstate := mkSS 0x11b4 sr_atoms [gs_rsh; gs_rmf] None (mkFacts [] [] []).
(* The bytes the run may change: x23 + 58 .. 64 and x9 + 208 .. 216. *)
Definition gs_win (SH mf a : Z) : Prop := SH + 58 <= a < SH + 64 \/ mf + 208 <= a < mf + 216.

Lemma gs_nwin_app : forall SH mf x, kLowShadowBeg <= SH -> SH + 64 <= kHighMemBeg -> x < mf + 208 ->
  (x < kLowShadowBeg \/ kHighMemBeg <= x) -> ~ gs_win SH mf x.
Proof. intros SH mf x H1 H2 H3 H4. unfold gs_win. lia. Qed.
Lemma gs_nwin_hi : forall SH mf x, SH + 64 <= mf -> mf <= x -> (x < mf + 208 \/ mf + 216 <= x) -> ~ gs_win SH mf x.
Proof. intros SH mf x H1 H2 H3. unfold gs_win. lia. Qed.
Lemma gs_nwin_sh : forall SH mf x, SH + 64 <= mf -> SH <= x < SH + 58 -> ~ gs_win SH mf x.
Proof. intros SH mf x H1 H2. unfold gs_win. lia. Qed.
Lemma gs_sh_off : forall F x, F mod 8 = 0 -> x mod 8 = 0 -> shadow_addr (F + x) = shadow_addr F + x / 8.
Proof.
intros F x HF Hx. unfold shadow_addr.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.div_mod x 8 ltac:(lia)) as DX.
rewrite HF in DF. rewrite Hx in DX.
assert (E1 : (F + x) / 8 = F / 8 + x / 8).
{ replace (F + x) with ((F / 8 + x / 8) * 8) by lia. apply Z.div_mul. lia. }
lia.
Qed.
Lemma gs_fs4 : fs_frame_bytes 4 = 1024.
Proof. reflexivity. Qed.

Ltac gs_chunk := cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]).
Ltac gs_cb0 :=
  let j := fresh "j" in let Hj := fresh "Hj" in
  intros j Hj; cbn [cbyte sv_denot];
  first [ reflexivity
        | unfold byte_of_word; change (bv_unsigned (Z_to_bv 64 0)) with 0; rewrite Z.shiftr_0_l; reflexivity ].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* Application memory lies outside the shadow band. *)
Lemma gs_app_out : forall lo len x, in_app lo len -> lo <= x < lo + len -> x < kLowShadowBeg \/ kHighMemBeg <= x.
Proof. intros lo len x (H1 & [H2 | (H2 & H3)]) Hx; [left | right]; lia. Qed.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput_seg_G_hand2_stmt.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Local Notation ECOMMON := (@ecommon rc PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
Local Notation INV_G := (@inv_G_end fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).

(* ---- what the run keeps and what it writes ------------------------------------------------------------ *)
Lemma gs_keep : forall E (H : word -> bool) (mem mem' : word -> option byte) SH mf,
  bv_unsigned (ew E 23) = SH -> bv_unsigned (ew E 9) = mf ->
  frame_of E [gs_rsh; gs_rmf] (mrestrict H mem) (mrestrict H mem') ->
  forall a, 0 <= a < 2 ^ 64 -> ~ gs_win SH mf a -> aview SEGS H mem' a = aview SEGS H mem a.
Proof.
intros E H mem mem' SH mf U23 U9 HF a Ha Hw.
apply (kept_of_frame E [gs_rsh; gs_rmf] H mem mem' (gs_win SH mf) HF); [|exact Ha|exact Hw].
intros b wlo whi x Hin Hx. unfold windows in Hin. apply in_map_iff in Hin as (rg & Eq & Hrg).
injection Eq as <- <- <-. cbn [In] in Hrg.
destruct Hrg as [<-|[<-|[]]]; unfold gs_rsh, gs_rmf in Hx;
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; [rewrite U23 in Hx | rewrite U9 in Hx];
unfold gs_win; clear - Hx; lia.
Qed.
Lemma gs_vm : forall (W : world SEGS) (m m' : word -> option byte) SH mf a v,
  (forall x, 0 <= x < 2 ^ 64 -> ~ gs_win SH mf x -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  0 <= a -> a + 8 <= 2 ^ 64 -> (forall x, a <= x < a + 8 -> ~ gs_win SH mf x) ->
  val_mem SEGS (rd W m) a 8 v -> val_mem SEGS (rd W m') a 8 v.
Proof.
intros W m m' SH mf a v K H0 H1 Hw Hv. eapply val_mem_kept; [|exact Hv].
intros k Hk. change (Z.of_nat 8) with 8 in Hk.
apply K; [clear - H0 H1 Hk; lia | apply Hw; clear - Hk; lia].
Qed.
Lemma gs_garr8_kept : forall (W W2 : world SEGS) m m2 a l,
  (forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS (w_H W2) m2 (a + j) = aview SEGS (w_H W) m (a + j)) ->
  garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W2 m2) a l.
Proof.
intros W W2 m m2 a l HK HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
eapply val_mem_kept; [|exact Hv].
intros k Hk. cbn in Hk. assert (k = 0) by lia. subst k. rewrite Z.add_0_r. apply HK. lia.
Qed.
Lemma gs_zero_kept : forall (W W2 : world SEGS) m m2 a n,
  (forall i, 0 <= i < n / 8 -> aview SEGS (w_H W2) m2 (shadow_addr a + i) = aview SEGS (w_H W) m (shadow_addr a + i)) ->
  zero_shadow (aview SEGS (w_H W) m) SHADOW_OFF a n -> zero_shadow (aview SEGS (w_H W2) m2) SHADOW_OFF a n.
Proof.
intros W W2 m m2 a n HK HZ i Hi. unfold zero_shadow, shadow_of_addr in *. specialize (HK i Hi).
unfold shadow_addr in HK. rewrite HK. exact (HZ i Hi).
Qed.
Lemma gs_blk_kept : forall (W W2 : world SEGS) m m2 a n,
  (forall i, 0 <= i < (n + 7) / 8 -> aview SEGS (w_H W2) m2 (shadow_addr a + i) = aview SEGS (w_H W) m (shadow_addr a + i)) ->
  block_shadow (aview SEGS (w_H W) m) SHADOW_OFF a n -> block_shadow (aview SEGS (w_H W2) m2) SHADOW_OFF a n.
Proof.
intros W W2 m m2 a n HK (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros i Hi. specialize (HK i Hi). unfold shadow_addr in HK. unfold shadow_of_addr in *. rewrite HK. exact (H3 i Hi).
Qed.
Lemma gs_mid_len : forall g i, length (m_id g i) = 38%nat.
Proof. intros g i. unfold m_id. rewrite SlotModel.rec_id_length. reflexivity. Qed.
(* A byte of a chunk of the final symbolic state. *)
Lemma gs_byte : forall E ss ms (H : word -> bool) i rg base off cv j b,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some rg ->
  base_val E (YP09.r_base rg) = base -> In (YP09.mkChunk off cv) (YP09.r_chunks rg) ->
  0 <= j < cv_len cv -> cbyte SEGS E (base + off) cv j = Some b ->
  mbyte SEGS (mrestrict H (ms_mem ms)) (base + off + j) = Some b.
Proof.
intros E ss ms H i rg base off cv j b HS Hi Hb Hin Hj Hc.
pose proof (st_ok_pi_region_nth E ss (restrict H ms) i rg HS Hi) as HR.
destruct HR as (_ & _ & _ & HC). rewrite Hb in HC. rewrite Forall_forall in HC.
destruct (HC _ Hin j Hj) as (b' & Hb' & Hm). cbn [YP09.c_off YP09.c_val] in Hb', Hm.
rewrite Hc in Hb'. exact (eq_trans Hm (eq_sym Hb')).
Qed.
Lemma gs_val0 : forall E ss ms (H : word -> bool) i rg base off cv,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some rg ->
  base_val E (YP09.r_base rg) = base -> In (YP09.mkChunk off cv) (YP09.r_chunks rg) ->
  8 <= cv_len cv -> (forall j, 0 <= j < 8 -> cbyte SEGS E (base + off) cv j = Some (Z_to_bv 8 0)) ->
  val_mem SEGS (mrestrict H (ms_mem ms)) (base + off) 8 0.
Proof.
intros E ss ms H i rg base off cv HS Hi Hb Hin Hl Hc k Hk.
unfold YO0f.le_byte. change (0 mod 2 ^ (8 * Z.of_nat 8)) with 0. rewrite Z.shiftr_0_l. change (0 mod 256) with 0.
apply (gs_byte E ss ms H i rg base off cv (Z.of_nat k) _ HS Hi Hb Hin); [clear - Hk Hl; lia | apply Hc; clear - Hk; lia].
Qed.
Lemma gs_av0 : forall (H : word -> bool) (m : word -> option byte) a,
  mbyte SEGS (mrestrict H m) (a + 0) = Some (Z_to_bv 8 0) -> aview SEGS H m a = Some 0.
Proof. intros H m a Hb. unfold aview. rewrite Z.add_0_r in Hb. rewrite Hb. reflexivity. Qed.

(* ---- the entry of the run and its writes --------------------------------------------------------------- *)
Lemma gs_entry : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) SH mf,
  bv_unsigned (getr regs 23) = SH -> bv_unsigned (getr regs 9) = mf ->
  0 <= SH -> SH + 64 <= mf + 208 -> mf + 216 <= 2 ^ 64 ->
  (forall o, 58 <= o < 64 -> writable_at SEGS (mrestrict (w_H W) mem) (SH + o)) ->
  (forall o, 208 <= o < 216 -> writable_at SEGS (mrestrict (w_H W) mem) (mf + o)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) gs_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x11b4)) mem (seg_rom SEGS))).
Proof.
intros W regs mem SH mf U23 U9 H0 Hd H64 W23 W9.
assert (B23 : base_val (Eimg (Ereg regs [])) (Some 23%nat) = SH)
  by (cbn [base_val]; rewrite (ew_Eimg_Ereg_nat regs [] 23 23%bv eq_refl); exact U23).
assert (B9 : base_val (Eimg (Ereg regs [])) (Some 9%nat) = mf)
  by (cbn [base_val]; rewrite (ew_Eimg_Ereg_nat regs [] 9 9%bv eq_refl); exact U9).
rewrite restrict_mkst_fx. unfold gs_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
  + unfold region_ok, gs_rsh. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite B23. split; [clear - H0; lia|]. split; [clear - Hd H64; lia|]. split; [exact W23 | constructor].
  + unfold region_ok, gs_rmf. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite B9. split; [clear - H0 Hd; lia|]. split; [clear - H64; lia|]. split; [exact W9 | constructor].
- cbn [pairwise_disjoint all_disjoint]. split; [|exact (conj I I)]. split; [|exact I].
  unfold extent_disjoint, gs_rsh, gs_rmf. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B23, B9. left.
  clear - Hd. lia.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I].
Qed.
(* The writes: the shadow window is the frame's own shadow, the counter slot is in the stack window. *)
Lemma gs_awr : forall E STK sp0 FP bl0 blc (ly : alayout) pos SH mf,
  bv_unsigned (ew E 23) = SH -> bv_unsigned (ew E 9) = mf ->
  shadow_addr (frame_addr ly 4 pos) = SH ->
  sp0 - STK <= mf + 208 -> mf + 216 <= sp0 ->
  awr_ok E [gs_rsh; gs_rmf] STK sp0 FP bl0 blc ly [(4, pos)].
Proof.
intros E STK sp0 FP bl0 blc ly pos SH mf U23 U9 ESH H1 H2.
apply (YCbq.awr_ok_cons_gen E gs_rsh [gs_rmf] STK sp0 FP bl0 blc ly [(4, pos)] 23 SH); [reflexivity | exact U23 | |].
- intros a Ha. unfold gs_rsh in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  unfold awr_byte, in_frames. right; right; right. exists 4, pos. split; [left; reflexivity|].
  right. unfold in_zr. cbn [fst snd]. rewrite ESH. change (fs_frame_bytes 4 / 8) with 128. clear - Ha. lia.
- apply (awr_ok_cons_stack_off E gs_rmf [] STK sp0 FP bl0 blc ly [(4, pos)] 9 (mf - sp0));
  cbn [gs_rmf YP09.r_base YP09.r_wlo YP09.r_whi];
  [reflexivity | clear - U9; lia | clear - H1; lia | clear - H2; lia | apply awr_ok_nil].
Qed.

(* ---- the stack and frame facts at the start --------------------------------------------------------- *)
Lemma gs_facts : AR_laws SEGS B -> STK_LLVMF <= LLVMF_STK ->
  forall (g : ectx) pos mf k ly S (W : world SEGS) mem md,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly S W mem md k ->
  frames S = [(4, pos)] -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
  alloc_ceiling + LLVMF_STK <= e_sp0 g /\ e_sp0 g <= 2 ^ 47 /\
  4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\ SFa g pos mod 32 = 0 /\
  frame_addr ly 4 pos = SFa g pos /\ in_app (SFa g pos) 1024 /\
  (forall i, 0 <= i < 128 -> apresent (w_H W) mem (shadow_addr (SFa g pos) + i)) /\
  (forall a, e_sp0 g - LLVMF_STK <= a < e_sp0 g -> apresent (w_H W) mem a).
Proof.
intros LAWS HSTK g pos mf k ly S W mem md HJ Hfr Hmf.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (Hin : In (4, pos) (frames S)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem md 4 pos HAR Hin) as (F1 & F2 & Fapp).
destruct (al_frames _ _ LAWS ly S W mem md 4 pos HAR Hin) as (F3 & _ & _ & Fsh).
assert (EF : frame_addr ly 4 pos = SFa g pos).
{ unfold SFa, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
rewrite gs_fs4 in F2, Fapp, Fsh. rewrite EF in F1, F2, F3, Fapp, Fsh.
split; [clear - Hceil Hslo; lia|]. split; [clear - Hshi H47; lia|].
split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact EF|]. split; [exact Fapp|].
split; [intros i Hi; exact (proj1 (Fsh i ltac:(change (1024 / 8) with 128; clear - Hi; lia)))|].
exact Hpres.
Qed.

(* ---- the boundary inv_G_end, from what the run did ------------------------------------------------------ *)
Ltac gs_kmf KEEP HSHmf Hmf0 C1 H :=
  apply (gs_vm _ _ _ _ _ _ _ KEEP);
  [ clear - Hmf0 C1; lia | clear - Hmf0; lia
  | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; apply gs_nwin_hi;
    [ exact HSHmf | clear - Hx Hmf0; lia | first [ left; clear - Hx; lia | right; clear - Hx Hmf0; lia ] ]
  | exact H ].

Lemma gs_post : forall (LAWS : AR_laws SEGS B) (HSTK : STK_LLVMF <= LLVMF_STK)
  (AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
     ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
     m_fds md' = m_fds md /\ m_fs md' = m_fs md)
  (g : ectx) pos mf (W2 : world SEGS) ly2 S2 regs2 mem2 md2 regs3 mem3 md3,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem3 md3 (4 * Z.of_nat (m_nrec g) + 4) ->
  frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat (m_nrec g) + 4 <= EV_LLVMF ->
  mo_le MT (e_S g) S2 ((4 * Z.of_nat (m_nrec g) + 4) * MEV MT) ->
  mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 4)) * MEV MT) ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  id_at g pos (m_nrec g) W2 mem2 -> hblocks B g ly2 S2 [] -> sh_reg g pos regs2 ->
  mf_id3 g pos mf W2 mem2 -> mf_id g pos mf W2 mem2 ->
  getr regs2 24 = w64 (SlotModel.t_any_fw (e_pl g)) ->
  getr regs2 25 = w64 (SFa g pos + V_ef) ->
  getr regs2 21 = w64 (SlotModel.t_cap_tok (e_pl g)) ->
  getr regs2 26 = w64 (SlotModel.t_cap_name (e_pl g)) ->
  getr regs2 27 = w64 (SlotModel.t_fam_raw (e_pl g)) ->
  val_mem SEGS (rd W2 mem2) (mf + 176) 8 (SlotModel.t_in (e_pl g)) ->
  val_mem SEGS (rd W2 mem2) (mf + 160) 8 (SlotModel.t_out (e_pl g)) ->
  val_mem SEGS (rd W2 mem2) (mf + 120) 8 (SlotModel.t_cap_disp (e_pl g)) ->
  val_mem SEGS (rd W2 mem2) (mf + 112) 8 (SlotModel.t_row (e_pl g)) ->
  getr regs3 2 = getr regs2 2 -> getr regs3 3 = getr regs2 3 -> getr regs3 4 = getr regs2 4 ->
  getr regs3 8 = getr regs2 8 -> getr regs3 9 = getr regs2 9 -> getr regs3 21 = getr regs2 21 ->
  getr regs3 23 = getr regs2 23 -> getr regs3 24 = getr regs2 24 -> getr regs3 25 = getr regs2 25 ->
  getr regs3 26 = getr regs2 26 -> getr regs3 27 = getr regs2 27 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ gs_win (shadow_addr (SFa g pos)) mf a ->
     aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  aview SEGS (w_H W2) mem3 (shadow_addr (SFa g pos) + 58) = Some 0 ->
  aview SEGS (w_H W2) mem3 (shadow_addr (SFa g pos) + 62) = Some 0 ->
  aview SEGS (w_H W2) mem3 (shadow_addr (SFa g pos) + 63) = Some 0 ->
  val_mem SEGS (rd W2 mem3) (mf + 208) 8 0 ->
  INV_G g pos mf W2 (cfg_at SEGS (BASE + 0x11c4) regs3 mem3 md3).
Proof.
intros LAWS HSTK AJ_NIL_IO g pos mf W2 ly2 S2 regs2 mem2 md2 regs3 mem3 md3 HJ3 Hfrs Hk MLE MOK HC Hid Hbl Hsh
  Hid3 Hmid R24 R25 R21 R26 R27 V176 V160 V120 V112 K2 K3 K4 K8 K9 K21 K23 K24 K25 K26 K27 KEEP B58 B62 B63 V208.
destruct HC as (R2 & R9 & R8 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64b & V72 & V80 & V88 & V96 & V104 & Vfl & HPRE & Hfds & Hfs & Hinb).
pose proof asan_consts as (C1 & _).
assert (HSTKv : STK_LLVMF = 16736) by reflexivity.
destruct (gs_facts LAWS HSTK g pos mf _ ly2 S2 W2 mem3 md3 HJ3 Hfrs Hmfb) as
  (Hceil & Hsp47 & HF4096 & HFceil & HF32 & EF & HFapp & _ & _).
assert (HSF8 : SFa g pos mod 8 = 0) by (apply mod32_mod8; exact HF32).
assert (HQ : SFa g pos = 8 * (SFa g pos / 8)).
{ pose proof (Z.div_mod (SFa g pos) 8 ltac:(discriminate)) as D. rewrite HSF8, Z.add_0_r in D. exact D. }
assert (ESH : shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8) by reflexivity.
assert (HSHlo : kLowShadowBeg <= shadow_addr (SFa g pos))
  by (clear - ESH HQ HF4096; unfold kLowShadowBeg, SHADOW_OFF in *; lia).
assert (HSHhi : shadow_addr (SFa g pos) + 64 <= kHighMemBeg)
  by (clear - ESH HQ HFceil C1; unfold kHighMemBeg, SHADOW_OFF in *; lia).
assert (Hmf0 : alloc_ceiling + 16384 <= mf /\ mf + 320 <= e_sp0 g /\ e_sp0 g <= 2 ^ 47)
  by (clear - Hmfb Hceil Hsp47 HSTK HSTKv; lia).
assert (HSHmf : shadow_addr (SFa g pos) + 64 <= mf) by (clear - HSHhi Hmf0 C1; unfold kHighMemBeg in *; lia).
pose proof HJ3 as (HAR3 & _).
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [Efd Efs].
unfold inv_G_end, acut.
exists ly2, S2, regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact MLE|]. split; [exact MOK|].
split.
{ unfold ecommon.
  split; [rewrite K2; exact R2|]. split; [rewrite K9; exact R9|]. split; [rewrite K8; exact R8|].
  split; [exact Hmfb|]. split; [exact Hmf32|]. split; [rewrite K3; exact Rgp|]. split; [rewrite K4; exact Rtp|].
  split; [gs_kmf KEEP HSHmf Hmf0 C1 V16|]. split; [gs_kmf KEEP HSHmf Hmf0 C1 V64|].
  split; [gs_kmf KEEP HSHmf Hmf0 C1 V192|]. split; [gs_kmf KEEP HSHmf Hmf0 C1 V168|].
  split; [gs_kmf KEEP HSHmf Hmf0 C1 Vra|]. split; [gs_kmf KEEP HSHmf Hmf0 C1 Vs0|].
  split; [gs_kmf KEEP HSHmf Hmf0 C1 V24|]. split; [gs_kmf KEEP HSHmf Hmf0 C1 V32|].
  split; [gs_kmf KEEP HSHmf Hmf0 C1 V40|]. split; [gs_kmf KEEP HSHmf Hmf0 C1 V48|].
  split; [gs_kmf KEEP HSHmf Hmf0 C1 V56|]. split; [gs_kmf KEEP HSHmf Hmf0 C1 V64b|].
  split; [gs_kmf KEEP HSHmf Hmf0 C1 V72|]. split; [gs_kmf KEEP HSHmf Hmf0 C1 V80|].
  split; [gs_kmf KEEP HSHmf Hmf0 C1 V88|]. split; [gs_kmf KEEP HSHmf Hmf0 C1 V96|].
  split; [gs_kmf KEEP HSHmf Hmf0 C1 V104|].
  split.
  { apply (gs_vm _ _ _ _ _ _ _ KEEP); [clear - HF4096; lia | clear - HFceil C1; lia | | exact Vfl].
    intros x Hx. apply gs_nwin_app; [exact HSHlo | exact HSHhi | clear - Hx HFceil Hmf0; lia |].
    apply (gs_app_out (SFa g pos) 1024 x HFapp). clear - Hx. lia. }
  split; [exact HPRE|]. split; [intros fd; rewrite Efd; reflexivity|]. split; [exact Efs|].
  pose proof HPRE as (_ & _ & _ & _ & Hinp & Hlen & _).
  unfold bytes_at8 in *. destruct Hinp as [[Hn0 _] | [[Hn0 Hn1] Hinb0]].
  - assert (Hpl : e_pl g = []) by (destruct (e_pl g); [reflexivity | cbn [length] in Hlen; clear - Hlen Hn0; lia]).
    rewrite Hpl. apply garr8_nil.
  - assert (Hin2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
    { destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hinb0. }
    destruct (al_blocks _ _ LAWS ly2 S2 W2 mem3 md3 (e_p g) (e_n g) HAR3 Hin2) as (_ & Hp4096 & Hpce & Happ & _).
    pose proof (req_size_pos (e_n g) ltac:(clear - Hn0; lia)) as Hrq.
    eapply gs_garr8_kept; [|exact Hinb].
    intros j Hj. rewrite length_map, <- Hlen in Hj. apply KEEP.
    + clear - Hj Hp4096 Hpce Hrq C1. lia.
    + apply gs_nwin_app; [exact HSHlo | exact HSHhi | clear - Hj Hpce Hrq Hmf0; lia |].
      apply (gs_app_out (e_p g) (req_size (e_n g)) _ Happ). clear - Hj Hrq. lia. }
cbv beta.
destruct Hid as (Hidb & Hidz & Hidk).
split.
{ split; [|split].
  - unfold bytes_at8 in *. eapply gs_garr8_kept; [|exact Hidb].
    intros j Hj. rewrite length_map, gs_mid_len in Hj. change (Z.of_nat 38) with 38 in Hj. unfold V_id. apply KEEP.
    + clear - Hj HF4096 HFceil C1. lia.
    + apply gs_nwin_app; [exact HSHlo | exact HSHhi | clear - Hj HFceil Hmf0; lia |].
      apply (gs_app_out (SFa g pos) 1024 _ HFapp). clear - Hj. lia.
  - unfold sh_zero in *. eapply gs_zero_kept; [|exact Hidz]. intros i Hi. unfold N_id in Hi. unfold V_id.
    rewrite (gs_sh_off (SFa g pos) 352 HSF8 eq_refl). change (352 / 8) with 44. change (38 / 8) with 4 in Hi.
    apply KEEP; [clear - Hi HSHlo HSHhi; unfold kLowShadowBeg, kHighMemBeg in *; lia
      | apply gs_nwin_sh; [exact HSHmf | clear - Hi; lia]].
  - unfold sh_blk in *. eapply gs_blk_kept; [|exact Hidk]. intros i Hi. unfold N_id in Hi. unfold V_id.
    rewrite (gs_sh_off (SFa g pos) 352 HSF8 eq_refl). change (352 / 8) with 44. change ((38 + 7) / 8) with 5 in Hi.
    apply KEEP; [clear - Hi HSHlo HSHhi; unfold kLowShadowBeg, kHighMemBeg in *; lia
      | apply gs_nwin_sh; [exact HSHmf | clear - Hi; lia]]. }
split; [exact Hbl|].
split; [unfold sh_reg in *; rewrite K23; exact Hsh|].
split; [unfold mf_id3 in *; gs_kmf KEEP HSHmf Hmf0 C1 Hid3|].
split; [unfold mf_id in *; gs_kmf KEEP HSHmf Hmf0 C1 Hmid|].
split.
{ unfold sh_zero, zero_shadow, V_f, N_f. intros i Hi. change (8 / 8) with 1 in Hi.
  assert (Ei : i = 0) by (clear - Hi; lia). subst i.
  change (shadow_of_addr SHADOW_OFF (SFa g pos + 464)) with (shadow_addr (SFa g pos + 464)).
  rewrite (gs_sh_off (SFa g pos) 464 HSF8 eq_refl). change (464 / 8) with 58. rewrite Z.add_0_r. exact B58. }
split.
{ unfold sh_zero, zero_shadow, V_ef, N_ef. intros i Hi. change (16 / 8) with 2 in Hi.
  change (shadow_of_addr SHADOW_OFF (SFa g pos + 496)) with (shadow_addr (SFa g pos + 496)).
  rewrite (gs_sh_off (SFa g pos) 496 HSF8 eq_refl). change (496 / 8) with 62.
  assert (Ei : i = 0 \/ i = 1) by (clear - Hi; lia).
  destruct Ei as [-> | ->]; [rewrite Z.add_0_r; exact B62|].
  replace (shadow_addr (SFa g pos) + 62 + 1) with (shadow_addr (SFa g pos) + 63) by (clear; lia). exact B63. }
split; [exact V208|].
split; [rewrite K24; exact R24|]. split; [rewrite K25; exact R25|]. split; [rewrite K21; exact R21|].
split; [rewrite K26; exact R26|]. split; [rewrite K27; exact R27|].
split; [gs_kmf KEEP HSHmf Hmf0 C1 V176|]. split; [gs_kmf KEEP HSHmf Hmf0 C1 V160|].
split; [gs_kmf KEEP HSHmf Hmf0 C1 V120|]. gs_kmf KEEP HSHmf Hmf0 C1 V112.
Qed.

(* ---- the run ------------------------------------------------------------------------------------------- *)
Lemma g_stores : g_stores_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS.
Proof.
unfold g_stores_stmt.
intros LAWS TL HSTK AJ_NIL_IO g pos mf W2 c2 Hpre.
destruct Hpre as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (Hid & Hbl & Hsh & Hid3 & Hmid & R24 & R25 & R21 & R26 & R27 & V176 & V160 & V120 & V112).
pose proof HC as HC0. destruct HC0 as (_ & R9 & _ & Hmfb & _).
pose proof asan_consts as (C1 & _).
assert (HSTKv : STK_LLVMF = 16736) by reflexivity.
destruct (gs_facts LAWS HSTK g pos mf _ ly2 S2 W2 mem2 md2 HJ Hfrs Hmfb) as
  (Hceil & Hsp47 & HF4096 & HFceil & HF32 & EF & HFapp & Hshp & Hpres).
assert (HSF8 : SFa g pos mod 8 = 0) by (apply mod32_mod8; exact HF32).
assert (HQ : SFa g pos = 8 * (SFa g pos / 8)).
{ pose proof (Z.div_mod (SFa g pos) 8 ltac:(discriminate)) as D. rewrite HSF8, Z.add_0_r in D. exact D. }
assert (ESH : shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8) by reflexivity.
assert (HSHlo : kLowShadowBeg <= shadow_addr (SFa g pos))
  by (clear - ESH HQ HF4096; unfold kLowShadowBeg, SHADOW_OFF in *; lia).
assert (HSHhi : shadow_addr (SFa g pos) + 64 <= kHighMemBeg)
  by (clear - ESH HQ HFceil C1; unfold kHighMemBeg, SHADOW_OFF in *; lia).
assert (Hmf0 : alloc_ceiling + 16384 <= mf /\ mf + 320 <= e_sp0 g /\ e_sp0 g <= 2 ^ 47)
  by (clear - Hmfb Hceil Hsp47 HSTK HSTKv; lia).
assert (HSHmf : shadow_addr (SFa g pos) + 64 <= mf) by (clear - HSHhi Hmf0 C1; unfold kHighMemBeg in *; lia).
assert (Hw1 : e_sp0 g - LLVMF_STK <= mf + 208) by (clear - Hmfb HSTK HSTKv; lia).
assert (Hw2 : mf + 216 <= e_sp0 g) by (clear - Hmf0; lia).
assert (U9 : bv_unsigned (getr regs2 9) = mf)
  by (rewrite R9; unfold w64; apply unsigned_lit_small; clear - Hmf0 C1; lia).
assert (U23 : bv_unsigned (getr regs2 23) = shadow_addr (SFa g pos))
  by (unfold sh_reg in Hsh; rewrite Hsh; unfold w64; apply unsigned_lit_small;
      clear - HSHlo HSHhi; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (W23 : forall o, 58 <= o < 64 -> writable_at SEGS (mrestrict (w_H W2) mem2) (shadow_addr (SFa g pos) + o))
  by (intros o Ho; apply (apresent_writable SEGS); apply Hshp; clear - Ho; lia).
assert (W9 : forall o, 208 <= o < 216 -> writable_at SEGS (mrestrict (w_H W2) mem2) (mf + o))
  by (intros o Ho; apply (apresent_writable SEGS); apply Hpres; clear - Ho Hw1 Hw2; lia).
remember (Eimg (Ereg regs2 (@nil word))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS : st_ok_pi SEGS VAL E gs_ss
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x11b4)) mem2 (seg_rom SEGS)))).
{ rewrite HE. apply (gs_entry W2 regs2 mem2 (shadow_addr (SFa g pos)) mf U23 U9);
  [clear - HSHlo; unfold kLowShadowBeg in *; lia | clear - HSHmf; lia | clear - Hmf0; lia | exact W23 | exact W9]. }
clear HE.
assert (UE23 : bv_unsigned (ew E 23) = shadow_addr (SFa g pos)) by (rewrite (EE 23%nat 23%bv eq_refl); exact U23).
assert (UE9 : bv_unsigned (ew E 9) = mf) by (rewrite (EE 9%nat 9%bv eq_refl); exact U9).
assert (ESH2 : shadow_addr (frame_addr ly2 4 pos) = shadow_addr (SFa g pos)) by (rewrite EF; reflexivity).
pose (RUNTOP := SRr_run_to_pi_AJ B LAWS).
unfold cfg_at. change (w64 (BASE + 0x11b4)) with (Z_to_bv 64 (BASE + 0x11b4)).
paj_run_to_sh RUNTOP HS HJ 0x11c4.
{ exact (gs_awr E LLVMF_STK (e_sp0 g) [] _ _ ly2 pos (shadow_addr (SFa g pos)) mf UE23 UE9 ESH2 Hw1 Hw2). }
(* The state at +0x11c4: region 0 (x23) holds the chunks 63, 62, 58 = CVal 1 (SLit 0), region 1 (x9) the chunk
   208 = CVal 8 (SLit 0); the registers are unchanged. *)
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
  pose proof (gs_keep E (w_H W2) mem2 (ms_mem msF) (shadow_addr (SFa g pos)) mf UE23 UE9 HFr) as KEEP;
  assert (B58 : mbyte SEGS (mrestrict (w_H W2) (ms_mem msF)) (shadow_addr (SFa g pos) + 58 + 0) = Some (Z_to_bv 8 0))
    by (eapply (gs_byte E _ msF (w_H W2) 0%nat _ (shadow_addr (SFa g pos)) 58 _ 0 (Z_to_bv 8 0) HS);
        [reflexivity | cbn [YP09.r_base base_val]; exact UE23 | gs_chunk | cbn; lia | cbn [cbyte sv_denot]; reflexivity]);
  assert (B62 : mbyte SEGS (mrestrict (w_H W2) (ms_mem msF)) (shadow_addr (SFa g pos) + 62 + 0) = Some (Z_to_bv 8 0))
    by (eapply (gs_byte E _ msF (w_H W2) 0%nat _ (shadow_addr (SFa g pos)) 62 _ 0 (Z_to_bv 8 0) HS);
        [reflexivity | cbn [YP09.r_base base_val]; exact UE23 | gs_chunk | cbn; lia | cbn [cbyte sv_denot]; reflexivity]);
  assert (B63 : mbyte SEGS (mrestrict (w_H W2) (ms_mem msF)) (shadow_addr (SFa g pos) + 63 + 0) = Some (Z_to_bv 8 0))
    by (eapply (gs_byte E _ msF (w_H W2) 0%nat _ (shadow_addr (SFa g pos)) 63 _ 0 (Z_to_bv 8 0) HS);
        [reflexivity | cbn [YP09.r_base base_val]; exact UE23 | gs_chunk | cbn; lia | cbn [cbyte sv_denot]; reflexivity]);
  assert (V208 : val_mem SEGS (rd W2 (ms_mem msF)) (mf + 208) 8 0)
    by (eapply (gs_val0 E _ msF (w_H W2) 1%nat _ mf 208 _ HS);
        [reflexivity | cbn [YP09.r_base base_val]; exact UE9 | gs_chunk | cbn; lia | gs_cb0])
end.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
prreg HS (9%bv : bv 5) P9. prreg HS (21%bv : bv 5) P21. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3. rewrite (EE 4%nat 4%bv eq_refl) in P4.
rewrite (EE 8%nat 8%bv eq_refl) in P8. rewrite (EE 9%nat 9%bv eq_refl) in P9.
rewrite (EE 21%nat 21%bv eq_refl) in P21. rewrite (EE 23%nat 23%bv eq_refl) in P23.
rewrite (EE 24%nat 24%bv eq_refl) in P24. rewrite (EE 25%nat 25%bv eq_refl) in P25.
rewrite (EE 26%nat 26%bv eq_refl) in P26. rewrite (EE 27%nat 27%bv eq_refl) in P27.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
  pmkst HS; apply SRr_ret;
  apply (gs_post LAWS HSTK AJ_NIL_IO g pos mf W2 ly2 S2 regs2 mem2 md2 (ms_regs msF) (ms_mem msF) _ HJ Hfrs Hk MLE MOK
    HC Hid Hbl Hsh Hid3 Hmid R24 R25 R21 R26 R27 V176 V160 V120 V112 P2 P3 P4 P8 P9 P21 P23 P24 P25 P26 P27 KEEP
    (gs_av0 _ _ _ B58) (gs_av0 _ _ _ B62) (gs_av0 _ _ _ B63) V208)
end.
Qed.
Check (g_stores : g_stores_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).

End c.
End b.
End a.

Print Assumptions g_stores.
