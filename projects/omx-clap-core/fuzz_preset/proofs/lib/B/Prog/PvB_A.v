(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/A/ACjr.v (equal, after the mapping, to the generic part of lib/YC4c.v) for libreac/fuzz_disco's program walk, over fuzz_disco's listing; mres_range states fuzz_disco.asan's image range as YImgTop's IMG_LO and IMG_TOP in place of cgif's literals; cgif's PC_INIT, lzw_MR, lzw_tabs and the kept_ctx/kept_ctx_m tactics of cgif's 72-byte LZW context block are left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoACjr.v, with its module paths changed; 136 of its 271 lines of code are new or changed and 109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/PRW_StepKit.v, with its module paths and module names changed; 1086 of its 1137 lines of code are new or changed and 220 lines of the source are left out. *)
(* fuzz_preset image B (asan-ubsan), parse_value 0x8637c: segment A, the ENTRY, B 0x8637c .. 0x86484,
   over the ONE image-B program listing (lib/B/Listing_prog.v) with the PA-listing engine on YCbqG's ajournal_x.
   From the entry state (pv_pre) to the cut C1 (PvB_Defs.v pv_at_C1, back from `jal skip_ws`).
   WHAT THE CODE DOES (the listing 0x8637c .. 0x86480): sp -= 160, `sd zero` at the new sp, ra and s0 .. s11 saved at
   sp0 - 8 .. sp0 - 104, s0 = sp0, `andi sp, sp, -32` (Y = sp0 - 160 when sp0 = 0 mod 32, sp0 - 176 when sp0 = 16 mod 32),
   s1 = Y, s3 = v, s4 = q; the shadow base (s7) and the use-after-return flag through their GOT words; the flag reads 1
   (YCbqG's alx_const) so `beqz a2` falls through to `li a0, 64; jal __asan_stack_malloc_0` (0x863ec). The frame-area
   call returns the class-0 fake frame fa = frame_addr ly 0 pos (the engine's YGcallMxmn.v aj_stack_malloc_at_xm;
   count_cid 0 < fs_frames 0 by pv_pre's frames bound); fa >= 4096 so `bnez s2` goes to 0x86420 and the
   real-stack fallback 0x86404 .. 0x8641c is unreachable. Then fa is spilled at Y + 48, the fake frame's header (magic,
   descriptor, pc) and its 8 shadow bytes (pv_shadow_live) are written, and `jal skip_ws` is called with a0 = q (the
   skip_ws text through YCbqGcallW.v's aj_call_xW, window from the callee sp Y up to sp0 + e).
   HOW: two engine stretches (run 1, 0x8637c .. 0x863ec, in both alignment cases; run 2, 0x863f0 .. 0x86480), each a
   symbolic state seated fresh from the facts at its start; the two calls by their kit rules.
   THE MEMORY NORMAL FORM (owner 10:2xZ): aj_memnorm rides from pv_pre's memnorm conjunct to pv_at_C1's last conjunct:
   across the two engine stretches by YSRrMemnorm.v's runner twin (paj_run_x_inv at P := memnorm), across the two
   calls by the callees' texts in the m-form (post Q /\ (memnorm mem -> memnorm mem'), no entry premise: the engine's
   YGcallMxmn.astack_malloc_realizes_xm and the PRH_FnReader.v tskip_ws_specX over PRH_Base.v fQmn / fpostWm).
   Numerals: 19632 / 19748 / 19896 are listing offsets (DERIVED: B pc - B_prog_base 0x816cc, PvB_Defs AF_pv /
   AF_pv_sm_ret / AF_pv_skw_ret); 38879 the frame descriptor's offset in the read-only band (DERIVED, PvB_Defs
   PV_DESCR_OFF); 160 / 176 / 48 / 56 / 64 / 8 / 24 / 104 are LENGTH (frame, slack, slots, class-0 frame and its shadow,
   header, saved area); 4272 = 176 + 4096 DERIVED; 0, 16, 32 alignments; 2 ^ 44 .. 2 ^ 47, 4096 LENGTH (atom ranges);
   2 ^ 40 LENGTH (the listing's slot-offset width as pa_B_ok states it, pva_slot_lt_ceil) and 4 LENGTH (a slot's byte
   length, find_segment's width);
   the chunk words the run reads back (0x41b58ab3, 0xf1 / 0xf8 / 0xf3 as 2 ^ 64 - 15 / - 8 / - 13) are WORDS of the
   listing. No ADDRESS literal.
   Rule 24: proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG YC80x YC1fPx YG0p YGcallx FCiface YGcallSx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YStrtodRowX YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs PvB_Model PvB_A_Home.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Instance PIB : PrhImg := prh_img_B.
(* YK06 (imported for the kit) declares a concrete alloc_ceiling; every kit statement this file meets (astk_ok, achain,
   the journal) reads the run's ceiling YM05.alloc_ceiling, so the name means that one here *)
#[local] Abbreviation alloc_ceiling := YM05.alloc_ceiling.

(* ---- the symbolic states of the two stretches ---- *)
Definition PVA_Bx : sv := SLit SHADOW_OFF.
Definition PVA_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* run 1 (0x8637c .. the frame-area call): atom 34 = X, the 32-aligned base of the entry sp (sp0 = X + c, c = 0 or
   16); the own frame [sp0 - 176, sp0) writable; the shadow-base GOT word (A_OBJ 0) and the flag's GOT word (A_OBJ 1),
   the shadow-base cell (A_OBJ 12, = SHADOW_OFF, atom 32) and the flag cell after it (= 1) *)
Definition pva_regions1 (c : Z) : smem :=
  [ YP09.mkRegion (Some 34%nat) (c - 176) c (c - 176) c [];
    got_regionP;
    YP09.mkRegion (Some (A_OBJ 1)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 12) 8))];
    YP09.mkRegion (Some (A_OBJ 12)) 0 12 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 4 (SLit 1))] ].
Definition pva_facts1 : facts :=
  mkFacts [ (34%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] [] [].
Definition pva_ss1 (c : Z) : sstate := mkSS AF_pv (sr_set sr_atoms 2%bv (SOff 34 c)) (pva_regions1 c) None pva_facts1.
(* run 2 (0x863f0 .. the skip_ws call): atoms 9 = Y (s1 = sp), 34 = fa (a0), 35 = fa's shadow address, 32 =
   SHADOW_OFF (s7); fa's shadow address as the code computes it is aliased to atom 35. The stretch reads no shadow
   (no check between the two calls), so the shadow span is empty (0, 0) and every written window lies outside it. *)
Definition pva_fash : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 34 0) (SLit 3)) (SOff 32 0).
Definition pva_regs2 : list sv :=
  sr_set (sr_set (sr_set sr_atoms 2%bv (SOff 9 0)) 10%bv (SOff 34 0)) 23%bv (SOff 32 0).
Definition pva_regions2 : smem :=
  [ YP09.mkRegion (Some 9%nat) 0 56 48 56 [];
    YP09.mkRegion (Some 34%nat) 0 64 0 24 [];
    YP09.mkRegion (Some 35%nat) 0 8 0 8 [] ].
Definition pva_facts2 : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (34%nat, mkAF 4096 (2 ^ 47) 5); (35%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0) ] []
          [ (pva_fash, SOff 35 0) ].
Definition PVA_Bspan2 : Z * Z := (0, 0).
Definition pva_ss2 : sstate := mkSS AF_pv_sm_ret pva_regs2 pva_regions2 None pva_facts2.

(* a chunk of a symbolic state, found as the walk's file FuzzMalloc.v (lib/A/Prog) fm_cv finds it *)
Definition pva_cv (rs : smem) (j : nat) (off w : Z) : option YP09.chunk :=
  match find_region rs (Some j) off w with Some r => find_chunk (YP09.r_chunks r) off w | None => None end.

Lemma pva_count_le : forall cid l, count_cid cid l <= Z.of_nat (length l).
Proof. intros cid l. induction l as [|[c p] t IH]; cbn [count_cid length]; [lia|]. destruct (c =? cid); lia. Qed.
(* a kept register (aregs_preserved's `Z_to_bv 5 r` form) read at its literal index *)
Lemma pva_getr_lit : forall (regs regs' : bvmap 5 word) (r : bv 5) z, bv_unsigned r = z ->
  getr regs' (Z_to_bv 5 z) = getr regs (Z_to_bv 5 z) -> getr regs' r = getr regs r.
Proof. intros regs regs' r z Hr H. subst z. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma pva_val_lit : forall (segs : list Segment) m a (n : nat) regs (r : bv 5) z, bv_unsigned r = z ->
  val_mem segs m a n (bv_unsigned (getr regs (Z_to_bv 5 z))) -> val_mem segs m a n (bv_unsigned (getr regs r)).
Proof. intros segs m a n regs r z Hr H. subst z. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac pva_keep P rlit z := exact (pva_getr_lit _ _ rlit z eq_refl (P z ltac:(unfold acallee_saved; lia))).

(* ---- fpre's return-address bound (the kit's PRH_Base.v (sha256 586b1b19f7ad; internal record), fpre's conjunct `raZ regs <
   YM05.alloc_ceiling`): a listing slot's pc is below the run's allocation ceiling. The slot's word is fetched from an
   image segment (pa_cert, pa_tbl_ok), so the pc is in_img, so below kLowMemEnd (pa_segs_low), which is below
   CEIL_MIN <= YM05.alloc_ceiling (YM05.alloc_ceiling_value). Statement and proof are PvB_NC.v pnc_slot_lt_ceil's
   (a copy of PRW_StepKit.pa_slot_lt_ceil, lib/A/Prog/PRW_StepKit.v:235;
   neither file is in this file's Require closure). ---- *)
Section pc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
Lemma pva_slot_lt_ceil : forall k e, 0 <= k < 2 ^ 40 -> plookup pl_tpi k = Some e ->
  pa_val A_TEXT + k < YM05.alloc_ceiling.
Proof.
intros k e Hk40 Hk. pose proof pa_B_ok as HB. rewrite <- pl_tpi_eq in Hk.
pose proof (cert_slot asym (clookup pa_tbl) pa_val pa_sigma L pa_cert k e Hk) as [Hc Hk0].
unfold pi_slot_check in Hc.
destruct (clookup pa_tbl (pa_val A_TEXT + k)) as [wz|] eqn:Hf; [|discriminate].
pose proof (pa_tbl_ok _ _ Hf) as Hfw.
unfold fetch_word in Hfw. destruct (negb _); [discriminate|].
unfold code_read in Hfw.
destruct (find_segment pa_segs (bv_unsigned (Z_to_bv 64 (pa_val A_TEXT + k))) (Z.of_N 4)) as [sg|] eqn:Hfs; [|discriminate].
destruct (find_segment_hit _ _ _ _ Hfs) as (Hin & Hlo & Hhi).
assert (Himg : in_img pa_segs (bv_unsigned (Z_to_bv 64 (pa_val A_TEXT + k)))).
{ exists sg. split; [exact Hin|]. change (Z.of_N 4) with 4 in Hhi. lia. }
pose proof (pa_segs_low _ Himg) as HR.
rewrite Z_to_bv_unsigned in HR. unfold bv_wrap in HR. change (bv_modulus 64) with (2 ^ 64) in HR.
rewrite Z.mod_small in HR by lia.
pose proof (@YM05.alloc_ceiling_value rc) as [[HC _] _]. unfold kLowMemEnd in HR. lia.
Qed.
End pc.

Section c. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PSTX := (@prh_pst prh_img_B).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- helpers over the engine's states (no Section hypothesis) ---- *)
Lemma pva_cv_ok : forall E ss ms j off w c, st_ok SEGS E ss ms -> pva_cv (ss_mem ss) j off w = Some c ->
  YP09.chunk_ok SEGS E (ms_mem ms) (bv_unsigned (ew E j)) c.
Proof.
intros E ss ms j off w c HS H. unfold pva_cv in H.
destruct (find_region (ss_mem ss) (Some j) off w) as [r|] eqn:Hr; [|discriminate H].
destruct (find_region_sound _ _ _ _ _ Hr) as (Hin & Hb & _).
destruct (find_chunk_sound _ _ _ _ H) as (Hcin & _).
destruct (st_ok_mem_ok SEGS E ss ms HS) as (_ & Hrs & _).
destruct (proj1 (Forall_forall _ _) Hrs r Hin) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hcin) as Hck. rewrite Hb in Hck. exact Hck.
Qed.
Lemma pva_val : forall E ss ms j off (w : N) e v b a, st_ok SEGS E ss ms ->
  pva_cv (ss_mem ss) j off (Z.of_N w) = Some (YP09.mkChunk off (CVal w e)) ->
  bv_unsigned (ew E j) = b -> a = b + off -> U E e = v -> Z.of_N w <= 8 -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
  val_mem SEGS (ms_mem ms) a (N.to_nat w) v.
Proof.
intros E ss ms j off w e v b a HS H Hb Ha HU Hw Hv. subst a.
pose proof (pva_cv_ok E ss ms j off (Z.of_N w) _ HS H) as Hck. rewrite Hb in Hck.
apply (val_of_chunk_ok SEGS E _ _ off w e v Hck); [|exact Hv | exact Hw].
rewrite <- HU. unfold U. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* a word chunk of the run's end state, read through the restricted memory *)
Lemma pva_val8 : forall E ss H ms j off e v b a, st_ok SEGS E ss (restrict H ms) ->
  pva_cv (ss_mem ss) j off 8 = Some (YP09.mkChunk off (CVal 8 e)) -> bv_unsigned (ew E j) = b -> a = b + off ->
  U E e = v -> val_mem SEGS (mrestrict H (ms_mem ms)) a 8 v.
Proof.
intros E ss H ms j off e v b a HS Hc Hb Ha Hv.
exact (pva_val E ss (restrict H ms) j off 8 e v b a HS Hc Hb Ha Hv ltac:(cbn; lia)
  ltac:(rewrite <- Hv; unfold U; exact (bv_unsigned_in_range _ (sv_denot E e)))).
Qed.
Lemma pva_byte : forall E ss ms j off e b a, st_ok SEGS E ss ms ->
  pva_cv (ss_mem ss) j off 1 = Some (YP09.mkChunk off (CVal 1 e)) -> bv_unsigned (ew E j) = b -> a = b + off ->
  val_mem SEGS (ms_mem ms) a 1 (U E e mod 256).
Proof.
intros E ss ms j off e b a HS H Hb Ha k Hk. subst a. assert (Ek : k = 0%nat) by lia. subst k.
pose proof (pva_cv_ok E ss ms j off 1 _ HS H) as Hck. rewrite Hb in Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2). cbn in Hb1. injection Hb1 as <-.
cbn [YP09.c_off] in Hb2. rewrite Z.add_0_r in Hb2. cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite Hb2. f_equal.
unfold YP09.byte_of_word. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold YO0f.le_byte, U, bv_wrap, bv_modulus.
cbn [Z.of_N Z.of_nat Z.mul Pos.mul]. rewrite ?Z.shiftr_0_r.
try change (2 ^ 8) with 256. rewrite ?Zmod_mod. reflexivity.
Qed.
Lemma pva_byte_v : forall E ss H ms j off e v b a, st_ok SEGS E ss (restrict H ms) ->
  pva_cv (ss_mem ss) j off 1 = Some (YP09.mkChunk off (CVal 1 e)) -> bv_unsigned (ew E j) = b -> a = b + off ->
  U E e mod 256 = v -> val_mem SEGS (mrestrict H (ms_mem ms)) a 1 v.
Proof.
intros E ss H ms j off e v b a HS Hc Hb Ha Hv. rewrite <- Hv.
exact (pva_byte E ss (restrict H ms) j off e b a HS Hc Hb Ha).
Qed.
(* a byte outside the run's write windows keeps its view (FuzzMalloc.v fm_aview_of_frame) *)
Lemma pva_aview_of_frame : forall (Wx : world SEGS) (E' : env) rs (m m' : word -> option byte) a,
  frame_of E' rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') -> ~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E' rs m m' a HF Hn Ha. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Lemma pva_val_of_rd32 : forall H mem a v, rd32 (aview SEGS H mem) a v -> val_mem SEGS (mrestrict H mem) a 4 v.
Proof.
intros H mem a v Hr k Hk. specialize (Hr k Hk). unfold aview in Hr.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Hb; [|discriminate Hr].
cbn [option_map] in Hr. injection Hr as Hr. f_equal. change (YO0f.le_byte v 4 k) with (YG0f.le_byte v 4 k).
rewrite <- Hr. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* le_byte reads its value mod 2 ^ (8 n) *)
Lemma pva_val_mod : forall m a v, val_mem SEGS m a 8 (v mod 2 ^ 64) -> val_mem SEGS m a 8 v.
Proof.
intros m a v H k Hk. rewrite (H k Hk). do 2 f_equal. unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64.
rewrite Zmod_mod. reflexivity.
Qed.
(* a read-only byte is an image byte (FuzzStrdupB.v sd_ro_img) *)
Lemma pva_ro_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.
(* a writable byte off the image stays writable while the memory shows the same byte (PvB_D_Lit.v pvl_wr) *)
Lemma pva_wr_keep : forall (m m' : word -> option byte) x, writable_at SEGS m x -> mbyte SEGS m' x = mbyte SEGS m x ->
  0 <= x < 2 ^ 64 -> ~ in_img SEGS x -> writable_at SEGS m' x.
Proof.
intros m m' x Hw Hb Hx Hn. unfold writable_at, wview in *. unfold mbyte in Hb.
destruct (m' (Z_to_bv 64 x)) as [b'|]; [discriminate|].
destruct (m (Z_to_bv 64 x)) as [b|]; [|exact Hw].
rewrite (seg_rom_none SEGS x Hx Hn) in Hb. discriminate Hb.
Qed.
(* rdword reads its 8 bytes only *)
Lemma pva_rdword_ext : forall (rd rd' : reader) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
  rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
(* a word the memory holds is the word the view reads (YCem.v rdword_of_val_mem; YCem's YCeh does not build on
   this base, so the 15 lines are restated here) *)
Lemma pva_rdword_of_val : forall H mem a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (Bk : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (YG0f.le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  change (YO0f.le_byte v 8 k) with (YG0f.le_byte v 8 k). unfold YG0f.le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bk 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bk 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bk 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bk 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bk 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bk 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bk 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bk 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.
(* A frame-pointer chain under a view that changed ONE 8-aligned word X, whose old and new contents are >= 4096 and
   whose new content lies below the chain's floor L: a record reading X as its ra keeps a code-range ra; a record
   reading X as its next fp stops the chain there (bad_next). The parse_items -> parse_value case: s0 = q + 16, so
   the caller's record reads the cursor's p word at q, which skip_ws rewrites (the 06:39Z ruling). *)
Lemma pva_fpchain_patch : forall (rd rd' : reader) X L top ch bp,
  fpchain (rdword rd) bp top ch -> L + 16 <= bp -> bp + 16 <= top -> bp mod 8 = 0 -> X mod 8 = 0 ->
  (forall a, L <= a -> a + 8 <= top -> a mod 8 = 0 -> a <> X -> rdword rd' a = rdword rd a) ->
  (exists w, rdword rd' X = Some w /\ 4096 <= w < L) ->
  (exists w0, rdword rd X = Some w0 /\ 4096 <= w0) ->
  exists ch', fpchain (rdword rd') bp top ch' /\ Forall (fun r => bp <= fst (fst r)) ch'.
Proof.
intros rd rd' X L top ch. induction ch as [|[[fp ra] nfp] rest IH]; intros bp Hc HL Htop Hb8 HX8 Hag Hw' Hw0.
- destruct Hc as (r & Hr & Hr4).
  assert (Hne : bp - 8 <> X).
  { intros E. destruct Hw0 as (w0 & Hw0 & H4). rewrite <- E, Hr in Hw0. injection Hw0 as Ew. lia. }
  exists []. split; [|constructor]. exists r. split; [|exact Hr4]. rewrite (Hag (bp - 8)) by lia. exact Hr.
- destruct Hc as (Efp & Hal & Hra & Hnfp & Hra4 & Hrest). subst fp.
  assert (Hra' : exists ra', rdword rd' (bp - 8) = Some ra' /\ 4096 <= ra').
  { destruct (Z.eq_dec (bp - 8) X) as [E8 | N8].
    - destruct Hw' as (w & Hw & Hw4 & _). exists w. rewrite E8. split; [exact Hw | exact Hw4].
    - exists ra. rewrite (Hag (bp - 8)) by lia. split; [exact Hra | exact Hra4]. }
  destruct Hra' as (ra' & Hra'1 & Hra'2).
  destruct (Z.eq_dec (bp - 16) X) as [E16 | N16].
  + destruct Hw' as (w & Hw & Hwlo & Hwhi). exists [(bp, ra', w)].
    split; [|constructor; [cbn; lia | constructor]].
    cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact Hra'1|].
    split; [rewrite E16; exact Hw|]. split; [exact Hra'2|].
    replace (bad_next bp top w) with true; [reflexivity|]. unfold bad_next. symmetry.
    apply orb_true_intro. left. apply orb_true_intro. left. apply Z.leb_le. lia.
  + assert (Hn' : rdword rd' (bp - 16) = Some nfp) by (rewrite (Hag (bp - 16)) by lia; exact Hnfp).
    destruct (bad_next bp top nfp) eqn:Hbad.
    * exists [(bp, ra', nfp)]. split; [|constructor; [cbn; lia | constructor]].
      cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact Hra'1|]. split; [exact Hn'|].
      split; [exact Hra'2|]. rewrite Hbad. reflexivity.
    * pose proof Hbad as Hbad'. unfold bad_next in Hbad'.
      apply Bool.orb_false_iff in Hbad' as [Hb12 Hb3]. apply Bool.orb_false_iff in Hb12 as [Hb1 Hb2].
      apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2. apply Bool.negb_false_iff, Z.eqb_eq in Hb3.
      change (fpchain (rdword rd) nfp top rest) in Hrest.
      destruct (IH nfp Hrest ltac:(lia) ltac:(lia) Hb3 HX8 Hag Hw' Hw0) as (ch' & Hc' & Hf').
      exists ((bp, ra', nfp) :: ch'). split.
      -- cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact Hra'1|]. split; [exact Hn'|].
         split; [exact Hra'2|]. rewrite Hbad. exact Hc'.
      -- constructor; [cbn; lia|]. eapply Forall_impl; [|exact Hf']. intros r Hr. cbn beta in Hr |- *. lia.
Qed.
Lemma pva_achain_patch : forall ly (rd rd' : reader) sp v ch X,
  achain ly rd sp v ch -> X mod 8 = 0 ->
  (forall a, sp <= a -> a + 8 <= ly_top ly -> a mod 8 = 0 -> a <> X -> rdword rd' a = rdword rd a) ->
  (exists w, rdword rd' X = Some w /\ 4096 <= w < sp) -> (exists w0, rdword rd X = Some w0 /\ 4096 <= w0) ->
  exists ch', achain ly rd' sp v ch'.
Proof.
intros ly rd rd' sp v ch X [(Hb & ->) | (H1 & H2 & H3 & H4 & H5)] HX Hag Hw' Hw0.
- exists []. left. split; [exact Hb | reflexivity].
- destruct (pva_fpchain_patch rd rd' X sp (ly_top ly) ch v H4 ltac:(lia) ltac:(lia) H3 HX Hag Hw' Hw0)
    as (ch' & Hc' & Hf').
  exists ch'. right. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact Hc'|].
  eapply Forall_impl; [|exact Hf']. intros r Hr. cbn beta in Hr. lia.
Qed.
(* parse_value's own record (saved ra / s0 at sp0 - 8 / sp0 - 16) pushed on a chain from s0 (YCbq.v achain_push) *)
Lemma pva_chain : forall ly (rd0 rd' : reader) Y sp0 s0 ra ch, achain ly rd0 sp0 s0 ch -> ly_top ly <= 2 ^ 64 ->
  (forall a, sp0 <= a < 2 ^ 64 -> rd' a = rd0 a) -> rdword rd' (sp0 - 8) = Some ra ->
  rdword rd' (sp0 - 16) = Some s0 -> 4096 <= ra -> alloc_ceiling <= sp0 -> sp0 mod 8 = 0 -> Y + 16 <= sp0 ->
  exists ch1, achain ly rd' Y sp0 ch1.
Proof.
intros ly rd0 rd' Y sp0 s0 ra ch Hc Ht Hk H8 H16 Hra Hceil Hal HY.
destruct (Z_lt_le_dec sp0 (ly_top ly - 16)) as [Hlt | Hge].
- exists ((sp0, ra, s0) :: ch). exact (achain_push ly rd0 rd' sp0 s0 ra ch Y Hc Ht Hk H8 H16 Hra Hceil Hal Hlt HY).
- exists []. left. split; [right; left; exact Hge | reflexivity].
Qed.

Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

(* ---- Section hypotheses ---- *)
(* the kit rule: YCbqG's 16-field record at the harness head length (the instance's AR_laws_x_xs) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the frame-area rule's own hypotheses (YGcallMxmn.v aj_stack_malloc_at_xm, Section srule: OWNLOW, SMX verbatim) and
   frame class 0's contract in the m-form (the engine's YGcallMxmn.v astack_malloc_realizes_xm; preset's classes 0, 1,
   3; owner of the frame-class texts) *)
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Hypothesis SMX : forall ly S Hp W mem md cid, ARx ly S Hp W mem md -> 0 <= cid <= 10 ->
  count_cid cid (frames S) < fs_frames cid ->
  exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S') /\ (exists f, S' = set_fs f S) /\
    frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S).
Hypothesis ASM0 : YGcallMxmn.astack_malloc_realizes_xm (fx := fx0) SEGS B ARx 0.
(* the callee text: the skip_ws (lib/A/PRH_FnReader.v tskip_ws_specX, post in fpostWm) *)
Hypothesis SKIPWS : tskip_ws_specX (fx := fx0) (PI := PIB) (PA := PA) B ARx SK.
(* STAND-IN for the unit's PALib binding of B at the program listing, as the other image-B walks take it *)
Hypothesis PAL : PALib (L := B_prog_listing) (PI := PA) B.
(* MARKED image fact, discharged at PI_prog_B: parse_value's entry is its listing slot *)
Hypothesis Hent : SIGMA AS_parse_value = BASE + AF_pv.
(* MARKED image fact, discharged at PI_prog_B: the class-0 frame-area entry is the listing's __asan_stack_malloc_0 *)
Hypothesis Hsm0 : pc_stack_malloc (as_code B) 0 = SIGMA AS___asan_stack_malloc_0.
(* MARKED image fact, discharged at PI_prog_B: the use-after-return flag cell is the word after the shadow-base cell
   (B 0xab700 = 0xab6f8 + 8), the two GOT words lie below that cell pair, apart (0xa2850, 0xa28a8), all in low memory *)
Hypothesis Huarc : as_uar_cell B = VAL (A_OBJ 12) + 8.
Hypothesis Hobjd : VAL (A_OBJ 0) + 8 <= VAL (A_OBJ 1) /\ VAL (A_OBJ 1) + 8 <= VAL (A_OBJ 12) /\
  VAL (A_OBJ 12) + 12 <= kLowMemEnd.
(* MARKED instance fact, discharged at lib/A/CfParamsPreset.v (cf_head = 16, preset source/alloc.c:31): a harness
   block's hidden head holds its 8-byte size word (PRH_Base.v prh_head_wide; PvB_X.v takes it in this spelling) *)
Hypothesis HHEAD : 8 <= cf_head.
(* MARKED image fact, discharged at PI_prog_B: alloc.c's five statics are image bytes, neither the runtime's own
   statics nor errno (FuzzFreeB.v / OwnB.v pal_pst_ok, with YC80x.v's PST_ok) *)
Hypothesis PSTOK : forall a, Exists (in_zr a) PSTX ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* MARKED image fact, discharged at PI_prog_B: no read-only byte is one of alloc.c's statics (S1ImgB.v pst_not_ro_B) *)
Hypothesis RONP : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) PSTX.
(* the two image facts of PvB_A_Home.v, in its spelling: *)
(* MARKED image fact, discharged at PI_prog_B: the image's shadow is mapped in every allocator state
   (img_shadow_vis_cf, lib/Reusable/YGcfAmx2.v, over ARx) *)
Hypothesis pvh_img_vis : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO_B <= a < IMG_TOP_B ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* MARKED image fact, discharged at PI_prog_B: the image's zero-shadow ranges are whole granules *)
Hypothesis pvh_zs_al : forall r, In r (as_zero_shadow B) -> fst r mod 8 = 0 /\ snd r mod 8 = 0.
(* MARKED instance fact, discharged at PI_prog_B (PAImg_prog.v: pa_lo := IMG_LO_B, pa_hi := IMG_TOP_B): the kit's
   per-instance kept_img / kept_at bounds lie inside the B' image box (PvB_A_Home.v PA_BOX, in its spelling) *)
Hypothesis PA_BOX : IMG_LO_B <= @pa_lo _ B_prog_listing PA /\ @pa_hi _ B_prog_listing PA <= IMG_TOP_B.

(* the runner carrying aj_memnorm (= YAkMemnorm.memnorm, by conversion) across each engine stretch: the engine's twin
   (YC1fPx.v paj_run_x_inv at P := memnorm, engine set preset-tree-at-2026-10-29T12-55-44Z.tsv (sha256 7967f42d1cd6; internal record);
   its laws YSRrMemnorm.srr_inv_laws_memnorm_k), as PvB_D.v uses it *)
Let RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_B) (PI := PA) B PSTX ARx LAWS (YAkMemnorm.memnorm SEGS)
  (srr_inv_laws_memnorm_k SEGS).

(* the entry premises, unpacked (PvB_Defs.v pv_pre; PRH_Base.v fpre; YCbqG.v afn_pre_x / astk_ok; PRH_FnParse.v rd_pre);
   HPKS0 / HPK240 are pv_pre's two live-count premises (its last conjuncts): segment A makes no allocator event *)
Ltac pva_unpack HPRE :=
  pose proof HPRE as (HFPRE & HCTX & HUNIV & HCUR & HCH & HQCH & Hq10 & Hv11 & HRDP & HROOMp & HFRB & HMN0 & HPKS0 &
    HPK240 & HCWE0 & HWR0);
  pose proof HFPRE as (HAFN & HRO & Hhi64);
  pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
  pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop);
  pose proof HRDP as (Hfrm0 & Hmuniv & Hruniv1 & Hruniv2 & Hcur0 & Hwin & Hqlo & Hqhi & Hqra & Hsrc & Hhome &
    Hmaxrun & Hnode & Hqv & Htv & Hvwin & HLED0 & Hdmax & Hcntb & Htxc);
  pose proof Hwin as (He0 & He16 & Hetop & Hepres).

(* ---- the state at the frame-area call (after run 1), alignment case c ---- *)
Definition pva_call1 (en : PvEnt) (c : Z) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
  ajournal_x (SK := SK) SEGS B PSTX ARx (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en)
    (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en) [] (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en)
    mem1 md1 0 /\
  getr regs1 2 = w64 (pe_sp en - c - 160) /\ getr regs1 1 = Z_to_bv 64 (BASE + AF_pv_sm_ret) /\
  getr regs1 3 = getr (pe_regs en) 3 /\ getr regs1 4 = getr (pe_regs en) 4 /\
  getr regs1 8 = w64 (pe_sp en) /\ getr regs1 9 = w64 (pe_sp en - c - 160) /\
  getr regs1 19 = getr (pe_regs en) 11 /\ getr regs1 20 = getr (pe_regs en) 10 /\
  getr regs1 23 = w64 SHADOW_OFF /\
  Forall (fun oc => val_mem SEGS (rdW (pe_W en) mem1) (pe_sp en + fst oc) 8
    (bv_unsigned (getr (pe_regs en) (Z_to_bv 5 (snd oc))))) pv_saved /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pe_sp en - 176 <= a < pe_sp en) ->
     aview SEGS (w_H (pe_W en)) mem1 a = aview SEGS (w_H (pe_W en)) (pe_mem en) a) /\
  YStrtodRowX.aj_memnorm SEGS mem1.

Definition pva_E1 (regs : bvmap 5 word) (X : Z) : env :=
  Eimg (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 0; Z_to_bv 64 X]).

Lemma pva_stk : forall en, 176 + ESTACK <= pe_STK en.
Proof.
intros en. assert (HSTKe : pe_STK en = Z.of_nat (S (PjGrammar.MAXD - pe_d en)) * 320 + 16560) by reflexivity.
rewrite HSTKe. assert (ESTACK = 4096) as -> by reflexivity. nia.
Qed.

(* shadow byte k of run 2's end state: the width-1 chunk at offset k of atom 35 (the fake frame's shadow address) *)
Ltac pva_shb HS U35 :=
  lazymatch type of HS with st_ok _ ?E ?ssf _ =>
  lazymatch goal with |- val_mem _ _ (_ + Z.of_nat ?k) 1 _ =>
    let o := eval vm_compute in (Z.of_nat k) in
    change (Z.of_nat k) with o;
    let c := eval vm_compute in (pva_cv (ss_mem ssf) 35%nat o 1) in
    lazymatch c with Some (YP09.mkChunk _ (CVal _ ?e)) =>
      refine (pva_byte_v E _ _ _ 35%nat o e _ _ _ HS _ U35 _ _);
      [vm_compute; reflexivity | lia | rewrite U_SLit; vm_compute; reflexivity]
    end end end.
(* the 13 saved slots of run 1's end state: slot (off, r) is the chunk at off + c of atom 34 (= sp0 - c), holding
   the entry register r (atom r of the run's environment) *)
Ltac pva_saved_tac HS U34 Esav :=
  rewrite Forall_forall; intros [off r] Hin; cbn [fst snd];
  unfold pv_saved in Hin; cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [ injection Hin as <- <-;
      lazymatch type of U34 with bv_unsigned (ew ?E ?j) = _ - ?c =>
      lazymatch goal with |- val_mem _ _ (_ + ?o) 8 (bv_unsigned (getr _ (Z_to_bv 5 ?rr))) =>
        let n := eval vm_compute in (Z.to_nat rr) in
        refine (pva_val8 E _ _ _ j (o + c) (SOff n 0) _ _ _ HS _ U34 _
          (Esav n (Z_to_bv 5 rr) ltac:(lia) ltac:(vm_compute; reflexivity)));
        [vm_compute; reflexivity | lia]
      end end
    | ]);
  destruct Hin.

(* ---- run 1: the prologue to the frame-area call ---- *)
Lemma pva_run1 : forall en c (Q : world SEGS -> config -> Prop), pv_pre B ARx en -> (c = 0 \/ c = 16) ->
  pe_sp en mod 32 = c ->
  (forall regs1 mem1 md1, pva_call1 en c regs1 mem1 md1 ->
     SRr SEGS (pe_W en) (mkCfg (@YK11.mkst fx0 regs1 (Z_to_bv 64 (pc_stack_malloc (as_code B) 0)) mem1
       (YK11.seg_rom SEGS)) md1) Q) ->
  SRr SEGS (pe_W en) (cfg_at (fx := fx0) SEGS (SIGMA AS_parse_value) (pe_regs en) (pe_mem en) (pe_md en)) Q.
Proof.
intros en c Q HPRE Hc Hsp32 HK.
pva_unpack HPRE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pva_stk en) as HSTK. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (alx_const SEGS B ARx LAWS _ _ _ _ _ _ HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B PAL), (pal_cell B PAL) in Kgot. rewrite (pal_cell B PAL) in Kcell.
rewrite (pal_got_uar B PAL), Huarc in Kguar. rewrite Huarc in Kuar.
destruct Hobjd as (O01 & O112 & O12lo).
pose proof (pa_val_range (A_OBJ 0)) as RV0. pose proof (pa_val_range (A_OBJ 1)) as RV1.
pose proof (pa_val_range (A_OBJ 12)) as RV12.
set (W := pe_W en) in *. set (regs := pe_regs en) in *. set (mem := pe_mem en) in *. set (md := pe_md en) in *.
set (ly := pe_ly en) in *. set (S := pe_S en) in *. set (Hp := pe_Hp en) in *.
set (STK := pe_STK en) in *. set (e := pe_e en) in *. set (FP := pe_FP en) in *.
assert (Esp : pe_sp en = spZ regs) by reflexivity. rewrite Esp in *. set (sp0 := spZ regs) in *.
assert (Hsp_lo : 2 ^ 46 + 176 <= sp0) by lia.
assert (Hsp_hi : sp0 <= 2 ^ 47) by lia.
assert (HX : 0 <= sp0 - c < 2 ^ 64) by lia.
(* the journal at the entry, widened by the window *)
pose proof (ajournal_x_init_W (SK := SK) SEGS B PSTX ARx STK e FP ly S Hp W regs mem md (pe_ch en) HAFN Hwin) as HJ.
(* the environment *)
remember (pva_E1 regs (sp0 - c)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold pva_E1; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 0; Z_to_bv 64 (sp0 - c)]) n)
  by (intros n Hn; subst E; unfold pva_E1; apply Eimg_low; exact Hn).
assert (Er : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn Hr. rewrite EL by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n r Hr). }
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (sp0 - c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (U34 : bv_unsigned (ew E 34) = sp0 - c) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U0 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (apply HEI; unfold A_TEXT, A_OBJ, A_LIM; lia).
assert (U1 : bv_unsigned (ew E (A_OBJ 1)) = VAL (A_OBJ 1)) by (apply HEI; unfold A_TEXT, A_OBJ, A_LIM; lia).
assert (U12 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply HEI; unfold A_TEXT, A_OBJ, A_LIM; lia).
assert (Esav : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  U E (SOff n 0) = bv_unsigned (getr regs r)).
{ intros n r Hn Hr. rewrite U_SOff, (Er n r Hn Hr), Z.add_0_r. apply zcanon_id.
  pose proof (bv_unsigned_in_range _ (getr regs r)) as Hb. unfold M64. exact Hb. }
assert (HS : st_ok_pi SEGS VAL E (pva_ss1 c)
  (restrict (w_H W) (@YK11.mkst fx0 regs (Z_to_bv 64 (BASE + AF_pv)) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pva_ss1. apply pa_entry_st_ok_full.
  - apply regs_ok_pin; [rewrite HE; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
    cbn [sv_denot]. rewrite U34. replace (sp0 - c + c) with sp0 by lia. unfold sp0, spZ.
    rewrite Z_to_bv_bv_unsigned. reflexivity.
  - destruct Hc as [-> | ->]; vm_compute; reflexivity.
  - unfold pva_regions1, got_regionP. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U34. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    + rewrite U0. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite U12, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
        | change (Z.of_N 8) with 8; lia |].
      match goal with |- val_mem _ _ ?x _ _ => replace x with (VAL (A_OBJ 0)) by lia end.
      exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    + rewrite U1. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff (A_OBJ 12) 8) (VAL (A_OBJ 12) + 8));
        [cbn [sv_denot]; rewrite U12; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
        | change (Z.of_N 8) with 8; lia |].
      match goal with |- val_mem _ _ ?x _ _ => replace x with (VAL (A_OBJ 1)) by lia end.
      exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
    + rewrite U12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 32 0) SHADOW_OFF);
          [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SHADOW_OFF; lia | change (Z.of_N 8) with 8; lia |].
        match goal with |- val_mem _ _ ?x _ _ => replace x with (VAL (A_OBJ 12)) by lia end.
        exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
      * apply (chunk_ok_val SEGS E _ _ 8 4 (SLit 1) 1);
          [reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | change (Z.of_N 4) with 4; lia |].
        exact (pva_val_of_rd32 (w_H W) mem _ _ Kuar).
  - apply pairwise_disjoint_of_extents. unfold pva_regions1, got_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U34, U0, U1, U12.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok pva_facts1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U34, U32. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
    replace ((sp0 - c) mod 32) with 0; [| rewrite Zminus_mod, Hsp32; destruct Hc as [-> | ->]; reflexivity].
    unfold SHADOW_OFF. repeat split; lia. }
assert (SHOK : sh_ok SEGS PVA_Bx [] E (mrestrict (w_H W) mem)) by (constructor).
clear HE EL.
(* the entry memory's normal form, pv_pre's memnorm conjunct (HMN0), in the runner's spelling (conversion) *)
assert (HPM : YAkMemnorm.memnorm SEGS mem) by exact HMN0.
unfold cfg_at. rewrite Hent. change (w64 (BASE + AF_pv)) with (Z_to_bv 64 (BASE + AF_pv)).
destruct Hc as [-> | ->].
all: paj_run_tok_x_inv RUN HS HJ SHOK HPM PVA_Bspan;
  [ intros a (r & Hr & Ha); unfold pva_ss1, pva_regions1, got_regionP in Hr; cbn [ss_mem In] in Hr;
    repeat (destruct Hr as [<- | Hr];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U34 in Ha;
        first [ unfold awr_byte; left; lia | exfalso; lia ] |]);
    destruct Hr
  | ].
all: pmkst HS; rewrite <- Hsm0; apply HK.
all: prreg HS (2%bv : bv 5) R2; prreg HS (1%bv : bv 5) R1; prreg HS (3%bv : bv 5) R3; prreg HS (4%bv : bv 5) R4;
  prreg HS (8%bv : bv 5) R8; prreg HS (9%bv : bv 5) R9; prreg HS (19%bv : bv 5) R19; prreg HS (20%bv : bv 5) R20;
  prreg HS (23%bv : bv 5) R23.
all: unfold pva_call1; rewrite ?Esp.
all: split; [exact HJ|].
all: split; [rewrite R2, U34; unfold w64; f_equal; lia|].
all: split; [rewrite R1; reflexivity|].
all: split; [rewrite R3; exact (Er 3%nat 3%bv ltac:(lia) ltac:(reflexivity))|].
all: split; [rewrite R4; exact (Er 4%nat 4%bv ltac:(lia) ltac:(reflexivity))|].
all: split; [rewrite R8; first [rewrite E34; unfold w64; f_equal; lia | rewrite U34; unfold w64; f_equal; lia]|].
all: split; [rewrite R9, U34; unfold w64; f_equal; lia|].
all: split; [rewrite R19; exact (Er 11%nat 11%bv ltac:(lia) ltac:(reflexivity))|].
all: split; [rewrite R20; exact (Er 10%nat 10%bv ltac:(lia) ltac:(reflexivity))|].
all: split; [rewrite R23, E32; reflexivity|].
all: split; [pva_saved_tac HS U34 Esav|].
all: split; [intros a Ha Hn; apply (pva_aview_of_frame W E _ mem (ms_mem ms) a HFr); [|exact Ha];
  intros (r & Hr & Hwr); unfold pva_ss1, pva_regions1, got_regionP in Hr; cbn [ss_mem In] in Hr;
  repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hwr; rewrite ?U34 in Hwr; lia |]);
  destruct Hr|].
all: exact HPM.
Qed.

(* ---- the state at the skip_ws call (after the frame-area call and run 2) ---- *)
(* what the entry's memory still holds there: the caller's stack from sp0 up, the entry's blocks, the image but the
   runtime's own statics and errno, the entry's fake frames and their shadow *)
Definition pva_keep03 (en : PvEnt) (mem3 : word -> option byte) : Prop :=
  (forall a, pe_sp en <= a < 2 ^ 64 ->
     aview SEGS (w_H (pe_W en)) mem3 a = aview SEGS (w_H (pe_W en)) (pe_mem en) a) /\
  (forall b m i, In (b, m) (ablocks B (pe_ly en) (pe_S en)) -> 0 <= i < req_size m ->
     aview SEGS (w_H (pe_W en)) mem3 (b + i) = aview SEGS (w_H (pe_W en)) (pe_mem en) (b + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H (pe_W en)) mem3 a = aview SEGS (w_H (pe_W en)) (pe_mem en) a) /\
  (forall cid p a, In (cid, p) (frames (pe_S en)) ->
     (in_zr a (frame_rng (pe_ly en) (cid, p)) \/
      in_zr a (shadow_addr (frame_addr (pe_ly en) cid p), fs_frame_bytes cid / 8)) ->
     aview SEGS (w_H (pe_W en)) mem3 a = aview SEGS (w_H (pe_W en)) (pe_mem en) a).

Definition pva_call2 (en : PvEnt) (Y fa fl pos : Z) (S2 : astate) (regs3 : bvmap 5 word)
    (mem3 : word -> option byte) (md3 : Model) : Prop :=
  pe_sp en - 176 <= Y <= pe_sp en - 160 /\ Y mod 32 = 0 /\
  ajournal_x (SK := SK) SEGS B PSTX ARx (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en)
    (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en) [(0, pos)] (pe_ly en) S2 (pe_Hp en) (pe_W en)
    mem3 md3 0 /\
  frames S2 = (0, pos) :: frames (pe_S en) /\ ablocks B (pe_ly en) S2 = ablocks B (pe_ly en) (pe_S en) /\
  blocks_bytes S2 = blocks_bytes (pe_S en) /\ (exists f, S2 = set_fs f (pe_S en)) /\
  fa = frame_addr (pe_ly en) 0 pos /\ fl = flag_addr (pe_ly en) 0 pos /\
  getr regs3 2 = w64 Y /\ getr regs3 1 = Z_to_bv 64 (BASE + AF_pv_skw_ret) /\
  getr regs3 3 = getr (pe_regs en) 3 /\ getr regs3 4 = getr (pe_regs en) 4 /\
  getr regs3 8 = w64 (pe_sp en) /\ getr regs3 9 = w64 Y /\ getr regs3 10 = getr (pe_regs en) 10 /\
  getr regs3 18 = w64 fa /\ getr regs3 26 = w64 fa /\ getr regs3 27 = w64 (SHADOW_OFF + fa / 8) /\
  getr regs3 23 = w64 SHADOW_OFF /\ getr regs3 19 = getr (pe_regs en) 11 /\ getr regs3 20 = getr (pe_regs en) 10 /\
  Forall (fun oc => val_mem SEGS (rdW (pe_W en) mem3) (pe_sp en + fst oc) 8
    (bv_unsigned (getr (pe_regs en) (Z_to_bv 5 (snd oc))))) pv_saved /\
  val_mem SEGS (rdW (pe_W en) mem3) (Y + 48) 8 fa /\
  val_mem SEGS (rdW (pe_W en) mem3) fa 8 PV_MAGIC /\
  val_mem SEGS (rdW (pe_W en) mem3) (fa + 8) 8 (VAL (A_OBJ 2) + PV_DESCR_OFF) /\
  val_mem SEGS (rdW (pe_W en) mem3) (fa + 16) 8 (BASE + AF_pv) /\
  val_mem SEGS (rdW (pe_W en) mem3) (fa + 56) 8 fl /\
  garr8 SEGS (rdW (pe_W en) mem3) (SHADOW_OFF + fa / 8) pv_shadow_live /\
  pva_keep03 en mem3 /\
  YStrtodRowX.aj_memnorm SEGS mem3.

Lemma pva_U_range : forall E e, 0 <= U E e < 2 ^ 64.
Proof. intros E e. unfold U. exact (bv_unsigned_in_range _ (sv_denot E e)). Qed.
(* FuzzMalloc.v (lib/A/Prog) fm_U_add / fm_U_srl *)
Lemma pva_U_add : forall E a b, U E (SAlu ALU_ADD a b) = (U E a + U E b) mod 2 ^ 64.
Proof. intros E a b. rewrite U_SAlu. cbn [zalu_raw]. unfold zcanon, M64. reflexivity. Qed.
Lemma pva_U_srl : forall E a s, 0 <= s < 64 -> U E (SAlu ALU_SRL a (SLit s)) = Z.shiftr (U E a) s.
Proof.
intros E a s Hs. rewrite U_SAlu, U_SLit. cbn [zalu_raw].
rewrite (zcanon_id s) by (unfold M64; lia).
replace (Z.land s 63) with s by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
pose proof (pva_U_range E a) as Ha.
apply zcanon_id. unfold M64. rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)).
split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ (U E a)); [apply Z.div_le_upper_bound; nia | lia].
Qed.
(* a val_mem over the view rides through a change that keeps those bytes' views *)
Lemma pva_val_keep : forall (W W' : world SEGS) m m' a (n : nat) v, val_mem SEGS (rdW W m) a n v ->
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  val_mem SEGS (rdW W' m') a n v.
Proof.
intros W W' m m' a n v Hv Hk k Hkn. rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat k)).
- exact (Hv k Hkn).
- apply Hk. lia.
Qed.
Lemma pva_garr8_keep : forall (W W' : world SEGS) m m' a l, garr8 SEGS (rdW W m) a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  garr8 SEGS (rdW W' m') a l.
Proof.
intros W W' m m' a l Hg Hk j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (pva_val_keep W W' m m' _ 1 _ Hv). intros x Hx. apply Hk. cbn [Z.of_nat] in Hx. lia.
Qed.
(* the cursor rides through a change that keeps its 24 bytes and the text, the cursor off the image *)
Lemma pva_in_keep : forall (W W' : world SEGS) m m' q text len p d tb,
  pj_in_okR SEGS (rdW W m) q text len p d tb ->
  (forall x, q <= x < q + 24 -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  (forall x, text <= x < text + len -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  (forall x, q <= x < q + 24 -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x) ->
  pj_in_okR SEGS (rdW W' m') q text len p d tb.
Proof.
intros W W' m m' q text len p d tb (V1 & V2 & V3 & Hrw & Hq8 & Ht0 & Ht62 & Hp & Hlen & Gt & Hqt & Hd) Kq Kt Hoff.
split; [apply (pva_val_keep W W' m m' q 8 p V1); intros x Hx; apply Kq; cbn in Hx; lia|].
split; [apply (pva_val_keep W W' m m' (q + 8) 8 _ V2); intros x Hx; apply Kq; cbn in Hx; lia|].
split; [apply (pva_val_keep W W' m m' (q + 16) 4 d V3); intros x Hx; apply Kq; cbn in Hx; lia|].
split.
{ intros x Hx. destruct (Hoff x Hx) as [Hx64 Hni].
  apply (pva_wr_keep _ _ x (Hrw x Hx)); [apply (mbyte_of_aview SEGS); apply Kq; exact Hx | exact Hx64 | exact Hni]. }
do 5 (split; [assumption|]).
split; [apply (pva_garr8_keep W W' m m' text tb Gt); intros x Hx; apply Kt; lia|].
split; assumption.
Qed.
(* the ledger rides through a change that keeps alloc.c's statics and every head word, the blocks unchanged *)
Lemma pva_ledger_keep : forall ly S Hp W m ly' S' W' m' Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W m Lam peak cnt fail ran most own -> ablocks B ly' S' = ablocks B ly S ->
  (forall a, Exists (in_zr a) PSTX -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  (forall b n i, In (b, n) (ablocks B ly S) -> 0 <= i < req_size n ->
     aview SEGS (w_H W') m' (b + i) = aview SEGS (w_H W) m (b + i)) ->
  prh_ledger B ly' S' Hp W' m' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W m ly' S' W' m' Lam peak cnt fail ran most own (HG & HN & HF & HP) Eab Kp Kb.
assert (KP : forall a0 (n0 : nat) v0, In (a0, Z.of_nat n0) PSTX -> val_mem SEGS (rdW W m) a0 n0 v0 ->
  val_mem SEGS (rdW W' m') a0 n0 v0).
{ intros a0 n0 v0 Hin Hv. apply (pva_val_keep W W' m m' a0 n0 v0 Hv). intros x Hx. apply Kp.
  apply Exists_exists. exists (a0, Z.of_nat n0). split; [exact Hin|]. unfold in_zr. cbn [fst snd]. lia. }
split; [|split; [exact HN | split; [|exact HP]]].
- destruct HG as (G1 & G2 & G3 & G4 & G5 & (Gm & Gmr) & (Go & Gor) & Hr). unfold prh_glob.
  split; [apply (KP _ _ _ ltac:(unfold prh_pst; cbn [In]; left; reflexivity) G1)|].
  split; [apply (KP _ _ _ ltac:(unfold prh_pst; cbn [In]; right; left; reflexivity) G2)|].
  split; [apply (KP _ _ _ ltac:(unfold prh_pst; cbn [In]; right; right; left; reflexivity) G3)|].
  split; [apply (KP _ _ _ ltac:(unfold prh_pst; cbn [In]; right; right; right; left; reflexivity) G4)|].
  split; [apply (KP _ _ _ ltac:(unfold prh_pst; cbn [In]; right; right; right; right; left; reflexivity) G5)|].
  (* the two #102 statics g_most / g_own_ran_out (prh_pst's sixth and seventh rows) *)
  split; [split; [apply (KP _ _ _ ltac:(unfold prh_pst; cbn [In]; do 5 right; left; reflexivity) Gm) | exact Gmr]|].
  split; [split; [apply (KP _ _ _ ltac:(unfold prh_pst; cbn [In]; do 6 right; left; reflexivity) Go) | exact Gor]|].
  exact Hr.
- rewrite Forall_forall in HF |- *. intros [a k] Hin. destruct (HF (a, k) Hin) as (Hk & Hab & Hhp & Ha16 & Hv).
  cbn [fst snd] in *. split; [exact Hk|]. split; [rewrite Eab; exact Hab|]. split; [exact Hhp|].
  split; [exact Ha16|].
  apply (pva_val_keep W W' m m' _ 8 k Hv). intros x Hx. cbn in Hx.
  replace x with ((a - cf_head) + (x - (a - cf_head))) by lia. apply (Kb _ _ _ Hab).
  unfold req_size. destruct (Z.eqb_spec (k + cf_head) 0); lia.
Qed.
(* blocks_bytes reads the blocks' sizes only (YCbq.v blocks_bytes_bsum) *)
Lemma pva_bb_ab : forall ly S, blocks_bytes S = fold_right (fun b acc => snd b + acc) 0 (ablocks B ly S).
Proof.
intros ly S. unfold blocks_bytes, ablocks, blocks.
induction (st_chunks S) as [|c l IH]; cbn; [reflexivity|].
destruct (is_alloc c); cbn; rewrite IH; reflexivity.
Qed.

(* ---- the frame-area call and run 2 (0x863ec .. the skip_ws call) ---- *)
Lemma pva_mid : forall en c regs1 mem1 md1 (Q : world SEGS -> config -> Prop), pv_pre B ARx en -> (c = 0 \/ c = 16) ->
  pe_sp en mod 32 = c -> pva_call1 en c regs1 mem1 md1 ->
  (forall Y fa fl pos S2 regs3 mem3 md3, pva_call2 en Y fa fl pos S2 regs3 mem3 md3 ->
     SRr SEGS (pe_W en) (mkCfg (@YK11.mkst fx0 regs3 (Z_to_bv 64 (SIGMA AS_skip_ws)) mem3 (YK11.seg_rom SEGS)) md3) Q) ->
  SRr SEGS (pe_W en) (mkCfg (@YK11.mkst fx0 regs1 (Z_to_bv 64 (pc_stack_malloc (as_code B) 0)) mem1
    (YK11.seg_rom SEGS)) md1) Q.
Proof.
intros en c regs1 mem1 md1 Q HPRE Hc Hsp32 HC1 HK.
pva_unpack HPRE.

destruct HC1 as (HJ1 & R2 & R1 & R3 & R4 & R8 & R9 & R19 & R20 & R23 & Hsav1 & K1 & HMN1).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pva_stk en) as HSTK. assert (Hes : ESTACK = 4096) by reflexivity.
set (W := pe_W en) in *. set (regs := pe_regs en) in *. set (mem := pe_mem en) in *. set (md := pe_md en) in *.
set (ly := pe_ly en) in *. set (S := pe_S en) in *. set (Hp := pe_Hp en) in *.
set (STK := pe_STK en) in *. set (e := pe_e en) in *. set (FP := pe_FP en) in *.
assert (Esp : pe_sp en = spZ regs) by reflexivity. rewrite Esp in *. set (sp0 := spZ regs) in *.
assert (HYv : sp0 - c - 160 = sp0 - c - 160) by reflexivity.
set (Y := sp0 - c - 160) in *.
assert (HYb : sp0 - 176 <= Y <= sp0 - 160) by (unfold Y; destruct Hc as [-> | ->]; lia).
assert (HY32 : Y mod 32 = 0) by (unfold Y; destruct Hc as [-> | ->]; lia).
assert (Hsp_lo : alloc_ceiling + 4272 <= sp0) by lia.
assert (Hcnt : count_cid 0 (frames S) < fs_frames 0).
{ pose proof (pva_count_le 0 (frames S)) as Hc0. clear -Hc0 HFRB. clearbody S.
  rewrite Nat2Z.inj_succ in HFRB. pose proof (Nat2Z.is_nonneg (PjGrammar.MAXD - pe_d en)) as Hn0.
  lia. }
assert (HspY : spZ regs1 = sp0 + e + (Y - (sp0 + e))).
{ unfold spZ at 1. rewrite R2. rewrite unsigned_lit_small by lia. lia. }
eapply SRr_bind.
{ eapply (YGcallMxmn.aj_stack_malloc_at_xm (SK := SK) SEGS B PSTX ARx LAWS (@pa_segs_low _ B_prog_listing PA)
    (pal_env B PAL) OWNLOW SMX 0 ASM0 ltac:(lia) W regs1 mem1 (STK + e) (sp0 + e) FP ly S Hp W mem md [] ly S Hp md1 0
    (Y - (sp0 + e)) (Z_to_bv 64 (BASE + AF_pv_sm_ret)) HJ1).
  - exact HspY.
  - lia.
  - lia.
  - lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PA)); [unfold AF_pv_sm_ret; lia | reflexivity].
  - exact Hcnt. }
cbv beta. intros W2 c2 _ (EW2 & S2 & regs2 & mem2 & md2 & pos & Ec2 & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hfresh &
  Hnev & Hbb & Hz & Hflag & Hfpres & Hkept & HJcall & HfS2 & HKM2).
subst W2 c2.
assert (Efb : fs_frame_bytes 0 = 64) by reflexivity.
rewrite Efb in Hz, Hflag, Hfpres.
pose proof (ajx_ar HJ2) as HAR2. pose proof (ajx_ly HJ2) as Hly2. pose proof (ajx_secs HJ2) as Hsecs2.
pose proof (ajx_wle HJ2) as Hwle2. pose proof (ajx_io HJ2) as Hio2. pose proof (ajx_frs HJ2) as Hfrs2'.
pose proof (ajx_nev HJ2) as Hnev2. pose proof (ajx_k HJ2) as Hk2. pose proof (ajx_hi HJ2) as J1.
pose proof (ajx_blk HJ2) as J2. pose proof (ajx_img HJ2) as J3. pose proof (ajx_frm HJ2) as J4.
pose proof (ajx_gone HJ2) as Jgone. pose proof (ajx_pres HJ2) as Hpres2. pose proof (ajx_stk HJ2) as Hstk2.
pose proof (ajx_extra HJ2) as J5. pose proof (ajx_qt HJ2) as HQT2.
assert (HinF : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS ly S2 Hp W mem2 md2 0 pos HAR2 HinF) as (Hfa0 & Hfac & Hfapp).
destruct (alx_frames SEGS B ARx LAWS ly S2 Hp W mem2 md2 0 pos HAR2 HinF) as (Hfal32 & _ & Hfbytes & Hfsh).
rewrite Efb in Hfac, Hfapp, Hfbytes, Hfsh.
remember (frame_addr ly 0 pos) as fa eqn:Efa.
remember (flag_addr ly 0 pos) as fl eqn:Efl.
set (sh := SHADOW_OFF + fa / 8) in *.
assert (Esh : shadow_addr fa = sh) by reflexivity.
assert (Hshpres : forall i, 0 <= i < 8 -> apresent (w_H W) mem2 (sh + i)).
{ intros i Hi. rewrite <- Esh. exact (proj1 (Hfsh i ltac:(cbn; lia))). }
assert (Hfa47 : fa + 64 <= alloc_ceiling) by exact Hfac.
assert (Hsh_rng : SHADOW_OFF <= sh /\ sh + 8 <= kHighShadowEnd).
{ unfold sh. split; [pose proof (Z.div_pos fa 8 ltac:(lia) ltac:(lia)); lia|]. rewrite C2. unfold SHADOW_OFF. lia. }
assert (Hfa_sh : fa + 64 <= sh \/ sh + 8 <= fa).
{ destruct Hfapp as (Hf4 & [HL | (HH1 & HH2)]); [left | right]; unfold sh, kLowShadowBeg, SHADOW_OFF in *; rewrite ?C3 in *; lia. }
(* registers kept by the call *)
assert (P : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) by exact HP2.
(* the environment of run 2 *)
remember (Eimg (Ereg regs2 [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 0; Z_to_bv 64 fa; Z_to_bv 64 sh])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat ->
  ew E n = ew (Ereg regs2 [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 0; Z_to_bv 64 fa; Z_to_bv 64 sh]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (Er : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r).
{ intros n r Hn Hr. rewrite EL by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs2 _ n r Hr). }
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E34 : ew E 34 = Z_to_bv 64 fa) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 sh) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (E9 : ew E 9 = w64 Y).
{ rewrite (Er 9%nat 9%bv) by first [lia | reflexivity]. etransitivity; [pva_keep P (9%bv : bv 5) 9 | exact R9]. }
assert (U9 : bv_unsigned (ew E 9) = Y) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U34 : bv_unsigned (ew E 34) = fa) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = sh) by (rewrite E35; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
assert (U2b : bv_unsigned (ew E (A_OBJ 2)) = VAL (A_OBJ 2)) by (apply HEI; unfold A_TEXT, A_OBJ, A_LIM; lia).
assert (UT : bv_unsigned (ew E A_TEXT) = BASE) by (apply HEI; unfold A_TEXT, A_LIM; lia).
assert (HS2 : st_ok_pi SEGS VAL E pva_ss2
  (restrict (w_H W) (@YK11.mkst fx0 regs2 (Z_to_bv 64 (BASE + AF_pv_sm_ret)) mem2 (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pva_ss2. apply pa_entry_st_ok_full.
  - unfold pva_regs2. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [rewrite HE; apply regs_ok_Eimg_Ereg
      | intros X; discriminate X
      | cbn [sv_denot]; rewrite U9, Z.add_0_r; etransitivity; [pva_keep P (2%bv : bv 5) 2 | exact R2] ]
      | intros X; discriminate X
      | cbn [sv_denot]; rewrite U34, Z.add_0_r; exact Ha0 ]
      | intros X; discriminate X
      | cbn [sv_denot]; rewrite U32, Z.add_0_r; etransitivity; [pva_keep P (23%bv : bv 5) 23 | exact R23] ].
  - vm_compute; reflexivity.
  - unfold pva_regions2. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres2. lia.
    + rewrite U34. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hfpres. lia.
    + rewrite U35. unfold SHADOW_OFF in *. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hshpres. lia.
  - apply pairwise_disjoint_of_extents. unfold pva_regions2, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U34, U35.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - split; [|split; [exact I|]].
    + cbn [f_atoms atoms_ok pva_facts2]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U32, U34, U35. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SHADOW_OFF in *. repeat split; lia.
    + cbn [f_alias pva_facts2 alias_ok]. split; [|exact I].
      apply bv_eq. change (bv_unsigned (sv_denot E pva_fash) = bv_unsigned (sv_denot E (SOff 35 0))) with
        (U E pva_fash = U E (SOff 35 0)).
      unfold pva_fash. rewrite pva_U_add, pva_U_srl by lia. rewrite !U_SOff, U34, U32, U35, !Z.add_0_r.
      rewrite !zcanon_id by (unfold M64, SHADOW_OFF in *; lia).
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold sh.
      rewrite Z.mod_small by (unfold SHADOW_OFF in *; pose proof (Z.div_pos fa 8 ltac:(lia) ltac:(lia)); lia). lia. }
assert (SHOK2 : sh_ok SEGS PVA_Bx [] E (mrestrict (w_H W) mem2)) by (constructor).
clear HE EL.
(* the frame-area call's return memory is normal (aj_stack_malloc_at_xm's KEEP implication on the call memory's) *)
assert (HPM : YAkMemnorm.memnorm SEGS mem2) by exact (HKM2 HMN1).
change (Z_to_bv 64 (BASE + AF_pv_sm_ret)) with (Z_to_bv 64 (BASE + AF_pv_sm_ret)).
paj_run_tok_x_inv RUN HS2 HJ2 SHOK2 HPM PVA_Bspan2;
  [ intros a (r & Hr & Ha); unfold pva_ss2, pva_regions2 in Hr; cbn [ss_mem In] in Hr;
    destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    [ rewrite U9 in Ha; unfold awr_byte; left; lia
    | rewrite U34 in Ha; unfold awr_byte; right; right; right; exists 0, pos; split; [left; reflexivity|];
      left; unfold in_zr; cbn [fst snd]; rewrite Efb, <- Efa; lia
    | rewrite U35 in Ha; unfold awr_byte; right; right; right; exists 0, pos; split; [left; reflexivity|];
      right; unfold in_zr; cbn [fst snd]; rewrite Efb, <- Efa, Esh; cbn; lia ]
  | ].
pmkst HS2.
prreg HS2 (1%bv : bv 5) Q1. prreg HS2 (2%bv : bv 5) Q2. prreg HS2 (3%bv : bv 5) Q3. prreg HS2 (4%bv : bv 5) Q4.
prreg HS2 (8%bv : bv 5) Q8. prreg HS2 (9%bv : bv 5) Q9. prreg HS2 (10%bv : bv 5) Q10. prreg HS2 (18%bv : bv 5) Q18.
prreg HS2 (19%bv : bv 5) Q19. prreg HS2 (20%bv : bv 5) Q20. prreg HS2 (23%bv : bv 5) Q23. prreg HS2 (26%bv : bv 5) Q26.
prreg HS2 (27%bv : bv 5) Q27.
assert (Esh' : sh = SHADOW_OFF + fa / 8) by reflexivity.
(* what run 2 keeps: every byte off its three write windows *)
assert (K23 : forall a, 0 <= a < 2 ^ 64 -> ~ (Y + 48 <= a < Y + 56) -> ~ (fa <= a < fa + 24) -> ~ (sh <= a < sh + 8) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem2 a).
{ intros a Ha H1 H2 H3. apply (pva_aview_of_frame W E _ mem2 (ms_mem ms) a HFr); [|exact Ha].
  intros (r & Hr & Hwr). unfold pva_ss2, pva_regions2 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hwr;
    [rewrite U9 in Hwr | rewrite U34 in Hwr | rewrite U35 in Hwr]; lia. }
destruct Hkept as (Kc1 & Kc2 & Kc3 & Kc4 & _ & _).
apply (HK Y fa fl pos S2).
unfold pva_call2, pva_keep03. rewrite ?Esp.
split; [exact HYb|]. split; [exact HY32|]. split; [exact HJ2|].
split; [exact Hfrs2|]. split; [exact Eab|]. split; [exact Hbb|]. split; [exact HfS2|].
split; [exact Efa|]. split; [exact Efl|].
split; [rewrite Q2; exact E9|].
split; [rewrite Q1; reflexivity|].
split; [rewrite Q3, (Er 3%nat 3%bv) by first [lia | reflexivity]; etransitivity; [pva_keep P (3%bv : bv 5) 3 | exact R3]|].
split; [rewrite Q4, (Er 4%nat 4%bv) by first [lia | reflexivity]; etransitivity; [pva_keep P (4%bv : bv 5) 4 | exact R4]|].
split; [rewrite Q8, (Er 8%nat 8%bv) by first [lia | reflexivity]; etransitivity; [pva_keep P (8%bv : bv 5) 8 | exact R8]|].
split; [rewrite Q9; exact E9|].
split; [rewrite Q10, (Er 20%nat 20%bv) by first [lia | reflexivity];
  etransitivity; [pva_keep P (20%bv : bv 5) 20 | exact R20]|].
split; [rewrite Q18, E34; reflexivity|].
split; [rewrite Q26, E34; reflexivity|].
split; [rewrite Q27, E35; reflexivity|].
split; [rewrite Q23, E32; reflexivity|].
split; [rewrite Q19, (Er 19%nat 19%bv) by first [lia | reflexivity];
  etransitivity; [pva_keep P (19%bv : bv 5) 19 | exact R19]|].
split; [rewrite Q20, (Er 20%nat 20%bv) by first [lia | reflexivity];
  etransitivity; [pva_keep P (20%bv : bv 5) 20 | exact R20]|].
(* the 13 saved slots, untouched since run 1 (above the callee's window, off run 2's windows) *)
split.
{ rewrite Forall_forall in Hsav1 |- *. intros oc Hin.
  assert (Hoc : -104 <= fst oc <= -8).
  { unfold pv_saved in Hin. cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [fst]; lia |]). destruct Hin. }
  apply (pva_val_keep W W mem1 (ms_mem ms) _ 8 _ (Hsav1 oc Hin)). intros x Hx. change (Z.of_nat 8) with 8 in Hx.
  rewrite (K23 x) by (unfold SHADOW_OFF in *; lia). apply Kc1; lia. }
(* fa at Y + 48, the fake frame's header *)
split; [refine (pva_val8 E _ _ _ 9%nat 48 (SOff 34 0) fa _ _ HS2 _ U9 _ _);
  [vm_compute; reflexivity | lia | rewrite U_SOff, U34, Z.add_0_r; apply zcanon_id; unfold M64; lia]|].
split; [refine (pva_val8 E _ _ _ 34%nat 0 (SLit 1102416563) PV_MAGIC _ _ HS2 _ U34 _ _);
  [vm_compute; reflexivity | lia | rewrite U_SLit; unfold PV_MAGIC; apply zcanon_id; unfold M64; lia]|].
split; [apply pva_val_mod; refine (pva_val8 E _ _ _ 34%nat 8 (SOff (A_OBJ 2) 38879) _ _ _ HS2 _ U34 _ _);
  [vm_compute; reflexivity | lia | rewrite U_SOff, U2b; unfold zcanon, M64, PV_DESCR_OFF; reflexivity]|].
split; [apply pva_val_mod; refine (pva_val8 E _ _ _ 34%nat 16 (SOff A_TEXT 19632) _ _ _ HS2 _ U34 _ _);
  [vm_compute; reflexivity | lia | rewrite U_SOff, UT; unfold zcanon, M64, AF_pv; reflexivity]|].
(* the flag word the frame-area call wrote at fa + 56 *)
split.
{ replace (fa + 56) with (fa + 64 - 8) by lia.
  apply (pva_val_keep W W mem2 (ms_mem ms) _ 8 _ (val_mem_of_rdword SEGS (w_H W) mem2 _ _ Hflag)).
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply K23; lia. }
(* the 8 shadow bytes *)
split.
{ intros j Hj. change (length pv_shadow_live) with 8%nat in Hj.
  do 8 (destruct j as [|j]; [split; [pva_shb HS2 U35 | cbn; lia] |]). lia. }
(* what the entry's state keeps *)
split; [| exact HPM].
try change (pe_W en) with W. try change (pe_mem en) with mem. try change (pe_ly en) with ly. try change (pe_S en) with S.
split; [|split; [|split]].
- intros a Ha. rewrite (K23 a) by (unfold SHADOW_OFF in *; lia). rewrite (Kc1 a) by lia. apply K1; lia.
- intros b m i Hin Hi.
  destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & Hb4 & Hbc & Hbapp & _).
  assert (Hin2 : In (b, m) (ablocks B ly S2)) by (rewrite Eab; exact Hin).
  pose proof (sep_block_frame_x SEGS B ARx LAWS ly S2 Hp W mem2 md2 b m 0 pos HAR2 Hin2 HinF) as Hdj.
  rewrite <- Efa, Efb in Hdj. unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
  rewrite (K23 (b + i)) by (unfold in_app, kLowShadowBeg, SHADOW_OFF in *; rewrite ?C3 in *; lia).
  rewrite (Kc2 b m i Hin Hi) by (intros X; destruct X). apply K1; lia.
- intros a Hi Ho Her.
  pose proof (@pa_segs_low _ B_prog_listing PA a Hi) as Hlow.
  assert (Hnf : ~ (fa <= a < fa + 24)).
  { intros Hfa. destruct (alx_client_img SEGS B ARx LAWS ly S2 Hp W mem2 md2 a HAR2) as (_ & Hni).
    - right. left. exists 0, pos. split; [exact HinF|]. rewrite <- Efa, Efb. lia.
    - exact (Hni Hi). }
  rewrite (K23 a) by (unfold SHADOW_OFF in *; lia). rewrite (Kc3 a Hi Ho Her). apply K1; lia.
- intros cid p a Hin Hr. pose proof Hr as Hr0.
  destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (Hf0 & Hfc & Hfin).
  destruct (alx_frames SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (Hf32 & _).
  pose proof (fs_frame_bytes_nonneg cid) as HF0.
  destruct (in_split _ _ Hin) as (l2 & l3 & Hl).
  pose proof (sep_frames_pos_x SEGS B ARx LAWS ly S2 Hp W mem2 md2 (0, pos) (cid, p) [] l2 l3 HAR2
    ltac:(rewrite Hfrs2, Hl; reflexivity)) as Hdj.
  unfold frame_rng, zdisjoint in Hdj. cbn [fst snd] in Hdj. rewrite <- Efa, Efb in Hdj.
  unfold in_zr, frame_rng, shadow_addr in Hr. cbn [fst snd] in Hr.
  rewrite (K23 a) by (unfold in_app, kLowShadowBeg, SHADOW_OFF in *; rewrite ?C3 in *; destruct Hr; lia).
  rewrite (Kc4 cid p a Hin Hr0) by (intros X; destruct X).
  apply K1; [unfold SHADOW_OFF in *; destruct Hr; lia | unfold SHADOW_OFF in *; destruct Hr; lia].
Qed.

(* ---- the skip_ws call (B 0x86480) to the cut C1 (0x86484) ---- *)
Lemma pva_skw : forall en Y fa fl pos S2 regs3 mem3 md3, pv_pre B ARx en ->
  pva_call2 en Y fa fl pos S2 regs3 mem3 md3 ->
  (forall W2 ms2 md2, pv_at_C1 B ARx en W2 ms2 md2 -> SRr SEGS W2 (mkCfg ms2 md2) (pv_FINK B ARx en)) ->
  SRr SEGS (pe_W en) (mkCfg (@YK11.mkst fx0 regs3 (Z_to_bv 64 (SIGMA AS_skip_ws)) mem3 (YK11.seg_rom SEGS)) md3)
    (pv_FINK B ARx en).
Proof.
intros en Y fa fl pos S2 regs3 mem3 md3 HPRE HC2 HK.
pva_unpack HPRE.
pose proof HROOMp as (Hrl & Hmaxreq & Hlive).
destruct HC2 as (HYb & HY32 & HJ3 & Hfrs2 & Eab & Hbb & HfS2 & Efa & Efl & R2 & R1 & R3 & R4 & R8 & R9 & R10 &
  R18 & R26 & R27 & R23 & R19 & R20 & Hsav3 & V48 & Vmag & Vdesc & Vpc & Vfl & Gsh & (K3s & K3b & K3i & K3f) & HMN3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pva_stk en) as HSTK. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof Hnode as (Hv4096 & Hv8 & Hvrw & Hvz & Hvat & Hvam & Hvown & Hvra).
pose proof Hcur0 as (Vp0 & Vend0 & Vdep0 & Hqrw0 & Hq8 & Htx0 & Htx62 & Hpr & Htblen & Gtb0 & Hqt & Hd32).
pose proof Hsrc as (Hsby & Htx4096 & Htxceil & Htxam & Htxra & Htxhull).
set (W := pe_W en) in *. set (regs := pe_regs en) in *. set (mem := pe_mem en) in *. set (md := pe_md en) in *.
set (ly := pe_ly en) in *. set (S := pe_S en) in *. set (Hp := pe_Hp en) in *.
set (STK := pe_STK en) in *. set (e := pe_e en) in *. set (FP := pe_FP en) in *.
set (q := pe_q en) in *. set (v := pe_v en) in *. set (text := pe_text en) in *. set (len := pe_len en) in *.
set (tb := pe_tb en) in *. set (Lam := pe_Lam en) in *.
assert (Esp : pe_sp en = spZ regs) by reflexivity. rewrite Esp in *. set (sp0 := spZ regs) in *.
assert (EFP : FP = [(q, q + 8); (q + 16, q + 20); (v, v + 56)]) by reflexivity.
assert (Hsp_lo : alloc_ceiling + 4272 <= sp0) by lia.
pose proof HJ3 as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & Hstk3 & _ & _).
assert (HinF : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
assert (Efb : fs_frame_bytes 0 = 64) by reflexivity.
destruct (frames_bounds_x SEGS B ARx LAWS ly S2 Hp W mem3 md3 0 pos HAR3 HinF) as (Hfa0 & Hfac & Hfapp).
rewrite <- Efa in Hfa0, Hfac, Hfapp. rewrite Efb in Hfac, Hfapp.
(* the node lies below alloc_ceiling: rd_pre takes it out of the caller's window *)
assert (Hvlow : v + 56 <= alloc_ceiling).
{ destruct Hvat as [(a0 & k & Hin & H1 & H2) | [(b & m & Hin & _ & H1 & H2) | [(cid & p' & Hin & H1 & H2) | (H1 & H2)]]].
  - pose proof HLED0 as (_ & _ & HF & _). rewrite Forall_forall in HF.
    destruct (HF (a0, k) Hin) as (Hk0 & Hab0 & _). cbn [fst snd] in Hk0, Hab0.
    destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab0) as (_ & _ & Hc & _).
    pose proof (@cf_head_nonneg cp). unfold req_size in Hc. destruct (Z.eqb_spec (k + cf_head) 0); lia.
  - destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & _ & Hc & _).
    unfold req_size in Hc. destruct (Z.eqb_spec m 0); lia.
  - destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & Hc & _). lia.
  - exfalso. destruct Hvwin; lia. }
(* ---- the callee's premises at the call state ---- *)
assert (HLED3 : prh_ledger B ly S2 Hp W mem3 Lam (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en)
  (pe_own en)).
{ apply (pva_ledger_keep ly S Hp W mem ly S2 W mem3 Lam _ _ _ _ _ _ HLED0 Eab).
  - intros a Ha. destruct (PSTOK a Ha) as (Hi & Ho & Her). exact (K3i a Hi Ho Her).
  - exact K3b. }
assert (HHOMEab : forall ly' S', ablocks B ly' S' = ablocks B ly S -> prhReader_home B ly' S' Hp Lam text len).
{ intros ly' S' Eab'. destruct Hhome as [Hk | (b & m & Hin & Hnb & Hb1 & Hb2)];
    [left; exact Hk | right; exists b, m; rewrite Eab'; auto]. }
assert (Ktx3 : forall a, text <= a < text + len -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Ha. destruct (pva_home_place B ly S Hp W mem Lam _ _ _ _ _ _ text len HLED0 Hhome a Ha)
    as [(b & m & Hin & Hbm) | (Hi & _ & Ho & Her)].
  - replace a with (b + (a - b)) by lia. apply (K3b b m); [exact Hin | lia].
  - exact (K3i a Hi Ho Her). }
assert (Hqoff : forall x, q <= x < q + 24 -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x).
{ intros x Hx. split; [lia|]. intros Hi. pose proof (@pa_segs_low _ B_prog_listing PA x Hi). lia. }
assert (HCUR3 : pj_in_okR SEGS (rdW W mem3) q text len (pe_p en) (Z.of_nat (pe_d en)) tb).
{ apply (pva_in_keep W W mem mem3 q text len (pe_p en) (Z.of_nat (pe_d en)) tb Hcur0); [| exact Ktx3 | exact Hqoff].
  intros x Hx. apply K3s. lia. }
assert (HSRC3 : src_rd W mem3 text tb).
{ apply (pva_src_rd_at B ARx LAWS pvh_img_vis pvh_zs_al PA_BOX ly S2 Hp W mem3 md3 Lam _ _ _ _ _ _ W mem text tb HAR3 HLED3).
  - rewrite Htblen. exact (HHOMEab ly S2 Eab).
  - exact Hsrc.
  - rewrite Htblen. exact Ktx3. }
assert (HQRA3 : range_addressable (aview SEGS (w_H W) mem3) SHADOW_OFF q 24).
{ intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
  apply (alx_zshadow_byte SEGS B ARx LAWS ly S2 Hp W mem3 md3 x HAR3). lia. }
assert (HRO3 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem3)).
{ intros a Hr Ho Her. rewrite (K3i a (pva_ro_img a Hr) Ho Her). exact (HRO a Hr Ho Her). }
assert (R10q : getr regs3 10 = w64 q) by (rewrite R10; exact Hq10).
assert (HspY3 : spZ regs3 = Y) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
(* the call chain from the callee's sp Y through parse_value's own record *)
assert (Hsaved : forall off r, In (off, r) pv_saved ->
  val_mem SEGS (rdW W mem3) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros off r Hin. rewrite Forall_forall in Hsav3. exact (Hsav3 (off, r) Hin). }
assert (Rs8 : rdword (aview SEGS (w_H W) mem3) (sp0 - 8) = Some (raZ regs)).
{ replace (sp0 - 8) with (sp0 + -8) by lia.
  apply pva_rdword_of_val; [apply (pva_val_lit _ _ _ _ _ (1%bv : bv 5) 1 eq_refl); exact (Hsaved (-8) 1 ltac:(unfold pv_saved; cbn [In]; tauto)) |
    apply bv_unsigned_in_range]. }
assert (Rs16 : rdword (aview SEGS (w_H W) mem3) (sp0 - 16) = Some (s0Z regs)).
{ replace (sp0 - 16) with (sp0 + -16) by lia.
  apply pva_rdword_of_val; [apply (pva_val_lit _ _ _ _ _ (8%bv : bv 5) 8 eq_refl); exact (Hsaved (-16) 8 ltac:(unfold pv_saved; cbn [In]; tauto)) |
    apply bv_unsigned_in_range]. }
destruct (pva_chain ly (aview SEGS (w_H W) mem) (aview SEGS (w_H W) mem3) Y sp0 (s0Z regs) (raZ regs) (pe_ch en) Hch
  ltac:(lia) K3s Rs8 Rs16 Hra4 ltac:(lia) ltac:(lia) ltac:(lia)) as (ch1 & Hch1).
assert (Hsw : 0 <= STK_skip_ws <= 4096) by (vm_compute; split; congruence).
set (KSW := fQmn (PA := PA) mem3 (fun (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world SEGS) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (md' : Model) =>
  (room_live_cf S2 -> room_live_cf S') /\ Hp' = Hp /\ S' = S2 /\ ablocks B ly' S' = ablocks B ly S2 /\
  prh_ledger B ly' S' Hp' W' mem' Lam (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) /\
  pj_in_okR SEGS (rdW W' mem') q text len
    (text + len - Z.of_nat (length (PjGrammar.skip (rest_atR tb text (pe_p en))))) (Z.of_nat (pe_d en)) tb)).
eapply SRr_bind.
{ apply (aj_call_xW SEGS B PSTX ARx LAWS (@pa_segs_low _ _ PA) W regs3 mem3 (SIGMA AS_skip_ws) (STK + e) (sp0 + e) FP
    ly S Hp W mem md [(0, pos)] ly S2 Hp md3 0 STK_skip_ws (sp0 + e - Y) [(q, q + 8)] (Y - (sp0 + e))
    (Z_to_bv 64 (BASE + AF_pv_skw_ret)) ch1 KSW HJ3).
  - unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PA)); [unfold AF_pv_skw_ret; lia | reflexivity].
  - pose proof (@pa_B_ok _ B_prog_listing PA) as HBok. rewrite unsigned_lit_small; unfold AF_pv_skw_ret; lia.
  - replace (sp0 + e + (Y - (sp0 + e))) with Y by lia.
    replace (s0Z regs3) with sp0; [exact Hch1|]. unfold s0Z. rewrite R8. symmetry. apply unsigned_lit_small. lia.
  - intros HAFN3 HWIN3.
    assert (HqY : spZ regs3 <= q) by (unfold spZ; rewrite R2, unsigned_lit_small by lia; lia).
    assert (Hqt3 : q + 24 <= spZ regs3 + (sp0 + e - Y)) by (unfold spZ; rewrite R2, unsigned_lit_small by lia; lia).
    assert (HFP3 : fpre B ARx STK_skip_ws ly S2 Hp W regs3 mem3 md3 ch1).
    { split; [exact HAFN3|]. split; [exact HRO3|].
      split; [unfold spZ; rewrite R2, unsigned_lit_small by lia; lia|].
      (* fpre's float-state conjunct (FRM0-ENTRY): the call's float state is the entry's fx0 (rd_pre's) *)
      split; [|exact Hfrm0].
      (* fpre's return-address bound: the return pc is the jal's own, the listing slot BASE + AF_pv_skw_ret *)
      pose proof (@pa_B_ok _ B_prog_listing PA) as HBok.
      unfold raZ. rewrite R1, unsigned_lit_small by (unfold AF_pv_skw_ret; lia).
      destruct (plookup (@pl_tpi _ PL_prog_B) AF_pv_skw_ret) as [e0|] eqn:Hslot.
      - exact (pva_slot_lt_ceil (PI := PA) AF_pv_skw_ret e0 ltac:(unfold AF_pv_skw_ret; lia) Hslot).
      - vm_compute in Hslot. discriminate Hslot. }
    exact (SKIPWS ly S2 Hp W regs3 mem3 md3 ch1 (sp0 + e - Y) q text len (pe_p en) (Z.of_nat (pe_d en)) tb Lam
      (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) HFP3
      R10q HCUR3 HWIN3 HqY Hqt3 HQRA3 HSRC3 (HHOMEab ly S2 Eab) HLED3).
  - intros a Ha. left. destruct Ha as (r & Hr & Hwr). destruct Hr as [<- | []].
    exists (q, q + 8). split; [first [rewrite EFP | unfold pe_FP]; left; reflexivity | exact Hwr]. }
cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k1 & Ec4 & HJ4 & HJc & HXw & HP4 & HKSW).
subst c4. destruct HKSW as ((Hroom4 & EHp & ES4 & Eab4 & HLED4 & HCUR4) & HKEEP4). subst Hp4.
(* the memory normal form at C1: skip_ws's KEEP implication on the call memory's (pva_call2's last conjunct) *)
assert (HMN4 : YStrtodRowX.aj_memnorm SEGS mem4) by exact (HKEEP4 HMN3).
pose proof HJ4 as (HAR4 & Hly4 & _ & _ & _ & Hfrs4 & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _ & _ & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & M4 & _ & _ & _ & _ & _).
pose proof Hly4 as (_ & _ & _ & _ & _ & EF4 & _ & _ & Etop4 & Eslo4 & Eshi4 & _).
assert (EF : forall c p, frame_addr ly4 c p = frame_addr ly c p) by (intros; unfold frame_addr; rewrite EF4; reflexivity).
assert (EFl : forall c p, flag_addr ly4 c p = flag_addr ly c p) by (intros; unfold flag_addr; rewrite EF4; reflexivity).
assert (HinF4 : In (0, pos) (frames S4)) by (rewrite Hfrs4; left; reflexivity).
(* ---- what skip_ws kept ---- *)
assert (FP1n : forall a, ~ (q <= a < q + 8) -> ~ inFP [(q, q + 8)] a).
{ intros a Ha (r & Hr & Hwr). destruct Hr as [<- | []]. cbn in Hwr. lia. }
assert (KS4 : forall a, sp0 <= a < 2 ^ 64 -> ~ (q <= a < q + 8) ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hq. rewrite <- (K3s a Ha).
  destruct (Z_lt_le_dec a (sp0 + e)) as [Hlt | Hge].
  - apply HXw; [lia | exact (FP1n a Hq)].
  - apply M1; [lia|]. rewrite ?HspY3. lia. }
assert (KB4 : forall b m i, In (b, m) (ablocks B ly S) -> 0 <= i < req_size m ->
  aview SEGS (w_H W4) mem4 (b + i) = aview SEGS (w_H W) mem (b + i)).
{ intros b m i Hin Hi. rewrite <- (K3b b m i Hin Hi).
  destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & _ & Hbc & _).
  apply (M2 b m i); [rewrite Eab; exact Hin | rewrite Eab4, Eab; exact Hin | exact Hi | apply FP1n; lia]. }
assert (KF4 : forall cid p a, In (cid, p) (frames S) ->
  (in_zr a (frame_rng ly (cid, p)) \/ in_zr a (shadow_addr (frame_addr ly cid p), fs_frame_bytes cid / 8)) ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W) mem a).
{ intros cid p a Hin Hr. rewrite <- (K3f cid p a Hin Hr).
  destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (Hf0 & Hfc & _).
  pose proof (fs_frame_bytes_nonneg cid).
  apply (M4 cid p a); [rewrite Hfrs2; right; exact Hin | exact Hr |]. apply FP1n.
  unfold frame_rng, in_zr, shadow_addr in Hr. cbn [fst snd] in Hr. unfold SHADOW_OFF in *.
  destruct Hr as [Hr | Hr]; lia. }
assert (KI4 : forall a, text <= a < text + len -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W) mem a).
{ intros a Ha. destruct (pva_home_place B ly S Hp W mem Lam _ _ _ _ _ _ text len HLED0 Hhome a Ha)
    as [(b & m & Hin & Hbm) | (Hi & Hro & Ho & Her)].
  - replace a with (b + (a - b)) by lia. apply (KB4 b m); [exact Hin | lia].
  - rewrite <- (K3i a Hi Ho Her). apply M3; [exact Hi | exact Ho | exact Her | exact (RONP a Hro) |].
    apply fp_spares_closed. apply sink_closed_pos. repeat constructor. cbn. lia. }
assert (HSAV4 : forall off r, In (off, r) pv_saved ->
  val_mem SEGS (rdW W4 mem4) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros off r Hin.
  assert (Hoff : -104 <= off <= -8).
  { unfold pv_saved in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- _; lia|]). destruct Hin. }
  apply (pva_val_keep W W4 mem3 mem4 _ 8 _ (Hsaved off r Hin)). intros x Hx. cbn in Hx.
  apply HXw; [lia | apply FP1n; lia]. }
(* ---- the cut ---- *)
apply HK. unfold pv_at_C1.
exists regs4, mem4, Y, fa, fl, pos, ly4, S4, (0 + k1).
assert (Q2 : getr regs4 2 = getr regs3 2) by pva_keep HP4 (2%bv : bv 5) 2.
assert (Q3 : getr regs4 3 = getr regs3 3) by pva_keep HP4 (3%bv : bv 5) 3.
assert (Q4 : getr regs4 4 = getr regs3 4) by pva_keep HP4 (4%bv : bv 5) 4.
assert (Q8 : getr regs4 8 = getr regs3 8) by pva_keep HP4 (8%bv : bv 5) 8.
assert (Q9 : getr regs4 9 = getr regs3 9) by pva_keep HP4 (9%bv : bv 5) 9.
assert (Q18 : getr regs4 18 = getr regs3 18) by pva_keep HP4 (18%bv : bv 5) 18.
assert (Q19 : getr regs4 19 = getr regs3 19) by pva_keep HP4 (19%bv : bv 5) 19.
assert (Q20 : getr regs4 20 = getr regs3 20) by pva_keep HP4 (20%bv : bv 5) 20.
assert (Q23 : getr regs4 23 = getr regs3 23) by pva_keep HP4 (23%bv : bv 5) 23.
assert (Q26 : getr regs4 26 = getr regs3 26) by pva_keep HP4 (26%bv : bv 5) 26.
assert (Q27 : getr regs4 27 = getr regs3 27) by pva_keep HP4 (27%bv : bv 5) 27.
split; [reflexivity|].
split.
{ unfold pv_keep_regs. rewrite Q2, Q8, Q18, Q26, Q27, Q23, Q3, Q4.
  split; [exact R2|]. split; [exact R8|]. split; [exact R18|]. split; [exact R26|]. split; [exact R27|].
  split; [exact R23|]. split; [exact R3 | exact R4]. }
split; [rewrite Q9; exact R9|].
split; [rewrite Q19, R19; exact Hv11|].
split; [rewrite Q20, R20; exact Hq10|].
split.
{ (* pv_body *)
  assert (KFA : forall x, fa <= x < fa + 64 -> aview SEGS (w_H W4) mem4 x = aview SEGS (w_H W) mem3 x).
  { intros x Hx. apply (M4 0 pos x HinF); [left; unfold frame_rng, in_zr; cbn [fst snd]; rewrite <- Efa, Efb; lia|].
    apply FP1n. lia. }
  split.
  { split; [exact HYb|]. split; [exact HY32|].
    split; [intros a Ha; apply Hpres4; lia|].
    split; [rewrite Forall_forall; intros [off r] Hin; exact (HSAV4 off r Hin)|].
    split; [apply (pva_val_keep W W4 mem3 mem4 _ 8 _ V48); intros x Hx; cbn in Hx; apply HXw; [lia | apply FP1n; lia]|].
    split; [apply (pva_val_keep W W4 mem3 mem4 _ 8 _ Vmag); intros x Hx; cbn in Hx; apply KFA; lia|].
    split; [apply (pva_val_keep W W4 mem3 mem4 _ 8 _ Vdesc); intros x Hx; cbn in Hx; apply KFA; lia|].
    split; [apply (pva_val_keep W W4 mem3 mem4 _ 8 _ Vpc); intros x Hx; cbn in Hx; apply KFA; lia|].
    split; [apply (pva_val_keep W W4 mem3 mem4 _ 8 _ Vfl); intros x Hx; cbn in Hx; apply KFA; lia|].
    split.
    { intros a Ha. destruct (alx_frames SEGS B ARx LAWS ly4 S4 Hp W4 mem4 md4 0 pos HAR4 HinF4) as (_ & _ & Hfb4 & _).
      rewrite EF, <- Efa, Efb in Hfb4. exact (proj1 (Hfb4 a Ha)). }
    split; [reflexivity|].
    apply (pva_garr8_keep W W4 mem3 mem4 _ _ Gsh). intros x Hx.
    change (Z.of_nat (length pv_shadow_live)) with 8 in Hx.
    apply (M4 0 pos x HinF); [right; unfold in_zr; cbn [fst snd]; rewrite <- Efa, Efb; unfold shadow_addr; lia|].
    apply FP1n. unfold SHADOW_OFF in *. lia. }
  split; [exact HinF4|]. split; [rewrite EF; exact Efa|]. split; [rewrite EFl; exact Efl|].
  split; [exact HJ4|].
  intros a Ha Hnf. apply KS4; [lia|]. intros Hq. apply Hnf. unfold pe_FP. exists (q, q + 8).
  split; [left; reflexivity | cbn; lia]. }
split.
{ (* pv_chain *)
  intros rd' Hrd'.
  destruct HCH as (che & Hche & _).
  assert (Hrd4 : forall a, alloc_ceiling <= a -> rd' a = aview SEGS (w_H W4) mem4 a).
  { intros a Ha. apply Hrd'. change (pe_v en) with v. lia. }
  assert (Hag : forall a, sp0 <= a -> a + 8 <= ly_top ly -> a mod 8 = 0 -> a <> q ->
    rdword rd' a = rdword (aview SEGS (w_H W) mem) a).
  { intros a Ha Htopa Ha8 Haq. apply pva_rdword_ext. intros i Hi.
    rewrite Hrd4 by lia. apply KS4; lia. }
  assert (Hp1 : exists w, rdword rd' q = Some w /\ 4096 <= w < sp0).
  { pose proof HCUR4 as (Vp4 & _ & _ & _ & _ & _ & _ & Hpr4 & _).
    exists (text + len - Z.of_nat (length (PjGrammar.skip (rest_atR tb text (pe_p en))))).
    split; [|lia].
    rewrite (pva_rdword_ext (aview SEGS (w_H W4) mem4) rd' q) by (intros i Hi; apply Hrd4; lia).
    apply pva_rdword_of_val; [exact Vp4 | lia]. }
  assert (Hp0 : exists w0, rdword (aview SEGS (w_H W) mem) q = Some w0 /\ 4096 <= w0).
  { exists (pe_p en). split; [apply pva_rdword_of_val; [exact Vp0 | lia] | lia]. }
  destruct (pva_achain_patch ly (aview SEGS (w_H W) mem) rd' sp0 (s0Z regs) che q Hche Hq8 Hag Hp1 Hp0)
    as (chc & Hchc).
  assert (Rd8 : rdword rd' (sp0 - 8) = Some (raZ regs)).
  { rewrite (pva_rdword_ext (aview SEGS (w_H W4) mem4) rd') by (intros i Hi; apply Hrd4; lia).
    replace (sp0 - 8) with (sp0 + -8) by lia.
    apply pva_rdword_of_val; [apply (pva_val_lit _ _ _ _ _ (1%bv : bv 5) 1 eq_refl); exact (HSAV4 (-8) 1 ltac:(unfold pv_saved; cbn [In]; tauto)) |
      apply bv_unsigned_in_range]. }
  assert (Rd16 : rdword rd' (sp0 - 16) = Some (s0Z regs)).
  { rewrite (pva_rdword_ext (aview SEGS (w_H W4) mem4) rd') by (intros i Hi; apply Hrd4; lia).
    replace (sp0 - 16) with (sp0 + -16) by lia.
    apply pva_rdword_of_val; [apply (pva_val_lit _ _ _ _ _ (8%bv : bv 5) 8 eq_refl); exact (HSAV4 (-16) 8 ltac:(unfold pv_saved; cbn [In]; tauto)) |
      apply bv_unsigned_in_range]. }
  exact (pva_chain ly4 rd' rd' Y sp0 (s0Z regs) (raZ regs) chc (achain_ly_top ly ly4 rd' sp0 (s0Z regs) chc Etop4 Hchc)
    ltac:(lia) (fun a _ => eq_refl) Rd8 Rd16 Hra4 ltac:(lia) ltac:(lia) ltac:(lia)). }
(* the memory normal form at C1, from skip_ws's m-form text (fpostWm's KEEP implication) *)
split; [| exact HMN4].
(* pv_reader0 *)
assert (HBB4 : blocks_bytes S4 = blocks_bytes S) by (rewrite (pva_bb_ab ly4 S4), (pva_bb_ab ly S), Eab4, Eab; reflexivity).
split; [rewrite Hfrs4; reflexivity|].
split; [rewrite Eab4, Eab; reflexivity|].
split; [exact HBB4|].
split.
{ split; [apply Hroom4; destruct HfS2 as (f & ->); apply RL_set_fs; exact Hrl|].
  (* The batch kit's per-event live room: the live list at C1 is the entry's (the frame take is a set_fs, skip_ws keeps S) *)
  split; [exact Hmaxreq|].
  apply (pv_live_evs_keep S S4 _ Hlive). apply (rp_keep_trans _ S2 _).
  - destruct HfS2 as (f & EfS). rewrite EfS. apply rp_keep_set_fs.
  - apply rp_keep_eq. exact ES4. }
split; [exact HCUR4|].
split.
{ apply (pva_src_rd_at B ARx LAWS pvh_img_vis pvh_zs_al PA_BOX ly4 S4 Hp W4 mem4 md4 Lam _ _ _ _ _ _ W mem text tb HAR4 HLED4).
  - rewrite Htblen. apply HHOMEab. rewrite Eab4, Eab. reflexivity.
  - exact Hsrc.
  - rewrite Htblen. exact KI4. }
split; [apply HHOMEab; rewrite Eab4, Eab; reflexivity|].
split.
{ (* the node's bytes *)
  intros a Ha.
  destruct Hvat as [(a0 & k & Hin & H1 & H2) | [(b & m & Hin & _ & H1 & H2) | [(cid & p' & Hin & H1 & H2) | (H1 & H2)]]].
  - pose proof HLED0 as (_ & _ & HF & _). rewrite Forall_forall in HF.
    destruct (HF (a0, k) Hin) as (Hk0 & Hab0 & _). cbn [fst snd] in Hk0, Hab0.
    replace a with ((a0 - cf_head) + (a - (a0 - cf_head))) by lia. apply (KB4 _ (k + cf_head)); [exact Hab0|].
    unfold req_size. destruct (Z.eqb_spec (k + cf_head) 0); lia.
  - replace a with (b + (a - b)) by lia. apply (KB4 b m); [exact Hin|]. unfold req_size. destruct (Z.eqb_spec m 0); lia.
  - apply (KF4 cid p' a Hin). left. unfold frame_rng, in_zr. cbn [fst snd]. lia.
  - exfalso. destruct Hvwin; lia. }
split.
{ (* the node's shadow *)
  destruct Hvat as [(a0 & k & Hin & H1 & H2) | [(b & m & Hin & Hnl & H1 & H2) | [(cid & p' & Hin & H1 & H2) | (H1 & H2)]]].
  - apply (pva_home_shadow B ARx LAWS pvh_img_vis pvh_zs_al PA_BOX ly4 S4 Hp W4 mem4 md4 Lam _ _ _ _ _ _ v 56 HAR4 HLED4
      ltac:(lia)).
    left. left. exists a0, k. auto.
  - apply (pva_home_shadow B ARx LAWS pvh_img_vis pvh_zs_al PA_BOX ly4 S4 Hp W4 mem4 md4 Lam _ _ _ _ _ _ v 56 HAR4 HLED4
      ltac:(lia)).
    right. exists b, m. split; [rewrite Eab4, Eab; exact Hin|]. split; [|lia].
    intros Hb. pose proof HLED0 as (_ & _ & HF & HP). rewrite Forall_forall in HF.
    apply (Permutation_in _ HP) in Hb. apply in_map_iff in Hb as ((a1 & k1') & Eb & Hak). cbn [fst] in Eb.
    destruct (HF (a1, k1') Hak) as (Hk1 & Hab1 & _). cbn [fst snd] in Hk1, Hab1.
    destruct (Z.eq_dec m (k1' + cf_head)) as [Em | Nm].
    + apply Hnl. replace (b + cf_head) with a1 by lia. replace (m - cf_head) with k1' by lia. exact Hak.
    + rewrite Eb in Hab1.
      assert (Hne : (b, m) <> (b, k1' + cf_head)) by (intros X; injection X as X2; exact (Nm X2)).
      pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md b m b (k1' + cf_head) HAR Hin Hab1 Hne) as Hd.
      pose proof (@cf_head_nonneg cp).
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold req_size in Hd.
      destruct (Z.eqb_spec m 0), (Z.eqb_spec (k1' + cf_head) 0); lia.
  - intros x Hx. destruct (Hvra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    rewrite <- Hs. apply (KF4 cid p' (shadow_of_addr SHADOW_OFF x) Hin). right.
    destruct (alx_frames SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (Hf32 & _).
    assert (Hc0 : 0 <= cid).
    { destruct (Z_lt_le_dec cid 0) as [Hn | Hn]; [exfalso | exact Hn].
      assert (HF32 : fs_frame_bytes cid <= 32).
      { unfold fs_frame_bytes. replace cid with (- (- cid)) by lia.
        rewrite Z.shiftl_opp_r, Z.shiftr_div_pow2 by lia.
        assert (H2p : 2 ^ 1 <= 2 ^ (- cid)) by (apply Z.pow_le_mono_r; lia).
        change (2 ^ 1) with 2 in H2p. apply Z.div_le_upper_bound; lia. }
      lia. }
    rewrite (fs_frame_bytes_eq cid Hc0) in H2 |- *.
    pose proof (Z.pow_pos_nonneg 2 cid ltac:(lia) Hc0).
    unfold in_zr, shadow_addr, shadow_of_addr. cbn [fst snd]. remember (2 ^ cid) as P eqn:EP. clear EP. lia.
  - exfalso. destruct Hvwin; lia. }
split; [exact HLED4|].
(* the room at C1 (PvB_Room.v rp_keep): the frame take is a set_fs (rp_keep_set_fs), skip_ws keeps the state
   (the text's S' = S; rp_keep_eq) *)
split.
{ apply (rp_keep_trans _ S2 _).
  - destruct HfS2 as (f & EfS). rewrite EfS. apply rp_keep_set_fs.
  - apply rp_keep_eq. exact ES4. }
(* the hull meters at C1: the frame take and skip_ws leave st_secs as at entry *)
apply YGcfSecsStep.secs_same_of_secs. rewrite ES4. destruct HfS2 as (f & EfS). rewrite EfS. reflexivity.
Qed.

(* ---- THE SEGMENT: the entry state to the cut C1 ---- *)
Lemma pvA_holds : forall en, pv_pre B ARx en ->
  (forall W2 ms2 md2, pv_at_C1 B ARx en W2 ms2 md2 -> SRr SEGS W2 (mkCfg ms2 md2) (pv_FINK B ARx en)) ->
  SRr SEGS (pe_W en) (cfg_at (fx := fx0) SEGS (pa_sigma AS_parse_value) (pe_regs en) (pe_mem en) (pe_md en))
    (pv_FINK B ARx en).
Proof.
intros en HPRE HK.
assert (Hal : pe_sp en mod 16 = 0).
{ pva_unpack HPRE. exact Hal16. }
assert (Hc : pe_sp en mod 32 = 0 \/ pe_sp en mod 32 = 16) by lia.
destruct Hc as [Hc | Hc].
- apply (pva_run1 en 0 _ HPRE (or_introl eq_refl) Hc). intros regs1 mem1 md1 HC1.
  apply (pva_mid en 0 regs1 mem1 md1 _ HPRE (or_introl eq_refl) Hc HC1).
  intros Y fa fl pos S2 regs3 mem3 md3 HC2. exact (pva_skw en Y fa fl pos S2 regs3 mem3 md3 HPRE HC2 HK).
- apply (pva_run1 en 16 _ HPRE (or_intror eq_refl) Hc). intros regs1 mem1 md1 HC1.
  apply (pva_mid en 16 regs1 mem1 md1 _ HPRE (or_intror eq_refl) Hc HC1).
  intros Y fa fl pos S2 regs3 mem3 md3 HC2. exact (pva_skw en Y fa fl pos S2 regs3 mem3 md3 HPRE HC2 HK).
Qed.

End c.
