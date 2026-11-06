(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC94.v, with its module paths and module names changed; 201 of its 223 lines of code are new or changed and 227 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_rd13.v, with its module paths and module names changed; 75 of its 113 lines of code are new or changed and 185 lines of the source are left out. *)
(* ENC11 0x8281c-0x82834 of the image-B walk of LLVMFuzzerTestOneInput (lib/AU/Prog/codec_bmain_inv.v seg_enc 11):
     0x8281c lbu a0,24(s7)   a mod 256 (device)
     0x82820 lbu a1,28(s7)   b mod 256 (fn)
     0x82824 ld a3,64(s7)    n
     0x82828 ld a2,120(s1)   &k.bytes = F + 232 (the spill): the payload, its first n bytes
     0x8282c ld a4,144(s1)   &k.out = F + 300 (the spill)
     0x82830 jal diginet_sysex_encode (0x85174), which returns to JOIN 0x82834 itself
   No trap edge lies in the range (codec_bmain_encl.v bmenc_no_trap). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require DgnSpec DgnLib.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CPgEncC CPgSat.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgEncU CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkCallU CPgSatU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st codec_bmain_lem codec_bmain_encl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis SYSEX : cdcU_sysex_specX tfibsegs B MT BM_sysex.

Theorem seg_enc11_holds : seg_enc B MT K XM_LIB 11.
Proof.
intros g pos sp1 ops W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & kev & -> & HJ & Hfr & Hk & Hmo & HC &
  (Hops & Hkind & c & k & od & Hcur & Hkat & Henc & Ekind)).
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
pose proof HC as (Hpre & _ & R2 & _).
pose proof Hkat as (_ & Hwf).
pose proof Hwf as (_ & Wp & _ & Wa & Wb & Wc & Wd & Wn & _).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof satU_T_main_fits as Hfit.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
unfold cfg_at. replace (enc_pc 11) with 0x8281c by reflexivity. change (w64 0x8281c) with (Z_to_bv 64 0x8281c).
pose proof (enc_start B MT K XM_LIB LAWS TL g pos sp1 ly2 S2 W2 regs2 mem2 md2 kev c k 0x8281c HJ Hfr HC Hcur Hkat) as HS.
remember (bm_env g pos c regs2 (enc_ys k)) as E eqn:HEE.
assert (HAE : env_agree 37 (bm_env g pos c regs2 (enc_ys k)) E) by (subst E; apply env_agree_refl).
assert (B2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (bm_ew_reg g pos c regs2 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. unfold BM_HI in *. lia. }
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W2) mem2)) by apply Forall_nil.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 184 <= a < sp1 + 200) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
cw_keep_j0 HJ HJ0.
cw_run_to cw_awr_stk 0x85174. cw_keep cw_kwr_stk.
destruct (enc_callst B MT K XM_LIB LAWS g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev (enc_ys k) E _ ms _
  HJ0 Hfr HC Hops Hcur Hkat HJ HAE HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; right; right; right; left; reflexivity) KE) as (HCc & Hopsc & Hcurc & Hkatc).
rreg HS (1%bv : bv 5) Gra. rreg HS (10%bv : bv 5) Ga0. rreg HS (11%bv : bv 5) Ga1. rreg HS (12%bv : bv 5) Ga2. rreg HS (13%bv : bv 5) Ga3. rreg HS (14%bv : bv 5) Ga4.
pose proof Henc as (_ & _ & Hrdr & _ & Hko).
pose proof Hrdr as (Ha & Hb & _ & _ & Hlb & _ & Hnr & _).
pose proof Hkatc as ((_ & _ & _ & _ & _ & _ & _ & G40 & _) & _).
assert (E38 : ew E 38 = Z_to_bv 64 (kz_a k)) by (subst E; exact (bm_ew_y g pos c regs2 (enc_ys k) 1)).
assert (E39 : ew E 39 = Z_to_bv 64 (kz_b k)) by (subst E; exact (bm_ew_y g pos c regs2 (enc_ys k) 2)).
assert (E42 : ew E 42 = Z_to_bv 64 (kz_n k)) by (subst E; exact (bm_ew_y g pos c regs2 (enc_ys k) 5)).
assert (E33 : ew E 33 = Z_to_bv 64 (FA g pos)) by (subst E; exact (bm_ew_F g pos c regs2 (enc_ys k))).
assert (Uspc : spZ (ms_regs ms) = sp1).
{ pose proof HCc as (_ & _ & R2' & _). unfold spZ. rewrite R2'. unfold w64. apply unsigned_lit_small. unfold BM_HI in *. lia. }
set (bs := firstn (Z.to_nat (kz_n k)) (kz_bytes k)).
assert (Lbs : length bs = Z.to_nat (kz_n k)) by (unfold bs; rewrite length_firstn, Hlb; lia).
assert (Gbs : garr8 tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (FA g pos + 232) bs).
{ intros j Hj. rewrite Lbs in Hj.
  assert (Hnth : nth j bs 0 = nth j (kz_bytes k) 0).
  { unfold bs. replace (nth j (kz_bytes k) 0) with
      (nth j (firstn (Z.to_nat (kz_n k)) (kz_bytes k) ++ skipn (Z.to_nat (kz_n k)) (kz_bytes k)) 0)
      by (rewrite firstn_skipn; reflexivity).
    rewrite app_nth1; [reflexivity | rewrite length_firstn, Hlb; lia]. }
  rewrite Hnth. replace (FA g pos + 232) with (FA g pos + 192 + 40) by lia. apply G40. rewrite Hlb. lia. }
eapply cpw_call; [exact HS | reflexivity | |].
- cbn [ss_pc].
  apply (SYSEX LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 (ms_mem ms)
    _ kev (ms_regs ms) (kz_a k mod 256) (kz_b k mod 256) (FA g pos + 232) (kz_n k) (FA g pos + 300) bs fa5).
  + apply (enc_entry B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ kev TB_sysex 0x82834 HJ Hfr Hk HCc Gra);
      first [lia | reflexivity | apply Z.leb_le; vm_compute; reflexivity].
  + split; [apply Z.mod_pos_bound; lia|]. rewrite Ga0, E38, bm_zx by lia. reflexivity.
  + split; [apply Z.mod_pos_bound; lia|]. rewrite Ga1, E39, bm_zx by lia. reflexivity.
  + rewrite Ga2, E33, unsigned_lit_small by (unfold BM_HI in *; lia). reflexivity.
  + rewrite Ga3, E42. reflexivity.
  + rewrite Lbs. lia.
  + lia.
  + rewrite Ga4, E33, unsigned_lit_small by (unfold BM_HI in *; lia). reflexivity.
  + exact (enc_out_al _ Hf64).
  + intros Hn0. split; [lia|]. split; [exact Gbs|]. split; [|left; lia].
    rewrite Uspc. pose proof HCc as HCc'. pose proof HJ as (HAR & _).
    apply (satU_main_bytes_rd_n tfibsegs B LAWS ly2 S2 W2 (ms_mem ms) _ sp1 TB_sysex pos (FA g pos) LLVMF_STK (e_sp0 g) (kz_n k)
      HAR ltac:(rewrite Hfr; left; reflexivity) EFA Hf64 ltac:(lia) ltac:(lia)
      (bm_bs_k B MT K XM_LIB g pos sp1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ HCc')); first [lia | pose proof satU_T_main_sysex as HTT; lia].
  + rewrite Uspc. apply (enc_out B MT K XM_LIB LAWS g pos sp1 k ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ kev TB_sysex HJ Hfr HCc Hkatc Hko);
      first [lia | apply Z.leb_le; vm_compute; reflexivity].
- intros W3 c3 Hpost.
  assert (Eenc : DgnLib.sysex_spec (kz_a k mod 256) (kz_b k mod 256) bs = enc_kZ k od)
    by (unfold bs; unfold enc_kZ, DgnLib.enc_of_call; rewrite Ekind; reflexivity).
  rewrite Eenc in Hpost.
  apply (bmenc_finish B MT K XM_LIB MTL LAWS g pos sp1 ops c k od ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ kev TB_sysex 0x82834
    W3 c3 HJ Hfr Hk Hmo HCc Hopsc Hcurc Hkatc Henc Gra ltac:(left; reflexivity) Hpost).
Qed.
End b.
End a.
