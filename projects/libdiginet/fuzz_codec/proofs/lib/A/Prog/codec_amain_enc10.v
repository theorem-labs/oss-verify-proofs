(* ENC10 0x82124-0x82138 of the image-A walk of LLVMFuzzerTestOneInput (lib/A/Prog/codec_amain_inv.v seg_enc 10):
     0x82124 ld a0,8(s6)     p
     0x82128 lbu a2,28(s6)   b mod 256 (the dots)
     0x8212c ld a1,88(s1)    &k.bytes = F + 216 (the spill): the segment bytes
     0x82130 ld a3,96(s1)    &k.out = F + 284 (the spill)
     0x82134 jal diginet_counter_encode (0x86608)
     0x82138 j 0x8220c       JOIN *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CPgEncC CodecRo CodecGlobs CPgWalk CPgWalkCall CPgSat.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st codec_amain_lem codec_amain_encl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis IV : img_shadow_vis tfibsegs B.
Hypothesis COUNTER : cdc_counter_specX tfibsegs B MT AM_counter.

Theorem seg_enc10_holds : seg_enc B MT K XM_LIB 10.
Proof.
intros g pos sp1 ops W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & kev & -> & HJ & Hfr & Hk & Hmo & HC &
  (Hops & Hkind & c & k & od & Hcur & Hkat & Henc & Ekind)).
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
pose proof HC as (Hpre & _ & R2 & _).
pose proof Hkat as (_ & Hwf).
pose proof Hwf as (_ & Wp & _ & Wa & Wb & Wc & Wd & Wn & _).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
unfold cfg_at. replace (enc_pc 10) with 0x82124 by reflexivity. change (w64 0x82124) with (Z_to_bv 64 0x82124).
pose proof (enc_start B MT K XM_LIB LAWS TL g pos sp1 ly2 S2 W2 regs2 mem2 md2 kev c k 0x82124 HJ Hfr HC Hcur Hkat) as HS.
remember (am_env g pos c regs2 (enc_ys k)) as E eqn:HEE.
assert (HAE : env_agree 37 (am_env g pos c regs2 (enc_ys k)) E) by (subst E; apply env_agree_refl).
assert (B2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (am_ew_reg g pos c regs2 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. unfold AM_HI in *. lia. }
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W2) mem2)) by apply Forall_nil.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 152 <= a < sp1 + 168) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
cw_keep_j0 HJ HJ0.
cw_run_to cw_awr_stk 0x86608. cw_keep cw_kwr_stk.
destruct (enc_callst B MT K XM_LIB LAWS g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev (enc_ys k) E _ ms _
  HJ0 Hfr HC Hops Hcur Hkat HJ HAE HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; right; right; right; left; reflexivity) KE) as (HCc & Hopsc & Hcurc & Hkatc).
rreg HS (1%bv : bv 5) Gra. rreg HS (10%bv : bv 5) Ga0. rreg HS (11%bv : bv 5) Ga1. rreg HS (12%bv : bv 5) Ga2.
rreg HS (13%bv : bv 5) Ga3.
pose proof Henc as (_ & Hpd & Hrdr & _ & Hko).
pose proof Hrdr as (Ha & Hb & Hc & Hdr & Hlb & _).
assert (E37 : ew E 37 = Z_to_bv 64 (kz_p k)) by (subst E; exact (am_ew_y g pos c regs2 (enc_ys k) 0)).
pose proof Hkatc as ((_ & _ & _ & _ & _ & _ & _ & G40 & _) & _).
assert (E39 : ew E 39 = Z_to_bv 64 (kz_b k)) by (subst E; exact (am_ew_y g pos c regs2 (enc_ys k) 2)).
assert (E33 : ew E 33 = Z_to_bv 64 (FA g pos)) by (subst E; exact (am_ew_F g pos c regs2 (enc_ys k))).
assert (Uspc : spZ (ms_regs ms) = sp1).
{ pose proof HCc as (_ & _ & R2' & _). unfold spZ. rewrite R2'. unfold w64. apply unsigned_lit_small. unfold AM_HI in *. lia. }
destruct (enc_pers B MT K XM_LIB LAWS TL g pos sp1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ kev k od T_counter GM IV HJ Hfr HCc Hpd
  ltac:(apply Z.leb_le; vm_compute; reflexivity) ltac:(apply Z.leb_le; vm_compute; reflexivity)) as (Hpers & Hdisj).
eapply cpw_call; [exact HS | reflexivity | |].
- cbn [ss_pc].
  apply (COUNTER LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 (ms_mem ms)
    _ kev (ms_regs ms) od (kz_p k) (FA g pos + 216) (kz_b k mod 256) (FA g pos + 284) (kz_bytes k) fa5).
  + apply (enc_entry B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ kev T_counter 0x82138 HJ Hfr Hk HCc Gra);
      first [lia | reflexivity | apply Z.leb_le; vm_compute; reflexivity].
  + rewrite Ga0, E37. reflexivity.
  + rewrite Uspc. exact Hpers.
  + rewrite Ga1, E33, unsigned_lit_small by (unfold AM_HI in *; lia). reflexivity.
  + lia.
  + replace (FA g pos + 216) with (FA g pos + 176 + 40) by lia. exact G40.
  + rewrite Hlb. lia.
  + rewrite Uspc, Hlb. pose proof HCc as HCc'. pose proof HJ as (HAR & _).
    apply (sat_main_bytes_rd_n tfibsegs B LAWS ly2 S2 W2 (ms_mem ms) _ sp1 T_counter pos (FA g pos) LLVMF_STK (e_sp0 g) 24
      HAR ltac:(rewrite Hfr; left; reflexivity) EFA Hf64 ltac:(lia) ltac:(lia)
      (am_bs_k B MT K XM_LIB g pos sp1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ HCc')); unfold T_counter, ESTACK in *; lia.
  + split; [apply Z.mod_pos_bound; lia|]. rewrite Ga2, E39, am_zx by lia. reflexivity.
  + rewrite Ga3, E33, unsigned_lit_small by (unfold AM_HI in *; lia). reflexivity.
  + rewrite Uspc. apply (enc_out B MT K XM_LIB LAWS g pos sp1 k ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ kev T_counter HJ Hfr HCc Hkatc Hko);
      first [lia | apply Z.leb_le; vm_compute; reflexivity].
  + exact Hdisj.
  + rewrite Hlb. change (Z.of_nat 24) with 24. left. lia.
- intros W3 c3 Hpost.
  assert (Eenc : DgnLib.counter_spec od (kz_bytes k) (kz_b k mod 256) = enc_kZ k od)
    by (unfold enc_kZ, DgnLib.enc_of_call; rewrite Ekind; reflexivity).
  rewrite Eenc in Hpost.
  apply (amenc_finish B MT K XM_LIB MTL LAWS g pos sp1 ops c k od ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ kev T_counter 0x82138
    W3 c3 HJ Hfr Hk Hmo HCc Hopsc Hcurc Hkatc Henc Gra ltac:(right; vm_compute; reflexivity) Hpost).
Qed.
End b.
End a.
