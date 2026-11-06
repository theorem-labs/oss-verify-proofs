(* ENC4 0x8213c-0x82148 of the image-A walk of LLVMFuzzerTestOneInput (lib/A/Prog/codec_amain_inv.v seg_enc 4):
     0x8213c lw a0,36(s6)    delta
     0x82140 ld a1,96(s1)    &k.out = F + 284 (the spill)
     0x82144 jal diginet_jog_encode (0x85190)
     0x82148 j 0x8220c       JOIN *)
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
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis JOG : cdc_jog_specX tfibsegs B MT AM_jog.

Theorem seg_enc4_holds : seg_enc B MT K XM_LIB 4.
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
unfold cfg_at. replace (enc_pc 4) with 0x8213c by reflexivity. change (w64 0x8213c) with (Z_to_bv 64 0x8213c).
pose proof (enc_start B MT K XM_LIB LAWS TL g pos sp1 ly2 S2 W2 regs2 mem2 md2 kev c k 0x8213c HJ Hfr HC Hcur Hkat) as HS.
remember (am_env g pos c regs2 (enc_ys k)) as E eqn:HEE.
assert (HAE : env_agree 37 (am_env g pos c regs2 (enc_ys k)) E) by (subst E; apply env_agree_refl).
assert (B2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (am_ew_reg g pos c regs2 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. unfold AM_HI in *. lia. }
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W2) mem2)) by apply Forall_nil.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 152 <= a < sp1 + 168) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
cw_keep_j0 HJ HJ0.
cw_run_to cw_awr_stk 0x85190. cw_keep cw_kwr_stk.
destruct (enc_callst B MT K XM_LIB LAWS g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev (enc_ys k) E _ ms _
  HJ0 Hfr HC Hops Hcur Hkat HJ HAE HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; right; right; right; left; reflexivity) KE) as (HCc & Hopsc & Hcurc & Hkatc).
rreg HS (1%bv : bv 5) R1. rreg HS (2%bv : bv 5) R2c. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4.
rreg HS (10%bv : bv 5) R10. rreg HS (11%bv : bv 5) R11.
pose proof Henc as (_ & _ & Hrdr & _ & Hko).
pose proof Hrdr as (_ & _ & _ & Hdr & _).
assert (E41 : ew E 41 = Z_to_bv 64 (kz_delta k mod 2 ^ 32)) by (subst E; exact (am_ew_y g pos c regs2 (enc_ys k) 4)).
assert (E33 : ew E 33 = Z_to_bv 64 (FA g pos)) by (subst E; exact (am_ew_F g pos c regs2 (enc_ys k))).
pose proof (Z.mod_pos_bound (kz_delta k) (2 ^ 32) ltac:(lia)) as Md.
assert (Uspc : spZ (ms_regs ms) = sp1).
{ pose proof HCc as (_ & _ & R2' & _). unfold spZ. rewrite R2'. unfold w64. apply unsigned_lit_small. unfold AM_HI in *. lia. }
eapply cpw_call; [exact HS | reflexivity | |].
- cbn [ss_pc].
  apply (JOG LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 (ms_mem ms)
    _ kev (ms_regs ms) (kz_delta k) (FA g pos + 284) fa5).
  + apply (enc_entry B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ kev T_jog 0x82148 HJ Hfr Hk HCc R1);
      first [lia | reflexivity | apply Z.leb_le; vm_compute; reflexivity].
  + split; [exact Hdr|]. rewrite R10, E41, am_sx32 by lia. rewrite am_s32_mod by lia. reflexivity.
  + rewrite R11, E33, unsigned_lit_small by (unfold AM_HI in *; lia). reflexivity.
  + rewrite Uspc. apply (enc_out B MT K XM_LIB LAWS g pos sp1 k ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ kev T_jog HJ Hfr HCc Hkatc Hko);
      first [lia | apply Z.leb_le; vm_compute; reflexivity].
- intros W3 c3 Hpost.
  assert (Eenc : DgnLib.jog_spec (kz_delta k) = enc_kZ k od) by (unfold enc_kZ, DgnLib.enc_of_call; rewrite Ekind; reflexivity).
  rewrite Eenc in Hpost.
  apply (amenc_finish B MT K XM_LIB MTL LAWS g pos sp1 ops c k od ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ kev T_jog 0x82148
    W3 c3 HJ Hfr Hk Hmo HCc Hopsc Hcurc Hkatc Henc R1 ltac:(right; vm_compute; reflexivity) Hpost).
Qed.
End b.
End a.
