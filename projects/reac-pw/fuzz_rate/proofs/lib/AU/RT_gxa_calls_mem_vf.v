(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/RT_gxa_calls_mem_vf.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RT_gxa_calls_mem_vf.v at 71994ff034c7, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the Modified-by lines above describe how lib/A/RT_gxa_calls_mem_vf.v was made and quote that file's image-A values; the code below carries image B's values; a numeral in a comment that quotes the donor's text (lib/A/RT_gxa_calls_mem_vf.v keeps its donor's comment text) is kept as lib/A/RT_gxa_calls_mem_vf.v writes it. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_memcpyw I_memcpyw2 I_amemcpy I_memcpy I_memsetw F_memset I_imemset.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RStep.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA.CopyCall.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA.SetCall.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA.AsanFacts.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.I.RecAsanBR.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.I.RecAsanVfBR.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.Img0.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.RT_gxa_mem_Tbl.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.RT_gxa_calls_mem.
Import ListNotations.
Open Scope Z_scope.

Module CJR := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RStep.
Module GXC := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA.CopyCall.
Module GXM := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA.SetCall.
Module GXF := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA.AsanFacts.
Module RTA := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.I.RecAsanBR.
Module RTV := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.I.RecAsanVfBR.
Module I0 := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.Img0.
Module TBL := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.RT_gxa_mem_Tbl.
Module RGM := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.RT_gxa_calls_mem.

Lemma Avf_sym_memcpy : @CJR.sym RTV.N_img_asan_vf 0x21334 = TBL.MC_TRAMP.
Proof. vm_compute. reflexivity. Qed.

Lemma Avf_sym_memset : @CJR.sym RTV.N_img_asan_vf 0x21738 = TBL.MS_TRAMP.
Proof. vm_compute. reflexivity. Qed.

Lemma A_segs : @CJR.img_segs RTA.N_img_asan = I0.rsegs.
Proof. reflexivity. Qed.

Lemma Avf_segs : @CJR.img_segs RTV.N_img_asan_vf = I0.rsegs.
Proof. reflexivity. Qed.

Theorem memcpy_stack_contract_Avf : @GXC.memcpy_stack_contract RTV.N_img_asan_vf RGM.copy_ready.
Proof.
  unfold GXC.memcpy_stack_contract, GXC.memcpy_stack_post.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m src junk SRC LEN DST OV SEPS MI ST G.
  rewrite Avf_sym_memcpy, <- RGM.A_sym_memcpy.
  rewrite Avf_segs in SRC, DST, MI, ST |- *. rewrite <- A_segs in SRC, DST, MI, ST |- *.
  pose proof (RGM.memcpy_stack_contract_A ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
                s9 s10 s11 t3 t4 t5 t6 F fc m src junk SRC LEN DST OV SEPS MI ST G) as H.
  unfold GXC.memcpy_stack_post in H.
  exact H.
Qed.

Lemma copy_ready_intro_vf : forall (m : word -> option byte) sp d s n Ld Ls,
  kHighShadowEnd < sp - GXC.COPY_DEPTH -> sp < 2 ^ 63 -> 0 <= n ->
  (n = 0 \/ d + n <= sp - GXC.COPY_DEPTH \/ sp <= d) ->
  @GXF.pf_rng RTV.N_img_asan_vf m d Ld -> @GXF.pf_rng RTV.N_img_asan_vf m s Ls ->
  @GXF.shadow_rw RTV.N_img_asan_vf m ->
  n <= Ld -> n <= Ls ->
  m2s_cells m -> icells m ->
  RGM.copy_ready m sp d s n.
Proof.
  intros m sp d s n Ld Ls H1 H2 N0 SEPD PD PS SRW HD HS C1 C2.
  unfold GXF.pf_rng, GXF.addressable, GXF.addr_byte in PD, PS. unfold GXF.shadow_rw in SRW.
  rewrite Avf_segs in PD, PS, SRW. rewrite <- A_segs in PD, PS, SRW.
  exact (RGM.copy_ready_intro m sp d s n Ld Ls H1 H2 N0 SEPD PD PS SRW HD HS C1 C2).
Qed.

Theorem memset_stack_contract_Avf : @GXM.memset_stack_contract RTV.N_img_asan_vf RGM.set_ready.
Proof.
  unfold GXM.memset_stack_contract, GXM.memset_stack_post.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m junk DST MI ST G.
  rewrite Avf_sym_memset, <- RGM.A_sym_memset.
  rewrite Avf_segs in DST, MI, ST |- *. rewrite <- A_segs in DST, MI, ST |- *.
  pose proof (RGM.memset_stack_contract_A ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
                s9 s10 s11 t3 t4 t5 t6 F fc m junk DST MI ST G) as H.
  unfold GXM.memset_stack_post in H.
  exact H.
Qed.

Lemma set_ready_intro_vf : forall (m : word -> option byte) sp d n Ld,
  kHighShadowEnd < sp - GXM.SET_DEPTH -> sp < 2 ^ 63 -> 0 <= n ->
  (n = 0 \/ d + n <= sp - GXM.SET_DEPTH \/ sp <= d) ->
  @GXF.pf_rng RTV.N_img_asan_vf m d Ld -> @GXF.shadow_rw RTV.N_img_asan_vf m -> n <= Ld ->
  m2s_cells m -> icells_ms m ->
  RGM.set_ready m sp d n.
Proof.
  intros m sp d n Ld H1 H2 N0 SEPD PD SRW HD C1 C2.
  unfold GXF.pf_rng, GXF.addressable, GXF.addr_byte in PD. unfold GXF.shadow_rw in SRW.
  rewrite Avf_segs in PD, SRW. rewrite <- A_segs in PD, SRW.
  exact (RGM.set_ready_intro m sp d n Ld H1 H2 N0 SEPD PD SRW HD C1 C2).
Qed.
