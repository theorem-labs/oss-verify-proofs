(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 247 of its 266 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe1.v, with its module paths and module names changed; 66 of its 96 lines of code are new or changed and 236 lines of the source are left out. *)
(* The end of an owe() segment of the image-B walk of LLVMFuzzerTestOneInput (lib/AU/Prog/codec_bmain_inv.v):
   from the executor state a segment walk reaches at CHK 0x82dd4 to the cut inv_chk. It is the image-A
   lib/A/Prog/codec_amain_owex.v at image B (ops in s4, the cursor at 184(sp1), the frame's 60 shadow bytes).
   owex_chk takes the start cut's journal facts and mcommon, the final state (st_ok at an env that agrees with the
   start env bm_env below 37, the twelve fixed registers as bm_sregs has them and s4, the cursor region of
   lib/AU/Prog/codec_bmain_st.v still in the state), the bytes mcommon reads kept, the frame's 60 shadow bytes, and
   the record facts at the end; it gives inv_chk through lib/AU/Prog/codec_bmain_st.v's bm_exit and bm_mcut. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CodecRo CodecGlobs CPgWalkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st.
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
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

(* an atom below 37 of an env that agrees with the start env *)
Lemma owex_ew : forall g pos c regs2 ys E n, env_agree 37 (bm_env g pos c regs2 ys) E -> (n < 37)%nat ->
ew E n = ew (bm_env g pos c regs2 ys) n.
Proof. intros g pos c regs2 ys E n [HA _] Hn. exact (HA n Hn). Qed.

Lemma owex_chk : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k0 c ys k' od E ss ms md3,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
  ly2 S2 W2 (ms_mem ms) md3 k0 ->
frames S2 = [(3, pos)] -> 0 <= k0 <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ops_at ops regs2 -> cur_at g sp1 c W2 mem2 ->
env_agree 37 (bm_env g pos c regs2 ys) E ->
st_ok tfibsegs E ss (restrict (w_H W2) ms) -> ss_pc ss = PC_CHK -> ss_resv ss = None ->
bm_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 20%bv = SOff 20 0 -> In bm_cur_region (ss_mem ss) ->
(forall a, bm_keepzone g pos sp1 a -> aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a) ->
(forall i, 0 <= i < 60 ->
 aview tfibsegs (w_H W2) (ms_mem ms) (shadow_addr (FA g pos) + i) = Some (nth (Z.to_nat i) (shm 0) 0)) ->
k_at g pos k' W2 (ms_mem ms) -> rec_okZ k' od -> kz_rc k' = fst (enc_kZ k' od) -> owe_want_okZ k' od ->
SRr tfibsegs W2 (mkCfg ms md3) (inv_chk B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k0 c ys k' od E ss ms md3 HJ Hfr Hk0 HMLE HC Hops Hcur HAG HS Hpc Hrv
  HKR H20 Hcr KE KSH Hkat Hrec Hrc Hwant.
pose proof HS as HS'. rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS Hrv) in HS'.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS Hrv). rewrite Hpc.
apply SRr_ret.
pose proof HC as (_ & Hsp1 & R2 & _).
pose proof Hcur as (Hc & _ & _).
assert (HPerm : Permutation (ablocks B ly2 S2) (ablocks B (e_ly g) (e_S g))).
{ pose proof HC as HP. do 49 (destruct HP as (_ & HP)). exact HP. }
assert (HMC : mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3).
{ assert (HAG35 : env_agree 35 (bm_env g pos c regs2 ys) E).
  { destruct HAG as [HA HD]. split; [intros n Hn; apply HA; lia | exact HD]. }
  eapply (bm_exit B MT K XM_LIB LAWS); [exact HC | exact HJ | exact HAG35 | exact HS' | exact HKR | exact KE | exact KSH | exact HPerm]. }
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3 k0 HJ Hfr HMC)
  as (_ & _ & _ & _ & _ & Hchi & Hclo & _ & Hsp & Hsp0c & Hsp047 & _ & _ & Hn & Hp & Hpn & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
unfold BM_HI in *.
unfold inv_chk. change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 PC_CHK) (ms_mem ms) (seg_rom tfibsegs)) md3)
  with (cfg_at tfibsegs PC_CHK (ms_regs ms) (ms_mem ms) md3).
eapply bm_mcut; [exact HJ | exact Hfr | exact Hk0 | exact HMLE | exact HMC |].
cbv beta. split.
- (* s4 *)
  destruct Hops as (Hops & R20). split; [exact Hops|].
  rewrite (st_ok_restrict_reg tfibsegs _ E ss ms 20%bv HS), H20. cbn [sv_denot].
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (owex_ew g pos c regs2 ys E 20 HAG ltac:(lia)).
  rewrite (bm_ew_reg g pos c regs2 ys 20 20%bv eq_refl). exact R20.
- exists c, k', od. split; [|split; [exact Hkat | split; [exact Hrec | split; [exact Hrc | exact Hwant]]]].
  (* the cursor, from the cursor region's two chunks *)
  pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & HRs & _).
  pose proof (proj1 (Forall_forall _ _) HRs _ Hcr) as HR. cbn [ms_mem restrict] in HR.
  unfold bm_cur_region in HR.
  assert (U2 : bv_unsigned (ew E 2) = sp1).
  { rewrite (owex_ew g pos c regs2 ys E 2 HAG ltac:(lia)), (bm_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2.
    unfold w64. apply unsigned_lit_small. lia. }
  split; [exact Hc|]. split.
  + pose proof (field_of_region E _ 2 sp1 _ 184 200 184 200 184 8%N (SOff 35 0) (e_p g + c) HR U2
      ltac:(left; reflexivity)) as V.
    apply V; [| cbn; lia | cbn; lia].
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (owex_ew g pos c regs2 ys E 35 HAG ltac:(lia)).
    apply bm_ew_CP.
  + pose proof (field_of_region E _ 2 sp1 _ 184 200 184 200 192 8%N (SOff 36 0) (e_n g - c) HR U2
      ltac:(right; left; reflexivity)) as V.
    apply V; [| cbn; lia | cbn; lia].
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (owex_ew g pos c regs2 ys E 36 HAG ltac:(lia)).
    apply bm_ew_CN.
Qed.
End b.
End a.
