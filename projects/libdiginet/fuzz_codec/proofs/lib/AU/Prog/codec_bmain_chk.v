(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC94.v, with its module paths and module names changed; 201 of its 223 lines of code are new or changed and 227 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_rd13.v, with its module paths, module names and addresses changed; 339 of its 376 lines of code are new or changed and 186 lines of the source are left out. *)
(* Segment CHK of the image-B walk of LLVMFuzzerTestOneInput (lib/AU/Prog/codec_bmain_inv.v seg_chk),
   0x82dd4-0x82df0, to LATCH 0x82df4:
     0x82dd4 mv a0,s7; jal check_refusal (0x84bc4, returns to 0x82ddc)
     0x82ddc mv a0,s7; jal check_range (0x84c84, returns to 0x82de4)
     0x82de4 lw a0,72(s7) (k.rc); bnez a0 -> 0x82df4
     0x82dec mv a0,s7; jal check_bytes (0x84d40, returns to 0x82df4)
   It is the image-A segment (lib/A/Prog/codec_amain_chk.v) at image B: k = F + 192 in s7, image B's entries
   and contracts (lib/AU/Prog/CPgChkU.v, which ask for the record pointer 8-aligned: F is 64-aligned).
   No instrumented check (k.rc is at a constant offset of the frame), and no UBSan trap edge lies in the range
   (bmchk_no_trap). Between the calls the cut is chk_at: the record k and the cursor fixed, k marked usable. Each
   run of the engine (the argument move and the `jal`, or the load and the branch) starts from an ENC-shaped state
   (lib/AU/Prog/codec_bmain_encl.v enc_start) or a reader-shaped one with k.rc as atom 37
   (lib/AU/Prog/codec_bmain_rdlib.v rd_start), writes at most the cursor window, and the cut facts at its stop come
   from codec_bmain_encl.v's enc_callst. Each call goes through the callee's image-B contract: its premises at the
   entry (enc_entry; chk_rd: k's 184 bytes readable and marked usable) and the cut facts back at the return from
   its post (chk_call, on codec_bmain_headl.v's bm_call_kept_x and codec_bmain_encl.v's k_at_kept; the three
   checks write nothing, cno_wr). The record premises of the three contracts are lib/AU/Prog/codec_bmain_lem.v's
   bmain_chk_facts. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CPgSat.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkCallU CPgSatU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st codec_bmain_lem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_headl codec_bmain_rdlib codec_bmain_encl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ================================ no trap edge in the segment ================================ *)
Lemma bmchk_no_trap :
  forallb (fun a => negb ((PC_CHK <=? a) && (a <? PC_LATCH))) (bm_trap_taken ++ bm_trap_fall) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================ arithmetic ================================ *)
(* the record pointer k = F + 192 is 8-aligned *)
Lemma chk_k_al : forall F, F mod 64 = 0 -> (F + 192) mod 8 = 0.
Proof.
intros F H. pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
replace (64 * (F / 64) + 192) with ((8 * (F / 64) + 24) * 8) by lia. apply Z_mod_mult.
Qed.

(* a 32-bit field read back from its value modulo 2 ^ 32 *)
Lemma chk_rc0 : forall r, - 2 ^ 31 <= r < 2 ^ 31 -> (r mod 2 ^ 32 = 0 <-> r = 0).
Proof.
intros r Hr. pose proof (Z.div_mod r (2 ^ 32) ltac:(lia)) as D.
pose proof (Z.mod_pos_bound r (2 ^ 32) ltac:(lia)) as M. split; intros H; [lia|]. subst r. reflexivity.
Qed.

(* the chunk of k.rc (4 bytes at k + 72 = F + 264) as atom 37 *)
Definition chk_rc_chunk : YP09.chunk := YP09.mkChunk 264 (CVal 4 (SOff 37 0)).

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
Hypothesis ACR : cdcU_check_refusal_specX tfibsegs B MT BM_check_refusal.
Hypothesis ACG : cdcU_check_range_specX tfibsegs B MT BM_check_range.
Hypothesis ACB : cdcU_check_bytes_specX tfibsegs B MT BM_check_bytes.

(* the cut inside CHK: at pc, the pass counter, the cursor at c and the record k; k marked usable *)
Definition chk_at (g : ectx) (pos sp1 ops c : Z) (k : kcallZ) (pc : Z) : world tfibsegs -> config -> Prop :=
mcut B MT K XM_LIB g pos sp1 0 pc (fun _ _ W2 regs2 mem2 _ =>
  ops_at ops regs2 /\ cur_at g sp1 c W2 mem2 /\ k_at g pos k W2 mem2).

(* ================================ the executor states ================================ *)
(* the cut chk_at at the stop of a run that wrote at most the cursor window *)
Lemma chk_stop_at : forall g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev ys E ss ms md3,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kev ->
frames S2 = [(3, pos)] -> 0 <= kev <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 -> ops_at ops regs2 -> cur_at g sp1 c W2 mem2 ->
k_at g pos k W2 mem2 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2
  (ms_mem ms) md3 kev ->
env_agree 37 (bm_env g pos c regs2 ys) E ->
st_ok tfibsegs E ss (restrict (w_H W2) ms) -> ss_resv ss = None ->
bm_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 20%bv = SOff 20 0 ->
In bm_cur_region (ss_mem ss) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 184 <= a < sp1 + 200) ->
 aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a) ->
chk_at g pos sp1 ops c k (ss_pc ss) W2 (mkCfg ms md3).
Proof.
intros g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev ys E ss ms md3
  HJ Hfr Hk Hmo HC Hops Hcur Hkat HJ3 HAG HS Hresv Hkeep H20 Hcr KE.
destruct (enc_callst B MT K XM_LIB LAWS g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev ys E ss ms md3
  HJ Hfr HC Hops Hcur Hkat HJ3 HAG HS Hresv Hkeep H20 Hcr KE) as (HC3 & Hops3 & Hcur3 & Hkat3).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W2) E ss ms HS Hresv).
exists ly2, S2, (ms_regs ms), (ms_mem ms), md3, kev. split; [reflexivity|].
split; [exact HJ3|]. split; [exact Hfr|]. split; [exact Hk|]. split; [exact Hmo|]. split; [exact HC3|].
split; [exact Hops3|]. split; [exact Hcur3 | exact Hkat3].
Qed.

(* k's 184 bytes are readable and marked usable at a call state of the walk, off the callee's window *)
Lemma chk_rd : forall g pos sp1 ly2 S2 W2 regs mem md kev T,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs mem md ->
0 <= T -> 352 + T <= TB_main_need ->
crd_ok tfibsegs W2 mem (spZ regs) T (FA g pos + 192) 184.
Proof.
intros g pos sp1 ly2 S2 W2 regs mem md kev T HJ Hfr HC HT HTn.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs mem md kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
pose proof HC as (_ & _ & R2 & _).
pose proof HJ as (HAR & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity. pose proof satU_T_main_fits as Hfit.
assert (Usp : spZ regs = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; unfold BM_HI in *; lia).
rewrite Usp.
apply (satU_main_k_rd tfibsegs B LAWS ly2 S2 W2 mem md sp1 T pos (FA g pos) LLVMF_STK (e_sp0 g) HAR
  ltac:(rewrite Hfr; left; reflexivity) EFA Hf64 (bm_bs_k B MT K XM_LIB g pos sp1 ly2 S2 W2 regs mem md HC)); lia.
Qed.

(* from a call state of the walk and the callee's post (writing nothing), the cut chk_at at the return address *)
Lemma chk_call : forall g pos sp1 ops c k ly2 S2 W2 regs mem md kev T a ra,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev ->
frames S2 = [(3, pos)] -> 0 <= kev <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs mem md ->
ops_at ops regs -> cur_at g sp1 c W2 mem -> k_at g pos k W2 mem ->
getr regs 1 = w64 ra ->
SRr tfibsegs W2 (cfg_at tfibsegs a regs mem md)
  (cdc_post tfibsegs B MT LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] kev regs T
     cno_wr ly2 S2 W2 mem md (fun _ _ _ => True)) ->
SRr tfibsegs W2 (cfg_at tfibsegs a regs mem md) (chk_at g pos sp1 ops c k ra).
Proof.
intros g pos sp1 ops c k ly2 S2 W2 regs mem md kev T a ra HJ Hfr Hk Hmo HC Hops Hcur Hkat R1 HP.
eapply SRr_mono; [exact HP|]. intros W3 c3 _ Hpost.
destruct Hpost as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HPR & Hfr3 & HPerm & _ & Hmo3 & HK & _).
unfold EV_CDC in HJ3. rewrite Z.add_0_r in HJ3.
destruct (bm_call_kept_x B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs mem md kev c T cno_wr
  ly3 S3 W3 regs3 mem3 md3 kev HJ Hfr HC Hcur ltac:(unfold cno_wr; intros x Hx; destruct Hx) HJ3 HPR HPerm HK)
  as (HC3 & Hcur3 & KF).
assert (HPR20 : getr regs3 20 = getr regs 20) by exact (HPR 20 ltac:(unfold acallee_saved; lia)).
exists ly3, S3, regs3, mem3, md3, kev. split; [rewrite R1; reflexivity|].
split; [exact HJ3|]. split; [rewrite Hfr3; exact Hfr|]. split; [exact Hk|].
split; [exact (mo_le_trans MT MTL _ _ _ 0 0 Hmo Hmo3)|]. split; [exact HC3|].
split; [destruct Hops as [Ho1 Ho2]; split; [exact Ho1 | rewrite HPR20; exact Ho2]|].
split; [exact Hcur3|].
apply (k_at_kept g pos k W2 W3 mem mem3 Hkat). intros x Hx. apply KF; [lia | unfold cno_wr; intros []].
Qed.

(* the three calls, at a call state of the walk with a0 = &k and ra the return address *)
Lemma chk_ref_call : forall g pos sp1 ops c k ly2 S2 W2 regs mem md kev,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev ->
frames S2 = [(3, pos)] -> 0 <= kev <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs mem md ->
ops_at ops regs -> cur_at g sp1 c W2 mem -> k_at g pos k W2 mem ->
getr regs 1 = Z_to_bv 64 0x82ddc -> getr regs 10 = w64 (FA g pos + 192) ->
~ (kz_kind k = 11 /\ kz_b k = 0x70 /\ kz_rc k = 0) ->
SRr tfibsegs W2 (cfg_at tfibsegs BM_check_refusal regs mem md) (chk_at g pos sp1 ops c k 0x82ddc).
Proof.
intros g pos sp1 ops c k ly2 S2 W2 regs mem md kev HJ Hfr Hk Hmo HC Hops Hcur Hkat R1 R10 Hn.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs mem md kev HJ Hfr HC) as (_ & Hf64 & _).
apply (chk_call g pos sp1 ops c k ly2 S2 W2 regs mem md kev TB_check_refusal BM_check_refusal 0x82ddc
  HJ Hfr Hk Hmo HC Hops Hcur Hkat R1).
pose proof Hkat as (Hka & Hwf).
apply (ACR LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev regs
  (FA g pos + 192) k).
- apply (enc_entry B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs mem md kev TB_check_refusal 0x82ddc HJ Hfr Hk HC R1);
    first [lia | reflexivity | apply Z.leb_le; vm_compute; reflexivity].
- exact R10.
- exact (chk_k_al _ Hf64).
- exact Hka.
- exact Hwf.
- apply (chk_rd g pos sp1 ly2 S2 W2 regs mem md kev TB_check_refusal HJ Hfr HC);
    apply Z.leb_le; vm_compute; reflexivity.
- exact Hn.
Qed.

Lemma chk_rng_call : forall g pos sp1 ops c k ly2 S2 W2 regs mem md kev,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev ->
frames S2 = [(3, pos)] -> 0 <= kev <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs mem md ->
ops_at ops regs -> cur_at g sp1 c W2 mem -> k_at g pos k W2 mem ->
getr regs 1 = Z_to_bv 64 0x82de4 -> getr regs 10 = w64 (FA g pos + 192) ->
(kz_rc k <> 0 -> kz_out k = kz_before k) -> kz_rc k = kz_want_rc k ->
SRr tfibsegs W2 (cfg_at tfibsegs BM_check_range regs mem md) (chk_at g pos sp1 ops c k 0x82de4).
Proof.
intros g pos sp1 ops c k ly2 S2 W2 regs mem md kev HJ Hfr Hk Hmo HC Hops Hcur Hkat R1 R10 Ho Hw.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs mem md kev HJ Hfr HC) as (_ & Hf64 & _).
apply (chk_call g pos sp1 ops c k ly2 S2 W2 regs mem md kev TB_check_range BM_check_range 0x82de4
  HJ Hfr Hk Hmo HC Hops Hcur Hkat R1).
pose proof Hkat as (Hka & Hwf).
apply (ACG LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev regs
  (FA g pos + 192) k).
- apply (enc_entry B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs mem md kev TB_check_range 0x82de4 HJ Hfr Hk HC R1);
    first [lia | reflexivity | apply Z.leb_le; vm_compute; reflexivity].
- exact R10.
- exact (chk_k_al _ Hf64).
- exact Hka.
- exact Hwf.
- apply (chk_rd g pos sp1 ly2 S2 W2 regs mem md kev TB_check_range HJ Hfr HC);
    apply Z.leb_le; vm_compute; reflexivity.
- exact Ho.
- exact Hw.
Qed.

Lemma chk_byt_call : forall g pos sp1 ops c k ly2 S2 W2 regs mem md kev,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev ->
frames S2 = [(3, pos)] -> 0 <= kev <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs mem md ->
ops_at ops regs -> cur_at g sp1 c W2 mem -> k_at g pos k W2 mem ->
getr regs 1 = Z_to_bv 64 0x82df4 -> getr regs 10 = w64 (FA g pos + 192) ->
kz_want_len k = cmd_lenZ (kz_out k) -> kz_want_len k <= 24 ->
firstn (Z.to_nat (kz_want_len k)) (kz_out k) = firstn (Z.to_nat (kz_want_len k)) (kz_want k) ->
cmd_keyZ (kz_out k) = kz_want_key k -> cmd_displayZ (kz_out k) = kz_want_display k ->
SRr tfibsegs W2 (cfg_at tfibsegs BM_check_bytes regs mem md) (chk_at g pos sp1 ops c k PC_LATCH).
Proof.
intros g pos sp1 ops c k ly2 S2 W2 regs mem md kev HJ Hfr Hk Hmo HC Hops Hcur Hkat R1 R10 B1 B2 B3 B4 B5.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs mem md kev HJ Hfr HC) as (_ & Hf64 & _).
apply (chk_call g pos sp1 ops c k ly2 S2 W2 regs mem md kev TB_check_bytes BM_check_bytes PC_LATCH
  HJ Hfr Hk Hmo HC Hops Hcur Hkat R1).
pose proof Hkat as (Hka & Hwf).
apply (ACB LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev regs
  (FA g pos + 192) k).
- apply (enc_entry B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs mem md kev TB_check_bytes 0x82df4 HJ Hfr Hk HC R1);
    first [lia | reflexivity | apply Z.leb_le; vm_compute; reflexivity].
- exact R10.
- exact (chk_k_al _ Hf64).
- exact Hka.
- exact Hwf.
- apply (chk_rd g pos sp1 ly2 S2 W2 regs mem md kev TB_check_bytes HJ Hfr HC);
    apply Z.leb_le; vm_compute; reflexivity.
- exact B1.
- exact B2.
- exact B3.
- exact B4.
- exact B5.
Qed.

(* ================================ the run to a callee's entry and the call ================================
   At the stop of a run at the callee's entry: the cut's parts there (enc_callst), a0 and ra read off the state,
   and the call through the lemma LEM (one of the three above, applied to its leading arguments). *)
Ltac chk_do_call g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev ys HJ0 Hfr Hk Hmo HC Hops Hcur Hkat UF LEM :=
  lazymatch goal with
  | HS : st_ok tfibsegs ?Ev ?ssv (restrict (w_H _) ?msv), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?msv) ?mdv _,
    HAE : env_agree 37 _ ?Ev, KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- SRr _ _ (mkCfg ?msv ?mdv') ?Q =>
    let HCc := fresh "HCc" in let Hopsc := fresh "Hopsc" in let Hcurc := fresh "Hcurc" in let Hkatc := fresh "Hkatc" in
    destruct (enc_callst B MT K XM_LIB LAWS g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev ys Ev ssv msv mdv
      HJ0 Hfr HC Hops Hcur Hkat HJ HAE HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; right; right; right; left; reflexivity) KE)
      as (HCc & Hopsc & Hcurc & Hkatc);
    let R1 := fresh "R1" in let R10 := fresh "R10" in
    rreg HS (1%bv : bv 5) R1; rreg HS (10%bv : bv 5) R10;
    rewrite UF in R10;
    eapply (cpw_call _ Ev ssv msv mdv' Q Q); [exact HS | reflexivity | cbn [ss_pc] |
      let W3 := fresh "W" in let c3 := fresh "c" in let H3 := fresh "H" in
      intros W3 c3 H3; apply SRr_ret; exact H3];
    apply (LEM ly2 S2 W2 (ms_regs msv) (ms_mem msv) mdv kev HJ Hfr Hk Hmo HCc Hopsc Hcurc Hkatc R1 R10)
  end.

(* ================================ the three pieces ================================ *)
(* 0x82dd4-0x82dd8: check_refusal, to 0x82ddc *)
Lemma chk_ph1 : forall g pos sp1 ops c k W2 c2,
chk_at g pos sp1 ops c k PC_CHK W2 c2 -> ~ (kz_kind k = 11 /\ kz_b k = 0x70 /\ kz_rc k = 0) ->
SRr tfibsegs W2 c2 (chk_at g pos sp1 ops c k 0x82ddc).
Proof.
intros g pos sp1 ops c k W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & kev & -> & HJ & Hfr & Hk & Hmo & HC & Hops & Hcur & Hkat) Hn.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
unfold BM_HI in Hchi.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof HC as (_ & _ & R2 & _).
pose proof (enc_start B MT K XM_LIB LAWS TL g pos sp1 ly2 S2 W2 regs2 mem2 md2 kev c k 0x82dd4 HJ Hfr HC Hcur Hkat)
  as HS.
remember (bm_env g pos c regs2 (enc_ys k)) as E eqn:HEE.
assert (HAE : env_agree 37 (bm_env g pos c regs2 (enc_ys k)) E) by (subst E; apply env_agree_refl).
assert (B2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (bm_ew_reg g pos c regs2 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (UF : bv_unsigned (ew E 33) = FA g pos).
{ subst E. rewrite (bm_ew_F g pos c regs2 _). apply unsigned_lit_small. lia. }
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W2) mem2)) by apply Forall_nil.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 184 <= a < sp1 + 200) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
unfold cfg_at, PC_CHK. change (w64 0x82dd4) with (Z_to_bv 64 0x82dd4).
cw_keep_j0 HJ HJ0.
cw_run_to cw_awr_stk 0x84bc4. cw_keep cw_kwr_stk.
chk_do_call g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev (enc_ys k) HJ0 Hfr Hk Hmo HC Hops Hcur Hkat UF
  (chk_ref_call g pos sp1 ops c k).
exact Hn.
Qed.

(* 0x82ddc-0x82de0: check_range, to 0x82de4 *)
Lemma chk_ph2 : forall g pos sp1 ops c k W2 c2,
chk_at g pos sp1 ops c k 0x82ddc W2 c2 ->
(kz_rc k <> 0 -> kz_out k = kz_before k) -> kz_rc k = kz_want_rc k ->
SRr tfibsegs W2 c2 (chk_at g pos sp1 ops c k 0x82de4).
Proof.
intros g pos sp1 ops c k W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & kev & -> & HJ & Hfr & Hk & Hmo & HC & Hops & Hcur & Hkat)
  Ho Hw.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
unfold BM_HI in Hchi.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof HC as (_ & _ & R2 & _).
pose proof (enc_start B MT K XM_LIB LAWS TL g pos sp1 ly2 S2 W2 regs2 mem2 md2 kev c k 0x82ddc HJ Hfr HC Hcur Hkat)
  as HS.
remember (bm_env g pos c regs2 (enc_ys k)) as E eqn:HEE.
assert (HAE : env_agree 37 (bm_env g pos c regs2 (enc_ys k)) E) by (subst E; apply env_agree_refl).
assert (B2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (bm_ew_reg g pos c regs2 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (UF : bv_unsigned (ew E 33) = FA g pos).
{ subst E. rewrite (bm_ew_F g pos c regs2 _). apply unsigned_lit_small. lia. }
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W2) mem2)) by apply Forall_nil.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 184 <= a < sp1 + 200) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
unfold cfg_at. change (w64 0x82ddc) with (Z_to_bv 64 0x82ddc).
cw_keep_j0 HJ HJ0.
cw_run_to cw_awr_stk 0x84c84. cw_keep cw_kwr_stk.
chk_do_call g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev (enc_ys k) HJ0 Hfr Hk Hmo HC Hops Hcur Hkat UF
  (chk_rng_call g pos sp1 ops c k).
- exact Ho.
- exact Hw.
Qed.

(* 0x82de4-0x82df0: k.rc, the branch, and check_bytes when k.rc = 0, to LATCH 0x82df4 *)
Lemma chk_ph3 : forall g pos sp1 ops c k W2 c2,
chk_at g pos sp1 ops c k 0x82de4 W2 c2 ->
(kz_rc k = 0 -> kz_want_len k = cmd_lenZ (kz_out k) /\ kz_want_len k <= 24 /\
   firstn (Z.to_nat (kz_want_len k)) (kz_out k) = firstn (Z.to_nat (kz_want_len k)) (kz_want k) /\
   cmd_keyZ (kz_out k) = kz_want_key k /\ cmd_displayZ (kz_out k) = kz_want_display k) ->
SRr tfibsegs W2 c2 (chk_at g pos sp1 ops c k PC_LATCH).
Proof.
intros g pos sp1 ops c k W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & kev & -> & HJ & Hfr & Hk & Hmo & HC & Hops & Hcur & Hkat)
  Hby.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
unfold BM_HI in Hchi.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof HC as (_ & _ & R2 & _).
pose proof Hkat as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & V72 & _) & Hwf).
pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & Wrc & _).
set (ys := [kz_rc k mod 2 ^ 32]).
pose proof (Z.mod_pos_bound (kz_rc k) (2 ^ 32) ltac:(lia)) as Mrc.
assert (X37 : ew (bm_env g pos c regs2 ys) 37 = Z_to_bv 64 (kz_rc k mod 2 ^ 32))
  by exact (bm_ew_y g pos c regs2 ys 0).
assert (Hrk : YP09.chunk_ok tfibsegs (bm_env g pos c regs2 ys) (mrestrict (w_H W2) mem2) (FA g pos) chk_rc_chunk).
{ unfold chk_rc_chunk.
  apply (chunk_ok_val tfibsegs _ _ (FA g pos) 264 4 (SOff 37 0) (kz_rc k mod 2 ^ 32));
    [ rewrite (bm_den_off _ 37 (kz_rc k mod 2 ^ 32) 0 X37) by lia; rewrite Z.add_0_r; reflexivity
    | cbn; lia | cbn; lia |].
  replace (FA g pos + 264) with (FA g pos + 192 + 72) by lia. exact (cw_val_mem_mod _ _ 4 _ V72). }
destruct (rd_start B MT K XM_LIB TL LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 kev c ys [] 0x82de4 0 0 [chk_rc_chunk]
  HJ Hfr HC Hcur ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply Forall_cons; [exact Hrk | apply Forall_nil])
  ltac:(vm_compute; reflexivity) I)
  as (HS & _).
remember (bm_env g pos c regs2 ys) as E eqn:HEE.
assert (HAE : env_agree 37 (bm_env g pos c regs2 ys) E) by (subst E; apply env_agree_refl).
assert (B2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (bm_ew_reg g pos c regs2 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (UF : bv_unsigned (ew E 33) = FA g pos).
{ subst E. rewrite (bm_ew_F g pos c regs2 ys). apply unsigned_lit_small. lia. }
assert (E37 : ew E 37 = Z_to_bv 64 (kz_rc k mod 2 ^ 32)) by (subst E; exact X37).
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W2) mem2)) by apply Forall_nil.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 184 <= a < sp1 + 200) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
unfold cfg_at. change (w64 0x82de4) with (Z_to_bv 64 0x82de4).
cw_keep_j0 HJ HJ0.
(* 0x82de4 lw a0,72(s7); 0x82de8 bnez a0 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk.
cw_branch Hbr.
all: rewrite branch_ne_U, (cw_U_sx32_eqb E 37 (kz_rc k mod 2 ^ 32) 0 E37 ltac:(lia) ltac:(lia)) in Hbr.
- (* k.rc <> 0: to LATCH *)
  cw_run_to cw_awr_stk 0x82df4. cw_keep cw_kwr_stk.
  apply SRr_ret.
  lazymatch goal with
  | HS : st_ok tfibsegs ?Ev ?ssv (restrict (w_H _) ?msv), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?msv) ?mdv _
    |- _ =>
    exact (chk_stop_at g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev ys Ev ssv msv mdv
      HJ0 Hfr Hk Hmo HC Hops Hcur Hkat HJ HAE HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; right; right; right; left; reflexivity) KE)
  end.
- (* k.rc = 0: 0x82dec mv a0,s7; jal check_bytes, returning to LATCH *)
  assert (Hrc0 : kz_rc k = 0).
  { apply (proj1 (chk_rc0 (kz_rc k) Wrc)). apply negb_false_iff in Hbr. apply Z.eqb_eq in Hbr. exact Hbr. }
  destruct (Hby Hrc0) as (B1 & B2' & B3 & B4 & B5).
  cw_run_to cw_awr_stk 0x84d40. cw_keep cw_kwr_stk.
  chk_do_call g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev ys HJ0 Hfr Hk Hmo HC Hops Hcur Hkat UF
    (chk_byt_call g pos sp1 ops c k).
  + exact B1.
  + exact B2'.
  + exact B3.
  + exact B4.
  + exact B5.
Qed.

(* ================================ the segment ================================ *)
Theorem seg_chk_holds : seg_chk B MT K XM_LIB.
Proof using MTL TL LAWS ACR ACG ACB.
unfold seg_chk. intros g pos sp1 ops W2 c2 Hst.
destruct Hst as (ly2 & S2 & regs2 & mem2 & md2 & kev & -> & HJ & Hfr & Hk & Hmo & HC & Hops &
  c & kc & od & Hcur & Hkat & Hrec & Hrc & Hwant).
destruct (bmain_chk_facts kc od Hrec Hrc Hwant) as (P1 & P2 & P3 & P4).
assert (H0 : chk_at g pos sp1 ops c kc PC_CHK W2 (cfg_at tfibsegs PC_CHK regs2 mem2 md2)).
{ exists ly2, S2, regs2, mem2, md2, kev. split; [reflexivity|].
  split; [exact HJ|]. split; [exact Hfr|]. split; [exact Hk|]. split; [exact Hmo|]. split; [exact HC|].
  split; [exact Hops|]. split; [exact Hcur | exact Hkat]. }
eapply SRr_bind; [exact (chk_ph1 g pos sp1 ops c kc W2 _ H0 P1)|]. intros W3 c3 _ H3.
eapply SRr_bind; [exact (chk_ph2 g pos sp1 ops c kc W3 c3 H3 P2 P3)|]. intros W4 c4 _ H4.
eapply SRr_mono; [exact (chk_ph3 g pos sp1 ops c kc W4 c4 H4 P4)|]. intros W5 c5 _ H5.
destruct H5 as (ly5 & S5 & regs5 & mem5 & md5 & k5 & -> & HJ5 & Hfr5 & Hk5 & Hmo5 & HC5 & Hops5 & Hcur5 & _).
exists ly5, S5, regs5, mem5, md5, k5. split; [reflexivity|].
split; [exact HJ5|]. split; [exact Hfr5|]. split; [exact Hk5|]. split; [exact Hmo5|]. split; [exact HC5|].
split; [exact Hops5 | exists c; exact Hcur5].
Qed.
End b.
End a.
