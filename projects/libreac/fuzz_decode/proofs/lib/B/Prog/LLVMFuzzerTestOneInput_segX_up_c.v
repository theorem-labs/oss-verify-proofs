(* LLVMFuzzerTestOneInput_segX_up_c: the straight stretches of the image-B up segment of LLVMFuzzerTestOneInput
   between malloc #3 and the scan loop L5, each from a concrete configuration to the next call (or the loop head):
   +0x8c8 .. __asan_memset (the NULL check of the new buffer refuted), +0x8dc .. reac_upstream_decode #1,
   +0x8ec .. reac_upstream_decode #2, and +0x900 .. +0x918 (the two abort edges +0x904 / +0x908 refuted).
   Each is one Pa run of lib/B/Prog/DecodeBPaLib.v from a seat with no tracked memory (segX_up_b up_seat0), as
   segX_up_b up_B1 is; and the __asan_memset call itself (lib/A/Prog/YC85.v aj_intrin_atS, as
   lib/B/Prog/LLVMFuzzerTestOneInput_segX_crt1_calls.v c1e_memset_call uses it for the decode buffer). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaRun PaShadow PaJournal YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBList DecodeBAddr DecodeBPa DecodeBImg DecodeBPaLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_segX_up_den LLVMFuzzerTestOneInput_segX_up_a LLVMFuzzerTestOneInput_segX_up_b.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN1y.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* YM03.v:182-189 redefines lia / nia globally (context pruning and retries); this file uses the originals
   (YM03.v:179-180). *)
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.

(* The landing of a run at a call: the memory is the run's start memory (no region is written) and the
   configuration is the callee's entry. *)
Ltac up_land HF HS HJ :=
  up_memeq HF; pmkst HS; cbn [pa_sigma PI_decodeb] in *;
  lazymatch goal with Hm : ms_mem _ = _ |- _ => rewrite Hm; rewrite Hm in HJ end.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Abbreviation SEGS := (@pa_segs _ decodeb_listing PI_decodeb).
#[local] Abbreviation VAL := (@pa_val _ decodeb_listing PI_decodeb).
#[local] Abbreviation BASE := (@pa_val _ decodeb_listing PI_decodeb A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := @paj_run fx rc dec_B_sink_head decodeb_listing PL_decodeb PI_decodeb B LAWS.
Let BR := @paj_branch fx rc decodeb_listing PI_decodeb.

(* An entry register, read through the seat's env. *)
Lemma up_den_atom : forall regs (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r ->
  sv_denot (EUP regs) (SOff n 0) = getr regs r.
Proof.
intros regs n r Hn. cbn [sv_denot]. rewrite (EUP_reg regs r n Hn), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma up_U_atom : forall regs (n : nat) (r : bv 5) v, Z.of_nat n = bv_unsigned r ->
  getr regs r = w64 v -> 0 <= v < 18446744073709551616 -> U (EUP regs) (SOff n 0) = v.
Proof.
intros regs n r v Hn Hr Hv. unfold U. rewrite (up_den_atom regs n r Hn), Hr. unfold w64.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616. apply Z.mod_small. exact Hv.
Qed.

Lemma up_U_m1 : forall regs (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r ->
  getr regs r = w64 (-1) -> U (EUP regs) (SOff n 0) = 18446744073709551615.
Proof.
intros regs n r Hn Hr. unfold U. rewrite (up_den_atom regs n r Hn), Hr. reflexivity.
Qed.

(* ---- +0x8c8 .. __asan_memset ---- *)
Definition up_keepB2 : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 10%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 24%bv; 25%bv; 26%bv; 27%bv].

Lemma up_B2 : forall (W : world SEGS) regs mem md upb (Q : world SEGS -> config -> Prop)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc k,
  @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  getr regs 10 = w64 upb -> 4096 <= upb < 18446744073709551616 ->
  (forall regsT mdT,
     getr regsT 11 = w64 165 -> getr regsT 12 = getr regs 24 -> getr regsT 23 = getr regs 10 ->
     getr regsT 1 = Z_to_bv 64 (BASE + 0x8dc) ->
     (forall x, In x up_keepB2 -> getr regsT x = getr regs x) ->
     @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem mdT k ->
     SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (decodeb_sigma DB___asan_memset)) mem (seg_rom SEGS)) mdT) Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x8c8)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md upb Q STK sp0 FP ly S W0 mem0 md0 own lyc Sc k HJ H10 Hu HK.
destruct (up_seat0 0x8c8 regs W mem) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (EUP regs)) by (unfold EUP; apply Eimg_env).
psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb.
- exfalso. rewrite branch_eq_U, (up_U_atom regs 10 10%bv upb eq_refl H10 ltac:(lia)), U_SLit in Hb.
  apply Z.eqb_eq in Hb. change (zcanon 0) with 0 in Hb. lia.
- paj_run_tok RUN HS HJ SHOK UPspan; [apply awr_ok_nil|].
  up_land HF HS HJ. apply HK.
  + up_rege HS (11%bv : bv 5) (SLit 165). reflexivity.
  + up_rege HS (12%bv : bv 5) (SOff 24 0). exact (up_den_atom regs 24 24%bv eq_refl).
  + up_rege HS (23%bv : bv 5) (SOff 10 0). exact (up_den_atom regs 10 10%bv eq_refl).
  + up_rege HS (1%bv : bv 5) (SOff 240 2268). exact (codeptr_val (EUP regs) 2268 HEI).
  + up_kept HS regs up_extra up_keepB2 (up_agree regs).
  + exact HJ.
Qed.

(* ---- +0x8dc .. reac_upstream_decode #1 (raw = NULL) ---- *)
Definition up_keepC : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].

Lemma up_C1 : forall (W : world SEGS) regs mem md (Q : world SEGS -> config -> Prop)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc k,
  @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  (forall regsT mdT,
     getr regsT 10 = w64 0 -> getr regsT 11 = getr regs 22 -> getr regsT 12 = getr regs 23 ->
     getr regsT 1 = Z_to_bv 64 (BASE + 0x8ec) ->
     (forall x, In x up_keepC -> getr regsT x = getr regs x) ->
     @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem mdT k ->
     SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (decodeb_sigma DB_reac_upstream_decode)) mem (seg_rom SEGS)) mdT) Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x8dc)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q STK sp0 FP ly S W0 mem0 md0 own lyc Sc k HJ HK.
destruct (up_seat0 0x8dc regs W mem) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (EUP regs)) by (unfold EUP; apply Eimg_env).
paj_run_tok RUN HS HJ SHOK UPspan; [apply awr_ok_nil|].
up_land HF HS HJ. apply HK.
- up_rege HS (10%bv : bv 5) (SLit 0). reflexivity.
- up_rege HS (11%bv : bv 5) (SOff 22 0). exact (up_den_atom regs 22 22%bv eq_refl).
- up_rege HS (12%bv : bv 5) (SOff 23 0). exact (up_den_atom regs 23 23%bv eq_refl).
- up_rege HS (1%bv : bv 5) (SOff 240 2284). exact (codeptr_val (EUP regs) 2284 HEI).
- up_kept HS regs up_extra up_keepC (up_agree regs).
- exact HJ.
Qed.

(* ---- +0x8ec .. reac_upstream_decode #2 (out = NULL) ---- *)
Definition up_keepC2 : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 26%bv; 27%bv].

Lemma up_C2 : forall (W : world SEGS) regs mem md (Q : world SEGS -> config -> Prop)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc k,
  @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  (forall regsT mdT,
     getr regsT 10 = getr regs 27 -> getr regsT 11 = getr regs 22 -> getr regsT 12 = w64 0 ->
     getr regsT 25 = getr regs 10 -> getr regsT 1 = Z_to_bv 64 (BASE + 0x900) ->
     (forall x, In x up_keepC2 -> getr regsT x = getr regs x) ->
     @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem mdT k ->
     SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (decodeb_sigma DB_reac_upstream_decode)) mem (seg_rom SEGS)) mdT) Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x8ec)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q STK sp0 FP ly S W0 mem0 md0 own lyc Sc k HJ HK.
destruct (up_seat0 0x8ec regs W mem) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (EUP regs)) by (unfold EUP; apply Eimg_env).
paj_run_tok RUN HS HJ SHOK UPspan; [apply awr_ok_nil|].
up_land HF HS HJ. apply HK.
- up_rege HS (10%bv : bv 5) (SOff 27 0). exact (up_den_atom regs 27 27%bv eq_refl).
- up_rege HS (11%bv : bv 5) (SOff 22 0). exact (up_den_atom regs 22 22%bv eq_refl).
- up_rege HS (12%bv : bv 5) (SLit 0). reflexivity.
- up_rege HS (25%bv : bv 5) (SOff 10 0). exact (up_den_atom regs 10 10%bv eq_refl).
- up_rege HS (1%bv : bv 5) (SOff 240 2304). exact (codeptr_val (EUP regs) 2304 HEI).
- up_kept HS regs up_extra up_keepC2 (up_agree regs).
- exact HJ.
Qed.

(* ---- +0x900 .. +0x918: both refusing calls returned -1 (+0x904 / +0x908), then a2 = a1 = 0, s9 = ~s7 ---- *)
Definition up_keepD : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 26%bv; 27%bv].

Lemma up_D : forall (W : world SEGS) regs mem md (Q : world SEGS -> config -> Prop)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc k,
  @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  getr regs 25 = w64 (-1) -> getr regs 10 = w64 (-1) ->
  (forall regsT mdT,
     getr regsT 11 = w64 0 -> getr regsT 12 = w64 0 ->
     getr regsT 25 = sv_denot (EUP regs) (SAlu ALU_XOR (SOff 23 0) (SLit (-1))) ->
     (forall x, In x up_keepD -> getr regsT x = getr regs x) ->
     @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem mdT k ->
     SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + 0x918)) mem (seg_rom SEGS)) mdT) Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x900)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q STK sp0 FP ly S W0 mem0 md0 own lyc Sc k HJ H25 H10 HK.
destruct (up_seat0 0x900 regs W mem) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (EUP regs)) by (unfold EUP; apply Eimg_env).
paj_run_tok RUN HS HJ SHOK UPspan; [apply awr_ok_nil|]. up_memeq HF.
psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb1.
{ exfalso. rewrite branch_ne_U, (up_U_m1 regs 25 25%bv eq_refl H25), U_SLit in Hb1. discriminate. }
paj_run_tok RUN HS HJ SHOK UPspan; [apply awr_ok_nil|]. up_memeq HF.
psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb2.
{ exfalso. rewrite branch_ne_U, (up_U_m1 regs 10 10%bv eq_refl H10), U_SLit in Hb2. discriminate. }
paj_run_tok RUN HS HJ SHOK UPspan; [apply awr_ok_nil|]. up_memeq HF.
(* stopped at the loop head's branch +0x918, before it *)
lazymatch goal with Hm : ms_mem _ = _ |- _ => rewrite Hm in HJ end.
pmkst HS.
lazymatch goal with Hm : ms_mem _ = _ |- _ => rewrite Hm end.
apply HK.
- up_rege HS (11%bv : bv 5) (SLit 0). reflexivity.
- up_rege HS (12%bv : bv 5) (SLit 0). reflexivity.
- up_rege HS (25%bv : bv 5) (SAlu ALU_XOR (SOff 23 0) (SLit (-1))). reflexivity.
- up_kept HS regs up_extra up_keepD (up_agree regs).
- exact HJ.
Qed.
End g.
