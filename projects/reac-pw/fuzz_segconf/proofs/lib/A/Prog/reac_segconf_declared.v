(* The walk of reac_segconf_declared on the ASan build of reac-pw/fuzz_segconf, image A (fuzz_segconf.asan, pin
   sha256 48c5355bdacbc5ba2e0a9ff843627969cb5d2913316654369904b549fc904ef8; entry 0x89854 =
   BASE + AF_reac_segconf_declared, 824 bytes, 206 instructions, side-stack frame class 1): it proves the contract
   reac_segconf_declared_contract of lib/A/Prog/reac_segconf_declared_c.v at this image's numbers, from the five
   segments reac_segconf_declared_s1.v .. _s5.v chained by reac_segconf_declared_a.v, in the form of
   plugin-hostd/fuzz_command's lib/A/Prog/chain_words.v and chain_words_exact.v.
   The Section hypotheses the theorem keeps: the contract's own list (its head comment) - the class-1 side-stack
   frame laws and the two callee contracts at their entries and SegInstA's stack windows; the per-binary record
   facts fuzz_command's walks take (PALib, PALibF, model_laws); and four image facts the record's image files
   discharge when they land: seg_val_relro and seg_sig_prog (SegObj.v), the read-only window below the overflow
   head (ro_below_ofl) and the stack-protector cells split's strtol compares (dc_sspP of
   reac_segconf_declared_d.v).
   The image numbers are SegInstA's (one definition each in the unit): STK_reac_segconf_declared and the two
   callees' STK, RLO_A / RHI_A, gotwA / guardA. The entry and the call targets stay listing terms
   (pa_val A_TEXT + AF_<fn>; the jal targets through seg_sig_prog). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00 YG0q.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable SegSyms SegList SegPa SegPaLib PaLibF PaSB SegObj SegGlob SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
reac_declared_vlan_split_c reac_declared_vlan_add_c reac_segconf_declared_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
reac_segconf_declared_d reac_segconf_declared_lem reac_segconf_declared_a.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
reac_segconf_declared_s1 reac_segconf_declared_s2 reac_segconf_declared_s3 reac_segconf_declared_s4
reac_segconf_declared_s5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
Section e.
Variable B : asyms.
(* the per-binary record facts, as fuzz_command's walks take them *)
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
(* the image facts the record's image files discharge: the listing's relro bounds and call targets, the read-only
   window below the overflow head, the stack-protector cells *)
Hypothesis VRELRO : seg_val_relro.
Hypothesis SIGP : seg_sig_prog.
Context {RO : ro_below_ofl SEGS RLO_A RHI_A}.
Hypothesis SSP : dc_sspP B gotwA guardA.
(* the class-1 side-stack frame: taken by the call at 0x898cc, released by the flag store at 0x89ad8 *)
Hypothesis ASM : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
(* the two program callees, at their entries and stack windows *)
Hypothesis SPLIT : forall fx0 : YK11.FPState,
  @reac_declared_vlan_split_contract fx0 rc SK SEGS B
    (BASE + AF_reac_declared_vlan_split) STK_reac_declared_vlan_split RLO_A RHI_A gotwA guardA.
Hypothesis ADD : forall fx0 : YK11.FPState,
  @reac_declared_vlan_add_contract fx0 rc SK SEGS B
    (BASE + AF_reac_declared_vlan_add) STK_reac_declared_vlan_add RLO_A RHI_A.
(* the read-only window lies in the image: the listing's relro bounds are its own *)
Lemma dc_ro_img : dc_ro_imgP RLO_A RHI_A.
Proof using VRELRO.
unfold dc_ro_imgP, RLO_A, RHI_A, SEG_RLO, SEG_RHI. intros a Ha. apply pa_relro_img.
destruct VRELRO as [E1 E2]. rewrite E1, E2. exact Ha.
Qed.
Theorem reac_segconf_declared_walk :
  reac_segconf_declared_contract SEGS B
    (BASE + AF_reac_segconf_declared) STK_reac_segconf_declared RLO_A RHI_A gotwA guardA.
Proof using TL TLF ML VRELRO SIGP RO SSP ASM SMP ASF FFL SPLIT ADD.
unfold reac_segconf_declared_contract.
intros ly S W regs mem md ch c tab max n rcs t HPRE HROD H10 Hc64 H11 Htab64 H12 Hmax64 H13 Hn64 HDP HROOM HNEV.
pose (cx := mkDCX ly S W regs mem md ch c tab max n rcs t 0).
assert (HP : dc_pre B STK_reac_segconf_declared RLO_A RHI_A gotwA guardA cx) by (constructor; assumption).
exact (dc_run B RLO_A RHI_A gotwA guardA
  (dc_S1 B RLO_A RHI_A gotwA guardA TL TLF ASM SMP ML)
  (dc_S2 B RLO_A RHI_A gotwA guardA SPLIT dc_ro_img SSP SIGP)
  (dc_S3 B RLO_A RHI_A gotwA guardA ADD SIGP dc_ro_img)
  (dc_S4 B RLO_A RHI_A gotwA guardA)
  (dc_S5 B RLO_A RHI_A gotwA guardA ML ASF FFL)
  cx HP).
Qed.
End e.
End f.
End d.
Print Assumptions reac_segconf_declared_walk.
About reac_segconf_declared_walk.
