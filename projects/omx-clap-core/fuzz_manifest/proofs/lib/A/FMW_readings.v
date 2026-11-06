(* lv2_locate_manifest_readings 0x81c04: readings_holds, the segments (FMW_rd_pre / _lp / _pp_top / _c8 / _pl, each to the
   next cut or the shared return FMW_rd_ret.v) assembled by FMW_rd_top.v's inductions, under the callee contracts
   (Section hypotheses, the donor's ACfi.v:107-114 pattern). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC20 YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_g3kit FMW_rd_base FMW_rd_cuts FMW_rd_top.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import
FMW_rd_pre FMW_rd_lp FMW_rd_pp_top FMW_rd_c8 FMW_rd_pl.
Import ListNotations.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).
Hypothesis CELLS : g3_cells B.
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis STRLEN : astrlen_realizes tfibsegs B PC_strlen.
Hypothesis SNPRINTF : asnprintf_realizes tfibsegs B PC_snprintf.
Hypothesis STRSTR : astrstr_realizes tfibsegs B PC_strstr.
Hypothesis STRNCMP : astrncmp_realizes tfibsegs B PC_strncmp.
Hypothesis STRNCASECMP : astrncasecmp_realizes tfibsegs B PC_strncasecmp.
Hypothesis STRCHR : astrchr_realizes tfibsegs B PC_strchr.
Hypothesis ISALNUM : aisalnum_realizes tfibsegs B PC_isalnum.
Hypothesis MALLOC : fuzz_malloc_spec tfibsegs B CTX_fuzz_malloc.
Hypothesis FREE : fuzz_free_spec tfibsegs B CTX_fuzz_free.
Hypothesis HASP : has_prefixed_spec tfibsegs B.

Theorem readings_holds : readings_spec tfibsegs B CTX.
Proof.
apply (readings_holds_seg B CTX).
- intros HL. eapply rd_E_holds; eassumption.
- intros f H1 H2. eapply rd_L_holds; eassumption.
- intros f H1 H2. eapply rd_P_holds; eassumption.
- intros f H1 H2. eapply rd_C8_holds; eassumption.
- intros f m H1 H2. eapply rd_PL_holds; eassumption.
Qed.
End c.
