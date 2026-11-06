(* lib/A/FSW_pj_free_top.v: pj_free_holds, pj_free_spec k (lib/A/FSH_Fn_reader.v) at every level k, for pj_free in
   image A (fs.asan, 0x83570 .. 0x8371c, pf.c:334-350).
   One level's walk is lib/A/FSW_pj_free.v (pjf_entry: 0x83570 to the loop head 0x835f8 or, n = 0, to 0x83654; the
   loop's kid / key / test segments; pjf_null: v = 0, the `beqz a0` at 0x835a4 to the epilogue) and
   lib/A/FSW_pj_free_tail.v (pjf_tail: 0x83654 .. the ret). Each kid call is pj_free at the level above (REC).
   The level induction starts at level 3, where the spec's premise k <= 2 is false, and runs down to level 0. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_Fn_reader
FSW_K FSW_ret FSW_rd FSW_pj FSW_K3 FSW_pj_free_tbl FSW_pj_free_dat FSW_pj_free FSW_pj_free_tail.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjStruct.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the same Section hypotheses as lib/A/FSW_pj_free.v and lib/A/FSW_pj_free_tail.v *)
Hypothesis HSS : FsShadowSyms B.
Hypothesis fs_fuzz_free_spec : @fuzz_free_spec fx rc SK tfibsegs B.
Hypothesis fs_memset_realizesU : aintrin_realizesU tfibsegs B OSet PC_memset.

(* one level, from the level above *)
Lemma pjf_level : forall k, @pj_free_spec fx rc SK tfibsegs B (S k) -> @pj_free_spec fx rc SK tfibsegs B k.
Proof.
intros k REC ly S0 U W regs mem md ch v D live peak cnt fail Hk HPRE HHD0 H10 HSH HBK HUI HG HSUM HEV.
destruct HSH as [(Hv0 & HD) | (HV & HFD & HPO & HVS)].
- subst v D. eapply (pjf_null B HSS); [lia | eassumption | eassumption | eassumption].
- apply pjf_fd_items in HFD.
  destruct HFD as (HND & HAP & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & HHDR & HSTR &
    HKIDS & HKEYS & HPERM & HITEMS).
  eapply pjf_entry; try eassumption.
  intros F Dfr lyc Sc Uc Wc regsc memc mdc HF HINV HR.
  eapply pjf_tail; eassumption.
Qed.
(* above level 2 the spec's premise k <= 2 is false *)
Lemma pjf_spec_hi : forall j, (3 <= j)%nat -> @pj_free_spec fx rc SK tfibsegs B j.
Proof. intros j Hj ly S0 U W regs mem md ch v D live peak cnt fail Hk. exfalso. lia. Qed.
Lemma pjf_holds_from : forall j, @pj_free_spec fx rc SK tfibsegs B (3 - j).
Proof.
induction j as [|j IH].
- apply pjf_spec_hi. lia.
- destruct (Nat.lt_ge_cases j 3) as [Hj | Hj].
  + apply pjf_level. replace (S (3 - S j)) with (3 - j)%nat by lia. exact IH.
  + replace (3 - S j)%nat with (3 - j)%nat by lia. exact IH.
Qed.
Theorem pj_free_holds : forall k, @pj_free_spec fx rc SK tfibsegs B k.
Proof.
intros k. destruct (Nat.le_gt_cases k 3) as [Hk | Hk].
- replace k with (3 - (3 - k))%nat by lia. apply pjf_holds_from.
- apply pjf_spec_hi. lia.
Qed.
End W.
