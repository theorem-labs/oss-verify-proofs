(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH03 YH02 YN3a YI06 YI5b YI09 YI08 YI0r YI1w YI1v YI4l YI21 YI2m YI5o YI5l YI6b YI5n YI20 YI1d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI1n YI1e YI1f YI1c YI1g YI1l.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI5c.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI01 YI3u YI22 YI5a YI5d YI0f YI2w YI2v YI0o YI2s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0c.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI25 YI2n YI1x.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0b YI1o YI1m YI1p.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Notation inFP_nil := YI04.inFP_nil (only parsing).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition AF_SLOW : Z := Eval vm_compute in (src0_A_cgif_addframe + 0x110).
Definition AF_FAST : Z := Eval vm_compute in (src0_A_cgif_addframe + 0x160).
Definition AF_BCMPRET : Z := Eval vm_compute in (src0_A_cgif_addframe + 0x178).
Definition BCMP_CLOB : list reg := [10; 11; 12; 13; 14]%bv.
End c.
Ltac reg_nowG HS tac :=
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
lazymatch goal with |- getr _ ?rr = _ =>
let T := fresh "T" in
pose proof (st_ok_reg src0segs Ec ssc msc rr HS) as T; eval_sr_get_in T; cbn [sv_denot] in T;
repeat (rewrite ew_havoc_old in T; [|nat_lt_lit]); rewrite ?Z.add_0_r in T;
cbn [ms_regs mkst] in T; cbn [ms_regs mkst]; rewrite T; clear T; tac
end
end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition B_regions (ih : Z) : list YP09.region :=
[ YP09.mkRegion (Some 2%nat) 0 96 0 0 (af_stk_chunks 32) ; af_Rg None None None (Some ih) ; af_Rcf ;
af_Rfr_part 18 68 0 40 0 0 ].
Definition B_facts : list (nat * afact) :=
af_facts ++ cf_facts ++ [(58%nat, mkAF 1 65535 0); (59%nat, mkAF 1 65535 0); (18%nat, mkAF 4096 (CEIL_MAX - 40) 4);
(69%nat, mkAF 4096 CEIL_MAX 0); (70%nat, mkAF 0 4294967295 0); (72%nat, mkAF 0 65535 0)].
Definition ss_slow (ih : Z) : sstate := mkSS AF_SLOW sr_atoms (B_regions ih) None (mkFacts B_facts [] []).
Definition ss_fast (ih : Z) : sstate := mkSS AF_FAST sr_atoms (B_regions ih) None (mkFacts B_facts [] []).
Section S.
Variable API : AllocAPI src0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src0_msyms MR.
Hypothesis FLUSHX : flushX_spec API.
Definition B_pre (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (regs0 regs1 : bvmap 5 word) (Lc : layout) (Ac : astate)
(memc : word -> option byte) (mdc : Model) (g N : Z) (s0 s : cgif_st) (rest FP : list (Z * Z)) (fh : frame_st)
(cfp lpal lpa img fattr fgen delay nlp tidx : Z) : Prop :=
let sp0 := spZ regs0 in
let CB := (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) in
journal src0_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac memc mdc /\ st_init_done Ac = true /\
YK0s.ret_ok (getr regs0 1) /\ sp0 mod 16 = 0 /\ getr regs0 4 = Z_to_bv 64 (ms_tp src0_msyms) /\
cgif_at memc g s /\ cgif_wf s N /\ same_geom s s0 /\
nth_error (cg_frames s) (Z.to_nat (cg_ihead s)) = Some (Some fh) /\
(Z.land fattr 1 = 0 -> Z.land (cg_attr s) 4 = 0) /\
obj_at src0segs memc cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] /\
cfp mod 8 = 0 /\ sp0 <= cfp /\ cfp + 32 <= 2 ^ 63 /\
Z_to_bv 64 lpa = Z_to_bv 64 lpal /\
(forall b n a, In (b, n) (cgif_blocks0 g s N) -> b <= a < b + n -> inFP FP a) /\
Permutation (blocks Lc Ac) (cgif_blocks0 g s N ++ CB ++ rest) /\
af_saved_ok memc sp0 regs0 /\
getr regs1 2 = Z_to_bv 64 (sp0 - 96) /\ getr regs1 8 = Z_to_bv 64 g /\ getr regs1 9 = Z_to_bv 64 cfp /\
getr regs1 18 = Z_to_bv 64 (fr_ptr fh) /\ getr regs1 21 = Z_to_bv 64 (g + 8 * cg_ihead s) /\
getr regs1 20 = Z_to_bv 64 (Z.land fattr 4) /\ getr regs1 19 = Z_to_bv 64 (cg_ihead s) /\
af_untouched regs0 regs1.
Definition B_preX (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (regs0 regs1 : bvmap 5 word) (Lc : layout) (Ac : astate)
(memc : word -> option byte) (mdc : Model) (g N : Z) (s0 s : cgif_st) (rest FP : list (Z * Z)) (fh : frame_st)
(cfp lpal lpa img fattr fgen delay nlp tidx : Z) (GPAL IMGv LPALv : list Z) (gs : YO07.gif_st) (brb : rbound) (HD : YO07.frame) : Prop :=
cg_gen s = cg_gen s0 /\ cg_file s = cg_file s0 /\
af_sink g s0 s N rest FP (concat (YO07.s_out gs)) L A mem md /\ (forall a, inFP (cgif_fp g s0 N) a -> a < alloc_ceiling) /\
Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N <= SINK_MAX /\ spZ regs0 <= 2 ^ 47 /\
cgif_live gs /\ rc_int (cg_cur s) = YO07.s_cur gs /\ af_live memc s N GPAL gs /\
garr8 src0segs memc img IMGv /\ Z.of_nat (length IMGv) = N /\
(Z.land fattr 1 <> 0 -> garr8 src0segs memc lpa LPALv /\ Z.of_nat (length LPALv) = 3 * nlp) /\
res_ok Ac brb /\ af_room brb N /\
qslot gs (Z.to_nat (cg_ihead s)) = Some HD /\ delay + YO07.f_delay HD <= 65535 /\ Z.land (cg_gen s) 1 = 0 /\
bv_unsigned (getr regs1 22) mod 2 ^ 16 = delay + YO07.f_delay HD.
End S.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
