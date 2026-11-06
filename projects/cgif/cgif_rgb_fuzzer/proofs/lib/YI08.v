(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK15 YN06 YK1b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0e YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN02 YI00 YI02 YI03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition LAY_RgbConfig : layout_t :=
[(0, 8%N); (8, 8%N); (16, 8%N); (24, 4%N); (28, 4%N); (32, 2%N); (34, 2%N); (36, 2%N)].
Definition RGBCONFIG_SIZE : Z := 40.
Definition LAY_Rgb : layout_t :=
[(0, 8%N);
(8, 8%N); (16, 8%N); (24, 8%N); (32, 4%N); (36, 4%N); (40, 2%N); (42, 2%N); (44, 2%N);
(48, 8%N); (56, 4%N); (60, 4%N)].
Definition RGB_SIZE : Z := 64.
Definition RG_gif := 0%nat.  Definition RG_wfn := 1%nat. Definition RG_ctx := 2%nat. Definition RG_path := 3%nat.
Definition RG_attr := 4%nat. Definition RG_gen := 5%nat. Definition RG_loops := 6%nat. Definition RG_w := 7%nat.
Definition RG_h := 8%nat.    Definition RG_bef := 9%nat. Definition RG_beffmt := 10%nat. Definition RG_cur := 11%nat.
Definition LAY_Cht : layout_t :=
[(0, 8%N); (8, 8%N); (16, 8%N); (24, 8%N); (32, 8%N); (40, 4%N); (44, 4%N)].
Definition CHT_SIZE : Z := 48.
Lemma lay_inside_RgbConfig : lay_inside LAY_RgbConfig RGBCONFIG_SIZE = true. Proof. reflexivity. Qed.
Lemma lay_inside_Rgb : lay_inside LAY_Rgb RGB_SIZE = true. Proof. reflexivity. Qed.
Lemma lay_inside_Cht : lay_inside LAY_Cht CHT_SIZE = true. Proof. reflexivity. Qed.
Definition optb (p n : Z) : list (Z * Z) := if p =? 0 then [] else [(p, n)].
Definition optfp (p n : Z) : list (Z * Z) := if p =? 0 then [] else [(p, p + n)].


Section J.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis errno_low : errno_addr B + 4 <= alloc_ceiling.
Hypothesis IMG : img_laws B MR.
Local Notation segs := (ms_segs B).
Lemma jfree_opt : free_realizes B MR -> free_null_realizes B ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc p n rest spc raw,
st_ok segs E ss ms -> ss_pc ss = ms_free B -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
Permutation (blocks Lc Ac) (optb p n ++ rest) ->
getr (ms_regs ms) 10 = Z_to_bv 64 p ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - ALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
(p <> 0 -> In (p, n) (blocks L A) -> forall i, 0 <= i < n -> inFP FP (p + i)) ->
SR segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\
Permutation (blocks L2 A2) rest /\
(forall b m i, In (b, m) (blocks L2 A2) -> 0 <= i < m ->
mbyte segs mem2 (b + i) = mbyte segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spc) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x))).
Proof.
intros HFR HFN E ss ms STK sp0 FP L A mem md Lc Ac mdc p n rest spc raw
HS Hpc Hrv HJ HB Ha0 Hsp Hspc Hal Hlo Hhi Htp Hra Hraw HFP.
unfold optb in HB. destruct (Z.eqb_spec p 0) as [->|Hp].
-
destruct (heap_model B MR LAWS _ _ _ _ (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)) as (Hh & Hl & _).
eapply SR_mono.
{ eapply (jfree_null B HFN); [exact HS | exact Hpc | exact Hrv | exact Hh | exact Hl | exact Ha0 | exact Hra | exact Hraw]. }
intros c' ->. exists Lc, Ac, (ms_regs ms), (ms_mem ms), mdc.
split; [reflexivity|]. split; [exact HJ|]. split; [intros r _; reflexivity|].
split; [exact HB|]. split; [intros; reflexivity|]. intros x _ _. split; [reflexivity | tauto].
-
assert (Hin : In (p, n) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
eapply SR_mono.
{ eapply (jfree_at B MR LAWS errno_low IMG HFR) with (a := p) (n := n) (spc := spc);
[ exact HS | exact Hpc | exact Hrv | exact HJ | exact Hin | exact Ha0 | exact Hsp | exact Hspc | exact Hal
| exact Hlo | exact Hhi | exact Htp | exact Hra | exact Hraw | intros Hin0 i Hi; exact (HFP Hp Hin0 i Hi) ]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & _).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
split; [eapply perm_after_rm1; [exact HB | exact Hrm]|]. split; [exact Hkeep | exact Hhi2].
Qed.
End J.
End c.
