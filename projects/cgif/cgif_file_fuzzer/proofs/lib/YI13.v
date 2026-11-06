(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK15 YM06 YP09 YP0m YP0l YP0k YP03 YK1j.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI06 YI09 YI16 YI00 YI14.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition WRITECB_STK : Z := 16 + FWRITE_STK.
Section c.
Variable segs : list Segment.
Lemma garr8_of_readable : forall (mem : word -> option byte) base n,
(forall a, base <= a < base + Z.of_nat n -> exists b, mbyte segs mem a = Some b) ->
exists l, length l = n /\ garr8 segs mem base l.
Proof.
intros mem base n. revert base. induction n as [|n IH]; intros base Hr.
- exists []. split; [reflexivity | apply garr8_nil].
- destruct (Hr base ltac:(lia)) as [b Hb].
destruct (IH (base + 1)) as (l & Hlen & Hl); [intros a Ha; apply Hr; lia|].
pose proof (bv_unsigned_in_range _ b) as Hbr. change (bv_modulus 8) with 256 in Hbr.
exists (bv_unsigned b :: l). split; [cbn; lia|]. intros [|j] Hj.
+ cbn [nth Z.of_nat]. rewrite Z.add_0_r. split; [|lia].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. reflexivity.
+ cbn [nth]. destruct (Hl j ltac:(cbn in Hj; lia)) as [Hv Hrg]. split; [|exact Hrg].
replace (base + Z.of_nat (S j)) with (base + 1 + Z.of_nat j) by lia. exact Hv.
Qed.
Definition segs_below (Bd : Z) : bool :=
forallb (fun sg => Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? Bd) segs.
Lemma writable_readable_high : forall Bd (m : word -> option byte) a,
segs_below Bd = true -> Bd <= a < 2 ^ 64 -> writable_at segs m a -> exists b, mbyte segs m a = Some b.
Proof.
intros Bd m a Hb Ha Hw. unfold writable_at, wview in Hw. unfold mbyte.
destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|]. exfalso.
destruct (find_segment segs (bv_unsigned (Z_to_bv 64 a)) 1) as [sg|] eqn:Hf; [| apply Hw; reflexivity].
pose proof (find_segment_range _ _ _ _ Hf) as [H1 H2]. pose proof (find_segment_in _ _ _ _ Hf) as Hin.
unfold segs_below in Hb. pose proof (proj1 (forallb_forall _ _) Hb sg Hin) as Hle. cbn beta in Hle. apply Z.leb_le in Hle.
rewrite YP03.unsigned_lit_small in H2 by lia. lia.
Qed.
Lemma garr8_of_writable_high : forall Bd (mem : word -> option byte) base n,
segs_below Bd = true -> Bd <= base -> base + Z.of_nat n <= 2 ^ 64 ->
(forall a, base <= a < base + Z.of_nat n -> writable_at segs mem a) ->
exists l, length l = n /\ garr8 segs mem base l.
Proof.
intros Bd mem base n Hb Hlo Hhi Hw. apply garr8_of_readable. intros a Ha.
apply (writable_readable_high Bd mem a Hb); [lia | apply Hw; exact Ha].
Qed.
End c.
Section W.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Context {SH : sink_head} {SK : sink_syms}.
Local Notation segs := (ms_segs B).
Definition writecb_spec (pc : Z) : Prop :=
forall L A (regs : bvmap 5 word) mem md g gvals (src n f : Z) (S bs : list Z),
fn_pre B MR WRITECB_STK L A regs mem md -> spZ regs <= 2 ^ 47 ->
getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 src -> getr regs 12 = Z_to_bv 64 n ->
obj_at segs mem g LAY_CGIF gvals ->
nth_error gvals CG_wfn = Some 0 -> nth_error gvals CG_file = Some f ->
In (g, CGIF_SIZE) (blocks L A) -> In (f, FILE_BLOCK) (blocks L A) ->
sink_at B mem md f S ->
garr8 segs mem src bs -> n = Z.of_nat (length bs) -> 0 <= src -> src + n <= 2 ^ 47 ->
(src + n <= f \/ f + FILE_BLOCK <= src) ->
(src + n <= spZ regs - WRITECB_STK \/ spZ regs <= src) ->
Z.of_nat (length S) + n <= SINK_MAX -> n <= 2 ^ 30 ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
(fun c' => exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
journal B MR WRITECB_STK (spZ regs) (sink_fp f) L A mem md L A mem' md' /\
regs_preserved regs regs' /\ getr regs' 10 = Z_to_bv 64 0 /\
sink_at B mem' md' f (S ++ bs)).
Lemma jwrite : forall pc, writecb_spec pc ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc g gvals (src n f : Z) (S bs : list Z) raw,
st_ok segs E ss ms -> ss_resv ss = None -> ss_pc ss = pc ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
getr (ms_regs ms) 10 = Z_to_bv 64 g -> getr (ms_regs ms) 11 = Z_to_bv 64 src -> getr (ms_regs ms) 12 = Z_to_bv 64 n ->
spZ (ms_regs ms) mod 16 = 0 -> sp0 - STK <= spZ (ms_regs ms) - WRITECB_STK -> spZ (ms_regs ms) <= sp0 ->
spZ (ms_regs ms) <= 2 ^ 47 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp B) ->
obj_at segs (ms_mem ms) g LAY_CGIF gvals ->
nth_error gvals CG_wfn = Some 0 -> nth_error gvals CG_file = Some f ->
In (g, CGIF_SIZE) (blocks Lc Ac) -> In (f, FILE_BLOCK) (blocks Lc Ac) ->
sink_at B (ms_mem ms) mdc f S ->
garr8 segs (ms_mem ms) src bs -> n = Z.of_nat (length bs) -> 0 <= src -> src + n <= 2 ^ 47 ->
(src + n <= f \/ f + FILE_BLOCK <= src) ->
(src + n <= spZ (ms_regs ms) - WRITECB_STK \/ spZ (ms_regs ms) <= src) ->
Z.of_nat (length S) + n <= SINK_MAX -> n <= 2 ^ 30 ->
(forall a, inFP (sink_fp f) a -> inFP FP a) ->
SR segs (mkCfg ms mdc)
(fun c' => exists regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md Lc Ac mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = Z_to_bv 64 0 /\
sink_at B mem2 md2 f (S ++ bs) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spZ (ms_regs ms) - WRITECB_STK <= x < spZ (ms_regs ms)) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\ (writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x)) /\
(forall a m i, In (a, m) (blocks Lc Ac) -> 0 <= i < m -> ~ inFP (sink_fp f) (a + i) ->
mbyte segs mem2 (a + i) = mbyte segs (ms_mem ms) (a + i))).
Proof.
intros pc WCB E ss ms STK sp0 FP L A mem md Lc Ac mdc g gvals src n f S bs raw
HS Hrv Hpc HJ Hra Hraw Ha0 Ha1 Ha2 Hal16 Hlo Hhi Hsp47 Htp Hobj Hwfn Hfile Hgin Hfin HSK HG Hn Hs0 Hs47 Hsf Hss Hroom Hn30 HFP.
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HFBv : FILE_BLOCK = 1264) by reflexivity. assert (HWv : WRITECB_STK = 528) by reflexivity.
pose proof (proj1 HJ) as HHc.
destruct (heap_blocks_range B MR LAWS Lc Ac (ms_mem ms) mdc f FILE_BLOCK HHc Hfin ltac:(lia)) as (Hf0 & Hf1 & Hf16).
eapply SR_mono.
{ eapply (jcall B MR) with (STK1 := WRITECB_STK) (FP1 := sink_fp f)
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) =>
L2 = Lc /\ A2 = Ac /\ getr regs2 10 = Z_to_bv 64 0 /\ sink_at B mem2 md2 f (S ++ bs));
[ exact HS | exact Hrv | exact HJ | exact Hra | | exact Hraw | exact Hal16 | lia | exact Hlo | exact Hhi | exact Htp | ].
- intros HPRE1. rewrite Hpc. eapply SR_mono.
{ eapply (WCB Lc Ac _ _ mdc g gvals src n f S bs HPRE1); try eassumption. }
cbv beta. intros c' (regs2 & mem2 & md2 & -> & HJc & HP & Hr10 & HSK2).
exists Lc, Ac, regs2, mem2, md2. split; [rewrite Hra; reflexivity|]. split; [exact HJc|]. split; [exact HP|].
repeat (split; [reflexivity|]). split; [exact Hr10 | exact HSK2].
- intros a Ha. split; [exact (HFP a Ha)|]. destruct Ha as (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (-> & -> & Hr10 & HSK2)).
exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hr10|]. split; [exact HSK2|].
split.
- pose proof HJc2 as (_ & _ & Hhi2 & _). exact Hhi2.
- intros a m i Hin Hi Hnf. pose proof HJc2 as (_ & _ & _ & Hblk2 & _). exact (Hblk2 a m i Hin Hin Hi Hnf).
Qed.
End W.
