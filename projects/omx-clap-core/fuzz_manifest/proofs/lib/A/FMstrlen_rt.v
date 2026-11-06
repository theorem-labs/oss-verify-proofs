(* fm's runtime contract for the strlen interceptor in the donor's form: astrlen_realizes (lib/A/FMH_Rt.v:107) at
   PC_strlen = 0x412c8, the four-byte jump to the interceptor at 0x41364 (REAL = musl strlen 0x92c08).
   Proved input: A/FMstrlen.v strlen_icpt_srr, the whole function from the jump to its return in the donor's
   per-call form.  This file unpacks ecall_pre_k and cstr_ok into its premises, with k the string's length, and
   repacks its post as rt_post_ro over STK_RT_STR = 2 * ESTACK, which is the walk's window.  The string and its
   NUL lie below alloc_ceiling and the window lies above it (FMrt_pre.stk_of_pre), so the two do not meet; the
   bytes musl's word loop reads after the NUL are cstr_ok's last clause; the word constants musl reads
   (0x10348 .. 0x10368, neither runtime-owned nor errno) come from rom_viewN (mconsts_of_rom_viewN). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import
AB1v AF0m AF0x FMupoison FMH_Base FMH_Rt FMrt_pre.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require AE39 FMstrlen.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* a C string's bytes and its NUL, as the donor's reader reads them *)
Lemma aview_cstr : forall (W : world tfibsegs) mem p (l : list Z) j,
  cstr tfibsegs W mem p l -> (j <= length l)%nat ->
  aview tfibsegs (w_H W) mem (p + Z.of_nat j) = Some (nth j (l ++ [0]) 0).
Proof.
  intros W mem p l j (HG & _) Hj.
  assert (Hj' : (j < length (l ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  destruct (HG j Hj') as (HV & HR).
  specialize (HV 0%nat ltac:(lia)).
  replace (p + Z.of_nat j + Z.of_nat 0) with (p + Z.of_nat j) in HV by lia.
  unfold aview. rewrite HV. cbn [option_map].
  rewrite (FMrt_pre.le_byte1 _ HR), (FMrt_pre.u8z _ HR). reflexivity.
Qed.

(* the musl word constants AE39.mconsts_view asks for, from the non-owned half of rom_view: no runtime-owned static
   and not errno meets 0x10348 .. 0x10368 *)
Lemma mconsts_of_rom_viewN : forall B (W : world tfibsegs) mem, TfibSyms B ->
  rom_viewN tfibsegs B W mem -> AE39.mconsts_view W mem.
Proof.
  intros B W mem TB Hr a Ha. pose proof AE39.mc_bounds as [B1 B2].
  pose proof Ha as Ha'. rewrite B1, B2 in Ha'.
  apply Hr; [exact (AE39.mc_in_rom a Ha) | |].
  - rewrite (ts_owned B TB). intros X. apply Exists_exists in X as ([lo n] & Hin & Hz). unfold in_zr in Hz.
    cbn [fst snd] in Hz.
    assert (C : forallb (fun r : Z * Z => (0x10368 <=? fst r) || (fst r + snd r <=? 0x10348)) Tfib_owned_static = true)
      by (vm_compute; reflexivity).
    pose proof (proj1 (forallb_forall _ _) C (lo, n) Hin) as Hc. cbn [fst snd] in Hc.
    apply orb_prop in Hc as [Hc|Hc]; apply Z.leb_le in Hc; lia.
  - rewrite (ts_errno B TB). unfold TFIB_ERRNO. lia.
Qed.

Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.

Theorem astrlen_holds : astrlen_realizes tfibsegs B PC_strlen.
Proof.
  unfold astrlen_realizes. intros ly S W regs mem md x l HPRE HROM G10 HCS.
  pose proof HCS as (HCSTR & Hx4096 & HxE & H32 & Ham & HRA & HV & HTAIL).
  pose proof HCSTR as (_ & HNZ).
  destruct (FMrt_pre.stk_of_pre B ly S W regs mem md STK_RT_STR HPRE ltac:(unfold STK_RT_STR, ESTACK; lia))
    as (_ & _ & HC1 & _).
  destruct HPRE as (HEP & _ & HLO & HW).
  pose proof (@YM05.alloc_ceiling_lt rc) as HCL.
  unfold STK_RT_STR, ESTACK in HC1.
  (* the string and its NUL lie below alloc_ceiling, the walk's window above it *)
  assert (DISJ : forall a, x <= a <= x + Z.of_nat (length l) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs))
    by (intros a Ha; unfold ESTACK; lia).
  eapply SRr_mono.
  - change (cfg_at tfibsegs PC_strlen regs mem md) with (cfg_at tfibsegs FMstrlen.SL_ENTRY regs mem md).
    apply (FMstrlen.strlen_icpt_srr B LAWS TB ly S W regs mem md x (Z.of_nat (length l)) HEP HLO HW G10);
      [ lia | lia | exact H32 | lia | | | exact DISJ
      | apply (FMrt_pre.amem_range_mono _ _ _ Ham); lia
      | exact HRA | exact HV | exact HTAIL | exact (mconsts_of_rom_viewN B W mem TB HROM) ].
    + (* first_byte: the bytes before index len are visible and not NUL, the byte at len is the NUL *)
      hnf. split; [lia|]. split.
      * intros i Hi. exists (nth (Z.to_nat i) (l ++ [0]) 0). split.
        -- replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia. apply aview_cstr; [exact HCSTR | lia].
        -- rewrite app_nth1 by lia. apply (proj1 (Forall_forall _ _) HNZ). apply nth_In. lia.
      * intros _. pose proof (aview_cstr W mem x l (length l) HCSTR (le_n _)) as E.
        rewrite app_nth2, Nat.sub_diag in E by lia. exact E.
    + (* src_ok: every byte up to the NUL is visible and below the window *)
      hnf. intros a Ha. split.
      * replace a with (x + Z.of_nat (Z.to_nat (a - x))) by lia.
        rewrite (aview_cstr W mem x l (Z.to_nat (a - x)) HCSTR ltac:(lia)). discriminate.
      * unfold ESTACK. lia.
  - cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & HAR' & HKEEP & Hsbm & A10 & Hfr & Hpres).
    hnf. split; [reflexivity|]. exists regs', mem', md', (Z.of_nat (length l)).
    split; [exact Hc|]. split; [exact HAR'|]. split; [exact HKEEP|]. split; [exact Hsbm|].
    split; [exact A10|]. split; [lia|]. split; [reflexivity|]. split; [exact Hfr | exact Hpres].
Qed.

End s.
