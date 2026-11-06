(* G4.ExHead.HeadExits: the scan head of expected (fm.asan): the state facts a head run keeps (hd_at_step) and the
   head's exits hd_exit_L (EX_CONT -> EX_L at i + 1), hd_exit_P (EX_P), hd_exit_R (EX_R).
   Memory: the only change a head run makes is the strncmp call's stack window [F - STK_RT_STR, F) (hd_keep). That
   window lies above alloc_ceiling (astk_ok of expected's entry: alloc_ceiling <= ly_stk_lo and
   ly_stk_lo + STK_expected <= sp, STK_expected = 208 + 8224), so the facts below alloc_ceiling survive (FMW_lib.v
   fw_glob_low / fw_rodata_low / fw_cstr_low), and the frame slots [F + 0x18, F + 0xd0) lie above it. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMW_ex_base FMW_ex_head_d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* an 8-byte value at or above F survives hd_keep (its window is below F); after FMW_lib.v fw_val_eqv *)
Lemma hx_val_keep : forall cx W (m m' : word -> option byte) a v,
  hd_keep cx W m m' -> 0 <= cx_F cx <= a -> a + 8 <= 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) m) a 8 v -> val_mem tfibsegs (mrestrict (w_H W) m') a 8 v.
Proof.
  intros cx W m m' a v HK Ha Han Hv k Hk. unfold hd_keep in HK.
  rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W) m m'); [apply Hv; exact Hk|].
  apply HK; lia.
Qed.

(* what ex_at_L at the entry state gives at the run's end state, apart from the index registers *)
Lemma hx_carry : forall cx i d f ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2,
  ex_at_L B cx i d f ly3 S3 W3 regs1 mem1 md1 ->
  hd_jr B cx ly3 S3 W3 mem2 md2 -> hd_keep cx W3 mem1 mem2 -> hd_kept_regs regs1 regs2 ->
  ex_com B cx ly3 S3 W3 regs2 mem2 md2 /\ ex_slots cx W3 mem2 d /\ ex_sregs cx regs2.
Proof.
  intros cx i d f ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2 HA HJ HK HR.
  destruct HA as (HB & HC & HSL & HSR & _).
  destruct HC as (_ & Hbl & HGL & Rsp & Rgp & Rtp & R25 & HSV & HRO & HCt & HCu & HKt & HKu).
  destruct HR as (K2 & K3 & K4 & K25 & K23 & K22 & K18 & K8).
  destruct HSR as (S23 & S22 & S18 & S8).
  pose proof HB as ((HPRE & _) & _).
  pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & _).
  assert (HSTK : STK_expected = 208 + 8224) by reflexivity.
  assert (HSTR : STK_RT_STR = 8192) by reflexivity.
  assert (HF : alloc_ceiling + 8224 <= cx_F cx /\ cx_F cx + 208 <= 2 ^ 47) by (unfold cx_F, cx_sp; lia).
  assert (KL : fw_low tfibsegs (w_H W3) mem1 mem2).
  { intros a Ha. unfold hd_keep in HK. apply HK; lia. }
  split; [|split].
  - split; [exact HJ|]. split; [exact Hbl|].
    split; [exact (fw_glob_low tfibsegs W3 mem1 mem2 _ _ _ _ KL HGL)|].
    split; [rewrite K2; exact Rsp|]. split; [rewrite K3; exact Rgp|]. split; [rewrite K4; exact Rtp|].
    split; [rewrite K25; exact R25|].
    split.
    { unfold ex_saved_ok in HSV |- *. rewrite Forall_forall in HSV |- *. intros s Hs.
      apply (hx_val_keep cx W3 mem1 mem2); [exact HK | | | exact (HSV s Hs)];
        unfold EX_SAVED in Hs; cbn [In] in Hs;
        repeat (destruct Hs as [<-|Hs]; [cbn [fst]; lia|]); contradiction. }
    split; [exact (fw_rodata_low tfibsegs B (w_H W3) mem1 mem2 fmw_segs_low KL HRO)|].
    split; [exact (fw_cstr_low tfibsegs W3 mem1 mem2 _ _ KL HCt)|].
    split; [exact (fw_cstr_low tfibsegs W3 mem1 mem2 _ _ KL HCu)|].
    split; [exact HKt | exact HKu].
  - destruct HSL as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
    unfold ex_slots. cbv zeta.
    repeat split; apply (hx_val_keep cx W3 mem1 mem2); try exact HK; try assumption; lia.
  - split; [rewrite K23; exact S23|]. split; [rewrite K22; exact S22|].
    split; [rewrite K18; exact S18 | rewrite K8; exact S8].
Qed.

Lemma hd_at_step : forall cx i d f ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2,
  ex_at_L B cx i d f ly3 S3 W3 regs1 mem1 md1 ->
  hd_jr B cx ly3 S3 W3 mem2 md2 -> hd_keep cx W3 mem1 mem2 ->
  hd_kept_regs regs1 regs2 -> getr regs2 19 = getr regs1 19 -> hd_lits regs2 ->
  ex_at_L B cx i d f ly3 S3 W3 regs2 mem2 md2.
Proof.
  intros cx i d f ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2 HA HJ HK HR R19 HL.
  destruct (hx_carry cx i d f ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2 HA HJ HK HR) as (HC & HSL & HSR).
  destruct HA as (HB & _ & _ & _ & HSC & A19 & _).
  destruct HL as (L9 & L15 & L16).
  split; [exact HB|]. split; [exact HC|]. split; [exact HSL|]. split; [exact HSR|]. split; [exact HSC|].
  split; [rewrite R19; exact A19|]. exact (conj L9 (conj L15 L16)).
Qed.

Lemma hd_exit_L : forall cx i d f f' ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2,
  ex_seg_L_from B cx i -> ex_at_L B cx i d f ly3 S3 W3 regs1 mem1 md1 -> ex_scan cx (S i) d f' ->
  hd_jr B cx ly3 S3 W3 mem2 md2 -> hd_keep cx W3 mem1 mem2 ->
  hd_kept_regs regs1 regs2 -> getr regs2 19 = w64 (Z.of_nat (S i)) -> hd_lits regs2 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_L regs2 mem2 md2) (ex_post B cx).
Proof.
  intros cx i d f f' ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2 HLf HA HSC' HJ HK HR R19 HL.
  destruct (hx_carry cx i d f ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2 HA HJ HK HR) as (HC & HSL & HSR).
  destruct HA as (HB & _).
  destruct HL as (L9 & L15 & L16).
  apply (HLf (S i) d f' ly3 S3 W3 regs2 mem2 md2); [lia|].
  split; [exact HB|]. split; [exact HC|]. split; [exact HSL|]. split; [exact HSR|]. split; [exact HSC'|].
  split; [exact R19|]. exact (conj L9 (conj L15 L16)).
Qed.

Lemma hd_exit_P : forall cx i d f a1 ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2,
  ex_seg_L_from B cx i -> ex_seg_P B -> ex_at_L B cx i d f ly3 S3 W3 regs1 mem1 md1 ->
  (i < length (cx_tb cx))%nat -> ManifestModel.head (cx_tb cx) i = Some (i + a1)%nat -> (a1 = 6 \/ a1 = 7)%nat ->
  hd_jr B cx ly3 S3 W3 mem2 md2 -> hd_keep cx W3 mem1 mem2 ->
  hd_kept_regs regs1 regs2 -> getr regs2 19 = getr regs1 19 -> hd_lits regs2 ->
  getr regs2 20 = w64 (cx_t cx + Z.of_nat i) -> getr regs2 11 = w64 (Z.of_nat a1) ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_P regs2 mem2 md2) (ex_post B cx).
Proof.
  intros cx i d f a1 ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2 HLf HP HA Hi Hh Ha1 HJ HK HR R19 HL R20 R11.
  destruct (hx_carry cx i d f ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2 HA HJ HK HR) as (HC & HSL & HSR).
  destruct HA as (HB & _ & _ & _ & HSC & A19 & _).
  destruct HL as (L9 & L15 & L16).
  apply (HP cx i d f a1 ly3 S3 W3 regs2 mem2 md2 HLf).
  split; [exact HB|]. split; [exact HC|]. split; [exact HSL|]. split; [exact HSR|]. split; [exact HSC|].
  split; [exact Hi|]. split; [exact Hh|]. split; [exact Ha1|]. split; [rewrite R19; exact A19|].
  split; [exact R20|]. split; [exact R11|]. exact (conj L9 (conj L15 L16)).
Qed.

Lemma hd_exit_R : forall cx i d f ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2,
  ex_seg_R B -> ex_at_L B cx i d f ly3 S3 W3 regs1 mem1 md1 ->
  hd_jr B cx ly3 S3 W3 mem2 md2 -> hd_keep cx W3 mem1 mem2 ->
  hd_kept_regs regs1 regs2 -> getr regs2 10 = w64 (cx_res cx) ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_R regs2 mem2 md2) (ex_post B cx).
Proof.
  intros cx i d f ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2 HR0 HA HJ HK HR R10.
  destruct (hx_carry cx i d f ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2 HA HJ HK HR) as (HC & _).
  destruct HA as (HB & _).
  exact (HR0 cx ly3 S3 W3 regs2 mem2 md2 HB HC R10).
Qed.
End s.

Print Assumptions hd_at_step.
Print Assumptions hd_exit_L.
Print Assumptions hd_exit_P.
Print Assumptions hd_exit_R.
