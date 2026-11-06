(* G4.ExHead.HeadExits, IMAGE B: the scan head of expected (fm.asan-ubsan): the state facts a head run keeps (hd_at_step,
   hx_at_L) and the head's exits hd_exit_P (EX_P), hd_exit_R (EX_R) and hd_exit_L (EX_NEXT 0x81694 -> EX_L at i + 1).
   B's continue is code, not a register move as in A: EX_NEXT `addi s7, s7, 1; add s5, a6, s7; ld a0, 0x80(sp)` and
   the UBSan guard 0x816a0 `bgeu a0, s7` (a0 = ~text from F+0x80; the not-taken arm is `j 0x8194c`, the trap). hd_N
   walks it: ss_N's facts (~text in [2^64 - 2^47, 2^64 - 4097], s7 <= MANIFEST_MAX) let the symbolic run decide the
   guard taken, so the trap arm is never reached (YP0e.v decide_cond2).
   Memory: the only change a head run makes is the strncmp call's stack window [F - STK_RT_STR, F) (hd_keep). That
   window lies above alloc_ceiling (astk_ok of expected's entry: alloc_ceiling <= ly_stk_lo and
   ly_stk_lo + STK_expected <= sp, STK_expected = 240 + 8224), so the facts below alloc_ceiling survive (FMW_lib.v
   fw_glob_low / fw_rodata_low / fw_cstr_low), and the frame slots [F + 0x28, F + 0xf0) lie above it.
   Shape after image A's lib/A/FMW_ex_head_x.v (06d82004dc3). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMTrapB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_ex_base FMW_ex_head_d FMW_ex_head_e.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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

(* what ex_at_L at the entry state gives at the run's end state, apart from the scan's registers *)
Lemma hx_carry : forall cx i d f ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2,
  ex_at_L B cx i d f ly3 S3 W3 regs1 mem1 md1 ->
  hd_jr B cx ly3 S3 W3 mem2 md2 -> hd_keep cx W3 mem1 mem2 ->
  getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
  getr regs2 25 = getr regs1 25 ->
  ex_com B cx ly3 S3 W3 regs2 mem2 md2 /\ ex_slots cx W3 mem2 d.
Proof.
  intros cx i d f ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2 HA HJ HK K2 K3 K4 K25.
  destruct HA as (HB & HC & HSL & _).
  destruct HC as (_ & Hbl & HGL & Rsp & Rgp & Rtp & R25 & HSV & HRO & HCt & HCu & HKt & HKu).
  pose proof HB as ((HPRE & _) & _).
  pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & _).
  assert (HSTK : STK_expected = 240 + 8224) by reflexivity.
  assert (HSTR : STK_RT_STR = 8192) by reflexivity.
  assert (HF : alloc_ceiling + 8224 <= cx_F cx /\ cx_F cx + 240 <= 2 ^ 47) by (unfold cx_F, cx_sp; lia).
  assert (KL : fw_low tfibsegs (w_H W3) mem1 mem2).
  { intros a Ha. unfold hd_keep in HK. apply HK; lia. }
  split.
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
  - destruct HSL as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
    unfold ex_slots. cbv zeta.
    repeat split; apply (hx_val_keep cx W3 mem1 mem2); try exact HK; try assumption; lia.
Qed.

(* ex_at_L at a run's end state, at any index i' whose scan state holds there *)
Lemma hx_at_L : forall cx i d f i' f' ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2,
  ex_at_L B cx i d f ly3 S3 W3 regs1 mem1 md1 ->
  hd_jr B cx ly3 S3 W3 mem2 md2 -> hd_keep cx W3 mem1 mem2 ->
  getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
  getr regs2 25 = getr regs1 25 -> getr regs2 16 = getr regs1 16 -> hd_lits regs2 ->
  ex_scan cx i' d f' -> getr regs2 23 = w64 (Z.of_nat i') -> getr regs2 21 = w64 (cx_t cx + Z.of_nat i') ->
  ex_at_L B cx i' d f' ly3 S3 W3 regs2 mem2 md2.
Proof.
  intros cx i d f i' f' ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2 HA HJ HK K2 K3 K4 K25 K16 HL HSC R23 R21.
  destruct (hx_carry cx i d f ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2 HA HJ HK K2 K3 K4 K25) as (HC & HSL).
  destruct HA as (HB & _ & _ & _ & HCR & _).
  destruct HCR as (R16 & _).
  destruct HL as (L8 & L19 & L27 & L17 & L5 & L6).
  split; [exact HB|]. split; [exact HC|]. split; [exact HSL|].
  split; [exact (conj L19 (conj L27 L8))|].
  split; [exact (conj (eq_trans K16 R16) (conj L17 (conj L5 L6)))|].
  split; [exact HSC|]. split; [exact R23 | exact R21].
Qed.

Lemma hd_at_step : forall cx i d f ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2,
  ex_at_L B cx i d f ly3 S3 W3 regs1 mem1 md1 ->
  hd_jr B cx ly3 S3 W3 mem2 md2 -> hd_keep cx W3 mem1 mem2 ->
  hd_kept_regs regs1 regs2 -> hd_lits regs2 ->
  ex_at_L B cx i d f ly3 S3 W3 regs2 mem2 md2.
Proof.
  intros cx i d f ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2 HA HJ HK HR HL.
  destruct HR as (K2 & K3 & K4 & K25 & K23 & K21 & K16).
  pose proof HA as (_ & _ & _ & _ & _ & HSC & R23 & R21).
  apply (hx_at_L cx i d f i f ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2 HA HJ HK K2 K3 K4 K25 K16 HL HSC);
    [rewrite K23; exact R23 | rewrite K21; exact R21].
Qed.

Lemma hd_exit_P : forall cx i d f a1 ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2,
  ex_seg_L_from B cx i -> ex_seg_P B -> ex_at_L B cx i d f ly3 S3 W3 regs1 mem1 md1 ->
  (i < length (cx_tb cx))%nat -> ManifestModel.head (cx_tb cx) i = Some (i + a1)%nat -> (a1 = 6 \/ a1 = 7)%nat ->
  hd_jr B cx ly3 S3 W3 mem2 md2 -> hd_keep cx W3 mem1 mem2 ->
  hd_kept_regs regs1 regs2 -> hd_lits regs2 -> getr regs2 10 = w64 (Z.of_nat a1) ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_P regs2 mem2 md2) (ex_post B cx).
Proof.
  intros cx i d f a1 ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2 HLf HP HA Hi Hh Ha1 HJ HK HR HL R10.
  pose proof (hd_at_step cx i d f ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2 HA HJ HK HR HL) as HA2.
  destruct HA2 as (HB & HC & HSL & HSR & HCR & HSC & R23 & R21).
  apply (HP cx i d f a1 ly3 S3 W3 regs2 mem2 md2 HLf).
  split; [exact HB|]. split; [exact HC|]. split; [exact HSL|]. split; [exact HSR|]. split; [exact HCR|].
  split; [exact HSC|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Ha1|].
  split; [exact R23|]. split; [exact R21 | exact R10].
Qed.

Lemma hd_exit_R : forall cx i d f ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2,
  ex_seg_R B -> ex_at_L B cx i d f ly3 S3 W3 regs1 mem1 md1 ->
  hd_jr B cx ly3 S3 W3 mem2 md2 -> hd_keep cx W3 mem1 mem2 ->
  getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
  getr regs2 25 = getr regs1 25 -> getr regs2 10 = w64 (cx_res cx) ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_R regs2 mem2 md2) (ex_post B cx).
Proof.
  intros cx i d f ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2 HR0 HA HJ HK K2 K3 K4 K25 R10.
  destruct (hx_carry cx i d f ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2 HA HJ HK K2 K3 K4 K25) as (HC & _).
  destruct HA as (HB & _).
  exact (HR0 cx ly3 S3 W3 regs2 mem2 md2 HB HC R10).
Qed.

(* EX_NEXT (0x81694) -> EX_L at i + 1: s7 = i + 1, s5 = a6 + 1 + s7_old; guard 0x816a0 decided by ss_N's facts *)
Lemma hd_N : forall cx i d f f' ly3 S3 W3 regs1 mem1 md1,
  ex_seg_L_from B cx i -> ex_at_L B cx i d f ly3 S3 W3 regs1 mem1 md1 -> ex_scan cx (S i) d f' ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_NEXT regs1 mem1 md1) (ex_post B cx).
Proof.
  intros cx i d f f' ly3 S3 W3 regs1 mem1 md1 HLf HA HSC'.
  pose proof (AR_laws_ok tfibsegs B) as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (hd_N_entry B cx i d f ly3 S3 W3 regs1 mem1 md1 HA) as HS.
  pose proof HA as (HB & HC & _ & _ & HCR & HSC & R23 & R21).
  pose proof HC as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HCt & _).
  pose proof HCR as (R16 & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Htb).
  pose proof HCt as (_ & H4096 & Hcl & _).
  pose proof HSC' as (Hi' & _).
  remember (Ereg regs1 [Z_to_bv 64 (2 ^ 64 - 1 - cx_t cx)]) as E eqn:HE.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs1 q)
    by (intros n q Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
  clear HE.
  assert (E16 : ew E 16 = Z_to_bv 64 (cx_t cx)) by (rewrite (EE 16%nat 16%bv eq_refl); exact R16).
  assert (E23 : ew E 23 = Z_to_bv 64 (Z.of_nat i)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
  assert (SHOK : sh_ok tfibsegs HD_Bx [] E
    (mrestrict (w_H W3) (ms_mem (mkst regs1 (Z_to_bv 64 EX_NEXT) mem1 (seg_rom tfibsegs))))) by constructor.
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem1 a = aview tfibsegs (w_H W3) mem1 a)
    by reflexivity.
  change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 EX_NEXT) mem1 (seg_rom tfibsegs))) in HJ.
  unfold cfg_at. change (w64 EX_NEXT) with (Z_to_bv 64 EX_NEXT).
  aj_run_to_tok EX_tbl_ok HS HJ SHOK HD_Bspan EX_L; [awr_ok_tac|]. hd_av W3 mem1.
  hd_mk HS.
  apply (HLf (S i) d f' ly3 S3 W3 _ _ _ ltac:(lia)).
  apply (hx_at_L cx i d f (S i) f' ly3 S3 W3 regs1 mem1 md1 _ _ _ HA HJ).
  - intros a Ha _. exact (AV a Ha).
  - hd_g HS. apply EE. reflexivity.
  - hd_g HS. apply EE. reflexivity.
  - hd_g HS. apply EE. reflexivity.
  - hd_g HS. apply EE. reflexivity.
  - hd_g HS. apply EE. reflexivity.
  - unfold hd_lits. repeat split; hd_g HS; reflexivity.
  - exact HSC'.
  - hd_g HS. rewrite E23, unsigned_lit_small by lia. unfold w64; f_equal; lia.
  - lazymatch goal with |- getr _ ?r = _ => hd_reg HS r end.
    unfold w64. apply fw_sv_U.
    rewrite (U_add_off_atom _ 16 1 23 0); rewrite ?E16, ?E23, ?unsigned_lit_small by lia; unfold M64; lia.
Qed.

Lemma hd_exit_L : forall cx i d f f' ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2,
  ex_seg_L_from B cx i -> ex_at_L B cx i d f ly3 S3 W3 regs1 mem1 md1 -> ex_scan cx (S i) d f' ->
  hd_jr B cx ly3 S3 W3 mem2 md2 -> hd_keep cx W3 mem1 mem2 ->
  hd_kept_regs regs1 regs2 -> hd_lits regs2 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_NEXT regs2 mem2 md2) (ex_post B cx).
Proof.
  intros cx i d f f' ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2 HLf HA HSC' HJ HK HR HL.
  exact (hd_N cx i d f f' ly3 S3 W3 regs2 mem2 md2 HLf
    (hd_at_step cx i d f ly3 S3 W3 regs1 mem1 md1 regs2 mem2 md2 HA HJ HK HR HL) HSC').
Qed.
End s.

Print Assumptions hd_at_step.
Print Assumptions hd_exit_P.
Print Assumptions hd_exit_R.
Print Assumptions hd_exit_L.
