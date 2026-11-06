(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1050 of its 1065 lines of code are new or changed and 32 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/CF/tx_put.v, with its module paths and module names changed; 14 of its 33 lines of code are new or changed and 1046 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/CF/tx_value.v, with its module paths and module names changed; 637 of its 661 lines of code are new or changed and 9 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract MemNorm KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct WriterSpec WriterSpecFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger GIInit TsRuns TsGo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import tx_put_c TxRet TxGlue TxCompose TxTree TsHelp tx_string_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import TxCalls.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section KB.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRB : errno_addr B + 4 <= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling.
Hypothesis AX : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable.YL01.AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis HG : globals_free B API omx_G.
Variable F : ResForm.
#[local] Set Default Proof Using "All".

Section Loop.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (t s k b0 len0 cap0 : Z) (bs : list Z) (txt : list byte) (bnd : rf_R F) (Lam : list (Z * Z)) (peak cnt fail : Z).
Hypothesis TXP : tx_put_contract B API F.
Hypothesis ST : tx_start B API F TS_STACK L A regs mem md t b0 len0 cap0 txt bnd (plen (strp bs))
  (len0 + Z.of_nat (length (map (Z_to_bv 8) (wstr bs))) + 1).
Hypothesis LED : ledger B L A mem Lam peak cnt fail.
Hypothesis CS : pj_cstr (ms_segs B) mem (fun a n => In (a, n) Lam) s k bs.
Hypothesis NB : forall a n, In (a, n) Lam -> a - 16 <> b0.

Local Notation FP := (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -112).
Local Notation N := (Z.of_nat (length bs)).
Local Notation NEED := (len0 + Z.of_nat (length (map (Z_to_bv 8) (wstr bs))) + 1).
Local Notation SVC := [C8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 27); C8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 26); C8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 25);
  C8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 24); C8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 23); C8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 22); C8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 21);
  C8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 20); C8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 19); C8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 18); C8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 9);
  C8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 8); C8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1)].
Local Notation PP := (tx_ret B API F TS_STACK L A regs mem md t b0 len0 cap0 txt (map (Z_to_bv 8) (wstr bs)) (plen (strp bs)) bnd
  (fun L' A' mem' => ledger B L' A' mem' Lam peak cnt fail /\
                     pj_cstr (ms_segs B) mem' (fun a n => In (a, n) Lam) s k bs)).

Lemma ts_num : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling + 8400 <= spZ regs /\ spZ regs < 2 ^ 63 /\ spZ regs mod 16 = 0 /\
  spZ regs <= t /\ t + 24 <= 2 ^ 64 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 10 = Z_to_bv 64 t /\
  4112 <= s /\ s + k <= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling /\ N + 1 <= k /\ Forall (fun c => 0 < c < 256) bs /\
  aa_MR API L A mem md /\ tx_inv B L A mem b0 len0 cap0 txt.
Proof.
  pose proof ST as ((M & _ & _ & RET & SPal & SPK & SP63 & _) & _ & _ & R10 & SPT & Thi & _ & _ & _ & _ & _ & _ & INV & _).
  unfold TS_STACK, TX_STACK, REALLOC_STACK, ALLOC_STACK in SPK.
  destruct CS as (Hin & Hk & HF & _).
  destruct LED as (_ & _ & _ & _ & _ & HL). rewrite Forall_forall in HL.
  destruct (HL (s, k) Hin) as (_ & Hb & _). cbn [fst snd] in Hb.
  destruct (block_range B API L A mem md _ _ M Hb) as [B1 B2].
  do 5 (split; [lia|]). split; [exact RET|]. split; [exact R10|]. split; [lia|]. split; [lia|].
  split; [exact Hk|]. split; [exact HF|]. split; [exact M | exact INV].
Qed.

Definition ts_inv (i : Z) : Prop :=
  forall regs2 pc2 mem2 md2 L2 A2 b2 cap2,
    evt rsegs (ts_Q N i (cat bs i) FP (s + i) t (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4)
                 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 8) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 9) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 18) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 19) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 20)
                 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 21) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 22) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 23) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 24) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 25)
                 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 26) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 27) fp_regs fp_csr (normalize rsegs mem2))
      (MS (canR regs2) fp_regs pc2 fp_csr None (normalize rsegs mem2) (seg_rom rsegs)) ->
    tx_relx B API F TS_STACK regs t b0 len0 cap0 txt (accs bs i) bnd L A mem md L2 A2 mem2 md2 b2 cap2 (ksb bs i) ->
    rw_cells rsegs mem2 (FP + 8) SVC ->
    SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs2 pc2 mem2 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md2) PP.

Lemma ts_keep : forall R1 mem1 mem2, spZ R1 = FP -> rw_cells rsegs mem1 (FP + 8) SVC ->
  (forall a, spZ R1 <= a < 2 ^ 64 -> ~ (t <= a < t + 24) ->
     mbyte (ms_segs B) mem2 a = mbyte (ms_segs B) mem1 a /\
     (writable_at (ms_segs B) mem1 a <-> writable_at (ms_segs B) mem2 a)) ->
  rw_cells rsegs mem2 (FP + 8) SVC.
Proof.
  intros R1 mem1 mem2 S1 SV KEEP. destruct ts_num as (SPK & SP63 & _ & SPT & _).
  pose proof (spZ_range regs) as SPR.
  apply (rw_cells_same mem1); [exact SV|]. intros a Ha. cbn [cells_size csize] in Ha.
  unfold spZ in *. rewrite <- SEGS. destruct (KEEP a) as [E Wr]; [lia | lia |].
  split; [exact E | intros Wa; apply Wr; exact Wa].
Qed.

Lemma ts_land : forall i mem2 md2 L2 A2 b2 cap2 R pc m' can ms',
  tx_relx B API F TS_STACK regs t b0 len0 cap0 txt (accs bs i) bnd L A mem md L2 A2 mem2 md2 b2 cap2 (ksb bs i) ->
  rw_cells rsegs mem2 (FP + 8) SVC ->
  munch [(FP, FP + 8)] (normalize rsegs mem2) m' -> wmono rsegs (normalize rsegs mem2) m' ->
  ms_rel rsegs can (MS R fp_regs pc fp_csr None m' (seg_rom rsegs)) -> ro_same rsegs mem2 (ms_mem can) ->
  Regs6ss.ms_eqv can ms' ->
  ms' = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst (ms_regs ms') pc (ms_mem ms') (seg_rom rsegs) /\
  (forall r, is_x0 r = false -> reg_get (ms_regs ms') r = reg_get R r) /\
  mem_rel rsegs (ms_mem ms') m' /\
  tx_relx B API F TS_STACK regs t b0 len0 cap0 txt (accs bs i) bnd L A mem md L2 A2 (ms_mem ms') md2 b2 cap2 (ksb bs i) /\
  rw_cells rsegs (ms_mem ms') (FP + 8) SVC.
Proof.
  intros i mem2 md2 L2 A2 b2 cap2 R pc m' can ms' R2 SV MU WM HREL RS EQV.
  destruct ts_num as (SPK & SP63 & _).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  pose proof R2 as (_ & _ & _ & _ & _ & _ & _ & _ & RA2 & _).
  assert (RA2r : ro_agree rsegs mem2) by (rewrite <- SEGS; exact RA2).
  destruct (final_n _ _ _ _ _ _ _ _ HREL EQV eq_refl eq_refl) as (EMS & HR & MRL & EM).
  rewrite <- EM in RS.
  pose proof (munch_rel rsegs _ mem2 (normalize rsegs mem2) (ms_mem ms') m' (mem_rel_normalize rsegs mem2 RA2r)
                MRL RS MU) as MU'.
  pose proof (wmono_rel rsegs mem2 (normalize rsegs mem2) (ms_mem ms') m' (mem_rel_normalize rsegs mem2 RA2r)
                MRL RS WM) as WM'.
  pose proof (ro_agree_same rsegs mem2 (ms_mem ms') RA2r RS) as RA'.
  split; [exact EMS|]. split; [exact HR|]. split; [exact MRL|]. split.
  - apply (tx_relx_store B API SEGS ERRB AX CTX HG F TS_STACK L A regs mem md t b0 len0 cap0 txt bnd _ _ (accs bs i)
             L2 A2 mem2 md2 b2 cap2 (ksb bs i)
             (ms_mem ms') FP (FP + 8) ST R2 MU' WM'); [rewrite SEGS; exact RA' |].
    intros a Ha. unfold spZ, TS_STACK, TX_STACK, REALLOC_STACK, ALLOC_STACK in *. lia.
  - apply (rw_cells_same mem2); [exact SV|]. intros a Ha. cbn [cells_size csize] in Ha.
    rewrite <- SEGS. unfold spZ in *.
    destruct (munch_byte B _ _ _ a MU' ltac:(lia) ltac:(cbn [outside]; split; [lia | exact I])) as [E Wr].
    split; [exact E | intros Wa; apply Wr; exact Wa].
Qed.

Lemma ts_norm : forall acc mem3 md3 L3 A3 b3 cap3 j3,
  tx_relx B API F TS_STACK regs t b0 len0 cap0 txt acc bnd L A mem md L3 A3 mem3 md3 b3 cap3 j3 ->
  rw_cells rsegs mem3 (FP + 8) SVC ->
  bytes_at rsegs (normalize rsegs mem3) s (map (Z_to_bv 8) (bs ++ [0])) /\
  (exists j, rw_cells rsegs (normalize rsegs mem3) FP [CB 8 j]) /\
  rw_cells rsegs (normalize rsegs mem3) (FP + 8) SVC /\
  mem_inv rsegs (normalize rsegs mem3) /\ bytes_at rsegs (normalize rsegs mem3) 0x104a8 hexl.
Proof.
  intros acc mem3 md3 L3 A3 b3 cap3 j3 R3 SV.
  destruct ts_num as (SPK & SP63 & _).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  pose proof R3 as ((_ & _ & _ & _ & _ & _ & _ & _ & SC3) & _ & _ & _ & _ & _ & _ & _ & RA3 & _).
  assert (RA3r : ro_agree rsegs mem3) by (rewrite <- SEGS; exact RA3).
  destruct (tx_rel_cstr B API F TS_STACK regs t b0 len0 cap0 txt acc bnd L A mem md L3 A3 mem3 md3 b3 cap3 j3
              Lam peak cnt fail s k bs R3 LED NB CS) as ((_ & _ & _ & HB3) & _).
  rewrite SEGS in HB3.
  split; [apply bytes_at_normalize; assumption|].
  split.
  { assert (FRP : forall i, 0 <= i < 8 -> present mem3 (FP + i)).
    { intros i Hi. unfold spZ in *. apply (present_of_writable B SEGS); [lia | left; lia |].
      apply SC3. unfold scratch_k, spZ, TS_STACK, TX_STACK, REALLOC_STACK, ALLOC_STACK. left. lia. }
    unfold spZ in *.
    edestruct (rw_of_present mem3 FP 8) as [j FRJ]; [lia | lia | lia | exact FRP |].
    exists j. change (Z.to_nat 8) with 8%nat in FRJ.
    apply rw_cells_norm; [exact RA3r | exact FRJ |]. intros i Hi. cbn in Hi.
    apply (ro_false B SEGS); [lia | left; lia]. }
  split.
  { unfold spZ in *. apply rw_cells_norm; [exact RA3r | exact SV |]. intros i Hi. cbn in Hi.
    apply (ro_false B SEGS); [lia | left; lia]. }
  split; [apply mem_inv_normalize|].
  apply bytes_at_normalize; [exact RA3r | exact (hex_img B API SEGS ERRB AX CTX HG mem3 RA3)].
Qed.

Lemma str_read : forall m j, bytes_at rsegs m s (map (Z_to_bv 8) (bs ++ [0])) -> 0 <= j <= N ->
  ov_read_bytes rsegs m (wa (s + j)) 1 = Some [Z_to_bv 8 (cat bs j)].
Proof.
  intros m j H Hj.
  rewrite (bytes_at_read rsegs m s _ j 1 H) by (rewrite ?length_map, ?length_app; cbn [length]; lia).
  f_equal. unfold cat. apply firstn1_map. rewrite length_app. cbn [length]. lia.
Qed.

Lemma str_src_ok : forall acc L1 A1 mem1 md1 b1 cap1 j1 regs1 i,
  tx_relx B API F TS_STACK regs t b0 len0 cap0 txt acc bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1 ->
  0 <= i < N -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling <= spZ regs1 - TX_STACK ->
  forall x, 0 <= x < 1 ->
    ~ (t <= s + i + x < t + 24) /\ ~ (spZ regs1 - TX_STACK <= s + i + x < spZ regs1) /\
    ~ (b1 <= s + i + x < b1 + cap1) /\
    (len0 + Z.of_nat (length acc) + 1 + 1 <= cap1 \/ spZ regs1 <= s + i + x \/
     Mem.ro_addr (ms_segs B) (Z_to_bv 64 (s + i + x)) = true \/
     exists a k', In (a, k') (blocks L1 A1) /\ a <> b1 /\ a <= s + i + x < a + k').
Proof.
  intros acc L1 A1 mem1 md1 b1 cap1 j1 regs1 i R1 Hi AC1 x Hx.
  destruct ts_num as (SPK & _ & _ & SPT & _ & _ & _ & S1 & S2 & S3 & _).
  pose proof (spZ_range regs) as SPR.
  destruct (tx_rel_lam B API F TS_STACK regs t b0 len0 cap0 txt acc bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1
              Lam peak cnt fail R1 LED NB) as (HQ & _).
  destruct CS as (Hin & _).
  destruct (HQ s k Hin) as (Hb & Hne).
  pose proof R1 as ((M1 & _) & _ & _ & _ & _ & _ & _ & INV1 & _).
  split; [lia|]. split; [lia|]. split.
  - intros X. destruct INV1 as (_ & [(C & _)|(Cp & Hb1 & _)]); [lia|].
    destruct (pairwise_in _ _ _ _ (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M1) Hb Hb1
                ltac:(intros E; inversion E; congruence)) as [D|D];
      unfold ranges_disjoint in D; cbn [fst snd] in D; lia.
  - right. right. right. exists (s - 16), (k + 16). split; [exact Hb|]. split; [exact Hne | lia].
Qed.

Lemma ts_all_end : ts_inv N.
Proof.
  intros regs2 pc2 mem2 md2 L2 A2 b2 cap2 HE R2 SV.
  destruct ts_num as (SPK & SP63 & SPal & SPT & Thi & RET & R10 & S1 & S2 & S3 & HF & M0 & INV0).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  pose proof R2 as ((M2 & _) & _ & _ & _ & _ & _ & _ & _ & RA2 & _).
  assert (RA2r : ro_agree rsegs mem2) by (rewrite <- SEGS; exact RA2).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ M2) as (Hh & Hlz & _).
  eapply (sr_evt_n B SEGS regs2 pc2 mem2 md2 _ _ Hh Hlz RA2r HE).
  intros ms' (can & s0 & HQ & HREL & RS & EQV).
  unfold ts_Q in HQ.
  destruct HQ as [(_ & HQ)|[(Hi & _)|[(Hi & _)|(Hi & _)]]]; [|lia..].
  destruct HQ as (x5 & x6 & x7 & a3 & a4 & a5 & a6 & a7 & x28 & x29 & x30 & x31 & m' & -> & _ & _ & ->).
  destruct (ts_land N mem2 md2 L2 A2 b2 cap2 _ _ _ can ms' R2 SV (munch_refl _ _) (wmono_refl _ _) HREL RS EQV)
    as (EMS & HR & _ & R3 & _).
  assert (ESP : Z_to_bv 64 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -112 + 112) = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2).
  { replace (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -112 + 112) with (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2)) by lia.
    apply Z_to_bv_bv_unsigned. }
  rewrite ESP in HR.
  set (R1 := ms_regs ms') in *. set (mem1 := ms_mem ms') in *.
  assert (G1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 1 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) by gval HR.
  assert (G2 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 2 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) by gval HR.
  assert (Sp1 : spZ R1 = spZ regs) by (unfold spZ; rewrite G2; reflexivity).
  assert (RP1 : regs_preserved regs R1) by regs_pres HR.
  rewrite EMS.
  replace (seg_rom rsegs) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B)) by (rewrite SEGS; reflexivity).
  change (Z_to_bv 64 0x154b8) with (Z_to_bv 64 TX_PUT).
  pose proof R3 as (_ & _ & _ & _ & _ & _ & _ & _ & RA3 & _).
  eapply (tx_put_call B API SEGS ERRB AX CTX F TXP TS_STACK L A regs mem md t b0 len0 cap0 txt bnd (plen (strp bs)) NEED (accs bs N)
            L2 A2 mem1 md2 b2 cap2 (ksb bs N) R1 0x10394 1 [Z_to_bv 8 34] [] _ ST R3).
  - rewrite <- ksb_full. reflexivity.
  - rewrite Sp1. unfold TS_STACK. lia.
  - rewrite Sp1. lia.
  - rewrite Sp1. exact SPal.
  - rewrite G1. exact RET.
  - gval HR.
  - gval HR.
  - gval HR.
  - gval HR.
  - lia.
  - lia.
  - lia.
  - apply (img1 B API SEGS ERRB AX CTX HG); [exact RA3 | vm_compute; reflexivity | vm_compute; reflexivity].
  - reflexivity.
  - intros x Hx. assert (x = 0) as -> by lia. rewrite Sp1.
    split; [unfold spZ in *; lia|]. split; [unfold spZ, TX_STACK, REALLOC_STACK, ALLOC_STACK in *; lia|].
    split.
    + intros X. pose proof R3 as ((M3 & _) & _ & _ & _ & _ & _ & _ & INV3 & _).
      destruct (inv_low B API SEGS ERRB AX CTX _ _ _ _ _ _ _ _ _ M3 INV3 X) as [_ NI].
      apply NI. apply (ro_img B SEGS); [lia | vm_compute; reflexivity].
    + right. right. left. rewrite SEGS. vm_compute. reflexivity.
  - rewrite accs_len, wstr_len. pose proof (escaped_le bs (Z.to_nat N)). rewrite Nat2Z.id, firstn_all. lia.
  - intros L3 A3 regs3 mem3 md3 RP (b3 & cap3 & R4) _.
    apply SR_ret. exists L3, A3, regs3, mem3, md3.
    split; [rewrite G1, SEGS; reflexivity|].
    split; [intros r Hr; rewrite (RP r Hr); exact (RP1 r Hr)|].
    rewrite accs_full, ksb_full in R4.
    split; [exists b3, cap3; exact R4|].
    split.
    + exact (proj1 (tx_rel_ledger B API F (ts_gst B API SEGS ERRB AX CTX HG) TS_STACK regs t b0 len0 cap0 txt _ bnd
                      L A mem md L3 A3 mem3 md3
                      b3 cap3 _ Lam peak cnt fail R4 M0 ltac:(unfold TS_STACK, TX_STACK, REALLOC_STACK, ALLOC_STACK; lia)
                      ltac:(unfold TS_STACK, TX_STACK, REALLOC_STACK, ALLOC_STACK; lia) SPT INV0 LED NB)).
    + exact (proj1 (tx_rel_cstr B API F TS_STACK regs t b0 len0 cap0 txt _ bnd L A mem md L3 A3 mem3 md3
                      b3 cap3 _ Lam peak cnt fail s k bs R4 LED NB CS)).
Qed.

Lemma ts_resume1 : forall i regs3 mem3 md3 L3 A3 b3 cap3,
  0 <= i < N ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 2 = Z_to_bv 64 FP -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 3 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 4 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 8 = Z_to_bv 64 t ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 9 = Z_to_bv 64 (s + i) ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 18 = Z_to_bv 64 0x102e9 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 19 = Z_to_bv 64 92 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 20 = Z_to_bv 64 9 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 21 = Z_to_bv 64 48 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 22 = Z_to_bv 64 (2 ^ 64 - 1) -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 23 = Z_to_bv 64 34 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 24 = Z_to_bv 64 32 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 25 = Z_to_bv 64 13 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 26 = Z_to_bv 64 10 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 27 = Z_to_bv 64 0x104a8 ->
  tx_relx B API F TS_STACK regs t b0 len0 cap0 txt (accs bs (i + 1)) bnd L A mem md L3 A3 mem3 md3 b3 cap3 (ksb bs (i + 1)) ->
  rw_cells rsegs mem3 (FP + 8) SVC ->
  ts_inv (i + 1) ->
  SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs3 (Z_to_bv 64 0x159e8) mem3 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md3) PP.
Proof.
  intros i regs3 mem3 md3 L3 A3 b3 cap3 Hi G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 R3 SV IH.
  destruct ts_num as (SPK & SP63 & SPal & SPT & Thi & RET & R10 & S1 & S2 & S3 & HF & M0 & INV0).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  destruct (ts_norm _ mem3 md3 L3 A3 b3 cap3 _ R3 SV) as (HBN & (j & RCN) & SVN & MIN & HXN).
  destruct (cat_facts bs (i + 1) HF ltac:(lia)) as [Hc Hcn].
  apply (IH regs3 (Z_to_bv 64 0x159e8) mem3 md3 L3 A3 b3 cap3); [| exact R3 | exact SV].
  unfold canR. rewrite G2, G3, G4, G8, G9, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27.
  replace (s + (i + 1)) with (s + i + 1) by lia.
  unfold spZ in *.
  eapply ts_go1 with (j := j);
    [lia | lia | lia | lia | lia | exact Hc | lia | exact Hcn | | exact RCN | exact SVN | exact MIN | exact HXN].
  replace (s + i + 1) with (s + (i + 1)) by lia. apply str_read; [exact HBN | lia].
Qed.

Lemma ts_case_p : forall i mem2 md2 L2 A2 b2 cap2 ms' can x5 x6 x7 a3 a4 a5 a6 a7 x28 x29 x30 x31 m',
  0 <= i < N -> 32 <= cat bs i -> cat bs i <> 34 -> cat bs i <> 92 -> ts_inv (i + 1) ->
  tx_relx B API F TS_STACK regs t b0 len0 cap0 txt (accs bs i) bnd L A mem md L2 A2 mem2 md2 b2 cap2 (ksb bs i) ->
  rw_cells rsegs mem2 (FP + 8) SVC ->
  munch [(FP, FP + 8)] (normalize rsegs mem2) m' -> wmono rsegs (normalize rsegs mem2) m' ->
  ms_rel rsegs can (MS (mkR (Z_to_bv 64 0x159e8) (Z_to_bv 64 FP) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) x5 x6 x7
                          (Z_to_bv 64 t) (Z_to_bv 64 (s + i)) (Z_to_bv 64 t) (Z_to_bv 64 (s + i)) (Z_to_bv 64 1)
                          a3 a4 a5 a6 a7 (Z_to_bv 64 0x102e9) (Z_to_bv 64 92) (Z_to_bv 64 9) (Z_to_bv 64 48)
                          (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 34) (Z_to_bv 64 32) (Z_to_bv 64 13) (Z_to_bv 64 10)
                          (Z_to_bv 64 0x104a8) x28 x29 x30 x31)
                       fp_regs (Z_to_bv 64 0x154b8) fp_csr None m' (seg_rom rsegs)) ->
  ro_same rsegs mem2 (ms_mem can) -> Regs6ss.ms_eqv can ms' ->
  SR (ms_segs B) (mkCfg ms' md2) PP.
Proof.
  intros i mem2 md2 L2 A2 b2 cap2 ms' can x5 x6 x7 a3 a4 a5 a6 a7 x28 x29 x30 x31 m'
    Hi Hc1 Hc2 Hc3 IH R2 SV MU WM HREL RS EQV.
  destruct ts_num as (SPK & SP63 & SPal & SPT & Thi & RET & R10 & S1 & S2 & S3 & HF & M0 & INV0).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  destruct (ts_land i mem2 md2 L2 A2 b2 cap2 _ _ _ can ms' R2 SV MU WM HREL RS EQV) as (EMS & HR & _ & R3 & SV3).
  set (R1 := ms_regs ms') in *. set (mem1 := ms_mem ms') in *.
  assert (G1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 1 = Z_to_bv 64 0x159e8) by gval HR.
  assert (G2 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 2 = Z_to_bv 64 FP) by gval HR.
  assert (Sp1 : spZ R1 = FP).
  { unfold spZ in *. transitivity (bv_unsigned (Z_to_bv 64 FP)); [f_equal; exact G2 | apply unsigned_lit; lia]. }
  rewrite EMS.
  replace (seg_rom rsegs) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B)) by (rewrite SEGS; reflexivity).
  change (Z_to_bv 64 0x154b8) with (Z_to_bv 64 TX_PUT).
  destruct (tx_rel_cstr B API F TS_STACK regs t b0 len0 cap0 txt _ bnd L A mem md L2 A2 mem1 md2 b2 cap2 _
              Lam peak cnt fail s k bs R3 LED NB CS) as ((_ & _ & _ & HB1) & _).
  rewrite SEGS in HB1.
  pose proof (cat_facts bs i HF ltac:(lia)) as [Hc _].
  destruct (ksb_split bs i Hi) as (rest & ERS).
  eapply (tx_put_call B API SEGS ERRB AX CTX F TXP TS_STACK L A regs mem md t b0 len0 cap0 txt bnd (plen (strp bs)) NEED (accs bs i)
            L2 A2 mem1 md2 b2 cap2 (ksb bs i) R1 (s + i) 1 [Z_to_bv 8 (cat bs i)] rest _ ST R3).
  - rewrite ERS, spcs_p by assumption. reflexivity.
  - rewrite Sp1. unfold spZ, TS_STACK in *. lia.
  - rewrite Sp1. unfold spZ in *. lia.
  - rewrite Sp1. unfold spZ in *. Z.div_mod_to_equations. lia.
  - rewrite G1. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok. vm_compute. reflexivity.
  - gval HR.
  - gval HR.
  - gval HR.
  - gval HR.
  - lia.
  - lia.
  - lia.
  - apply (bytes_at_mbytes B SEGS) in HB1. unfold cat.
    exact (mbytes_one B API SEGS ERRB AX CTX HG mem1 s (bs ++ [0]) i HB1
             ltac:(rewrite length_app; cbn [length]; lia)).
  - reflexivity.
  - eapply (str_src_ok (accs bs i) L2 A2 mem1 md2 b2 cap2 _ R1 i R3 Hi).
    rewrite Sp1. unfold spZ, TX_STACK, REALLOC_STACK, ALLOC_STACK in *. lia.
  - rewrite accs_len, wstr_len. pose proof (escaped_snoc_len bs i Hi). pose proof (piece_len (cat bs i) Hc). lia.
  - intros L3 A3 regs3 mem3 md3 RP (b3 & cap3 & R4) KEEP.
    rewrite G1.
    apply (ts_resume1 i regs3 mem3 md3 L3 A3 b3 cap3 Hi); try (rpa RP HR).
    + rewrite accs_step, ksb_step by lia. rewrite special_p, spcs_p by assumption. exact R4.
    + exact (ts_keep R1 mem1 mem3 Sp1 SV3 KEEP).
    + exact IH.
Qed.

Lemma ts_case_c : forall i mem2 md2 L2 A2 b2 cap2 ms' can x5 x6 x7 a3 a4 a5 a6 a7 x28 x29 x30 x31 m',
  0 <= i < N -> cat bs i < 32 -> ts_inv (i + 1) ->
  tx_relx B API F TS_STACK regs t b0 len0 cap0 txt (accs bs i) bnd L A mem md L2 A2 mem2 md2 b2 cap2 (ksb bs i) ->
  rw_cells rsegs mem2 (FP + 8) SVC ->
  munch [(FP, FP + 8)] (normalize rsegs mem2) m' -> wmono rsegs (normalize rsegs mem2) m' ->
  bytes_at rsegs m' (FP + 2) (map (Z_to_bv 8) (esc (cat bs i))) ->
  ms_rel rsegs can (MS (mkR (Z_to_bv 64 0x159e8) (Z_to_bv 64 FP) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) x5 x6 x7
                          (Z_to_bv 64 t) (Z_to_bv 64 (s + i)) (Z_to_bv 64 t) (Z_to_bv 64 (FP + 2))
                          (Z_to_bv 64 (Z.of_nat (length (esc (cat bs i)))))
                          a3 a4 a5 a6 a7 (Z_to_bv 64 0x102e9) (Z_to_bv 64 92) (Z_to_bv 64 9) (Z_to_bv 64 48)
                          (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 34) (Z_to_bv 64 32) (Z_to_bv 64 13) (Z_to_bv 64 10)
                          (Z_to_bv 64 0x104a8) x28 x29 x30 x31)
                       fp_regs (Z_to_bv 64 0x154b8) fp_csr None m' (seg_rom rsegs)) ->
  ro_same rsegs mem2 (ms_mem can) -> Regs6ss.ms_eqv can ms' ->
  SR (ms_segs B) (mkCfg ms' md2) PP.
Proof.
  intros i mem2 md2 L2 A2 b2 cap2 ms' can x5 x6 x7 a3 a4 a5 a6 a7 x28 x29 x30 x31 m'
    Hi Hc IH R2 SV MU WM HB HREL RS EQV.
  destruct ts_num as (SPK & SP63 & SPal & SPT & Thi & RET & R10 & S1 & S2 & S3 & HF & M0 & INV0).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  destruct (ts_land i mem2 md2 L2 A2 b2 cap2 _ _ _ can ms' R2 SV MU WM HREL RS EQV) as (EMS & HR & MRL & R3 & SV3).
  pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ MRL) HB) as HB1.
  set (R1 := ms_regs ms') in *. set (mem1 := ms_mem ms') in *.
  assert (G1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 1 = Z_to_bv 64 0x159e8) by gval HR.
  assert (G2 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 2 = Z_to_bv 64 FP) by gval HR.
  assert (Sp1 : spZ R1 = FP).
  { unfold spZ in *. transitivity (bv_unsigned (Z_to_bv 64 FP)); [f_equal; exact G2 | apply unsigned_lit; lia]. }
  rewrite EMS.
  replace (seg_rom rsegs) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B)) by (rewrite SEGS; reflexivity).
  change (Z_to_bv 64 0x154b8) with (Z_to_bv 64 TX_PUT).
  pose proof (cat_facts bs i HF ltac:(lia)) as [Hc0 _].
  assert (EL : 1 <= Z.of_nat (length (esc (cat bs i))) <= 6)
    by (rewrite <- (special_c (cat bs i)) by lia; apply piece_len; lia).
  pose proof R3 as ((M3 & _) & _ & _ & _ & _ & _ & _ & INV3 & _).
  destruct (inv_range B API SEGS ERRB AX CTX _ _ _ _ _ _ _ _ M3 INV3) as (_ & _ & _ & IR3).
  destruct (ksb_split bs i Hi) as (rest & ERS).
  eapply (tx_put_call B API SEGS ERRB AX CTX F TXP TS_STACK L A regs mem md t b0 len0 cap0 txt bnd (plen (strp bs)) NEED (accs bs i)
            L2 A2 mem1 md2 b2 cap2 (ksb bs i) R1 (FP + 2) (Z.of_nat (length (esc (cat bs i))))
            (map (Z_to_bv 8) (esc (cat bs i))) rest _ ST R3).
  - rewrite ERS, spcs_c by lia. reflexivity.
  - rewrite Sp1. unfold spZ, TS_STACK in *. lia.
  - rewrite Sp1. unfold spZ in *. lia.
  - rewrite Sp1. unfold spZ in *. Z.div_mod_to_equations. lia.
  - rewrite G1. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok. vm_compute. reflexivity.
  - gval HR.
  - gval HR.
  - gval HR.
  - gval HR.
  - unfold spZ in *. lia.
  - lia.
  - unfold spZ in *. lia.
  - exact (bytes_at_mbytes B SEGS _ _ _ HB1).
  - rewrite length_map. reflexivity.
  - intros x Hx. rewrite Sp1. unfold spZ, TX_STACK, REALLOC_STACK, ALLOC_STACK in *.
    split; [lia|]. split; [lia|]. split; [lia|]. right. left. lia.
  - rewrite accs_len, wstr_len. pose proof (escaped_snoc_len bs i Hi) as EE. rewrite special_c in EE by lia. lia.
  - intros L3 A3 regs3 mem3 md3 RP (b3 & cap3 & R4) KEEP.
    rewrite G1.
    apply (ts_resume1 i regs3 mem3 md3 L3 A3 b3 cap3 Hi); try (rpa RP HR).
    + rewrite accs_step, ksb_step by lia. rewrite special_c, spcs_c by lia. exact R4.
    + exact (ts_keep R1 mem1 mem3 Sp1 SV3 KEEP).
    + exact IH.
Qed.

Lemma ts_case_b : forall i mem2 md2 L2 A2 b2 cap2 ms' can x5 x6 x7 a3 a4 a5 a6 a7 x28 x29 x30 x31 m',
  0 <= i < N -> cat bs i = 34 \/ cat bs i = 92 -> ts_inv (i + 1) ->
  tx_relx B API F TS_STACK regs t b0 len0 cap0 txt (accs bs i) bnd L A mem md L2 A2 mem2 md2 b2 cap2 (ksb bs i) ->
  rw_cells rsegs mem2 (FP + 8) SVC ->
  munch [(FP, FP + 8)] (normalize rsegs mem2) m' -> wmono rsegs (normalize rsegs mem2) m' ->
  ms_rel rsegs can (MS (mkR (Z_to_bv 64 0x159d8) (Z_to_bv 64 FP) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) x5 x6 x7
                          (Z_to_bv 64 t) (Z_to_bv 64 (s + i)) (Z_to_bv 64 t) (Z_to_bv 64 0x102e9) (Z_to_bv 64 1)
                          a3 a4 a5 a6 a7 (Z_to_bv 64 0x102e9) (Z_to_bv 64 92) (Z_to_bv 64 9) (Z_to_bv 64 48)
                          (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 34) (Z_to_bv 64 32) (Z_to_bv 64 13) (Z_to_bv 64 10)
                          (Z_to_bv 64 0x104a8) x28 x29 x30 x31)
                       fp_regs (Z_to_bv 64 0x154b8) fp_csr None m' (seg_rom rsegs)) ->
  ro_same rsegs mem2 (ms_mem can) -> Regs6ss.ms_eqv can ms' ->
  SR (ms_segs B) (mkCfg ms' md2) PP.
Proof.
  intros i mem2 md2 L2 A2 b2 cap2 ms' can x5 x6 x7 a3 a4 a5 a6 a7 x28 x29 x30 x31 m'
    Hi Hc IH R2 SV MU WM HREL RS EQV.
  destruct ts_num as (SPK & SP63 & SPal & SPT & Thi & RET & R10 & S1 & S2 & S3 & HF & M0 & INV0).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  destruct (ts_land i mem2 md2 L2 A2 b2 cap2 _ _ _ can ms' R2 SV MU WM HREL RS EQV) as (EMS & HR & _ & R3 & SV3).
  set (R1 := ms_regs ms') in *. set (mem1 := ms_mem ms') in *.
  assert (G1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 1 = Z_to_bv 64 0x159d8) by gval HR.
  assert (G2 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 2 = Z_to_bv 64 FP) by gval HR.
  assert (Sp1 : spZ R1 = FP).
  { unfold spZ in *. transitivity (bv_unsigned (Z_to_bv 64 FP)); [f_equal; exact G2 | apply unsigned_lit; lia]. }
  rewrite EMS.
  replace (seg_rom rsegs) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B)) by (rewrite SEGS; reflexivity).
  change (Z_to_bv 64 0x154b8) with (Z_to_bv 64 TX_PUT).
  pose proof (cat_facts bs i HF ltac:(lia)) as [Hc0 _].
  pose proof R3 as ((M3 & _) & _ & _ & _ & _ & _ & _ & INV3 & RA3 & _).
  pose proof (escaped_snoc_len bs i Hi) as EE. rewrite special_q in EE by exact Hc. cbn [length Z.of_nat] in EE.
  destruct (ksb_split bs i Hi) as (rest & ERS).
  eapply (tx_put_call B API SEGS ERRB AX CTX F TXP TS_STACK L A regs mem md t b0 len0 cap0 txt bnd (plen (strp bs)) NEED (accs bs i)
            L2 A2 mem1 md2 b2 cap2 (ksb bs i) R1 0x102e9 1 [Z_to_bv 8 92] ([1] ++ rest) _ ST R3).
  - rewrite ERS, spcs_b by exact Hc. reflexivity.
  - rewrite Sp1. unfold spZ, TS_STACK in *. lia.
  - rewrite Sp1. unfold spZ in *. lia.
  - rewrite Sp1. unfold spZ in *. Z.div_mod_to_equations. lia.
  - rewrite G1. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok. vm_compute. reflexivity.
  - gval HR.
  - gval HR.
  - gval HR.
  - gval HR.
  - lia.
  - lia.
  - lia.
  - apply (img1 B API SEGS ERRB AX CTX HG); [exact RA3 | vm_compute; reflexivity | vm_compute; reflexivity].
  - reflexivity.
  - intros x Hx. assert (x = 0) as -> by lia. rewrite Sp1.
    split; [unfold spZ in *; lia|]. split; [unfold spZ, TX_STACK, REALLOC_STACK, ALLOC_STACK in *; lia|].
    split.
    + intros X. destruct (inv_low B API SEGS ERRB AX CTX _ _ _ _ _ _ _ _ _ M3 INV3 X) as [_ NI].
      apply NI. apply (ro_img B SEGS); [lia | vm_compute; reflexivity].
    + right. right. left. rewrite SEGS. vm_compute. reflexivity.
  - rewrite accs_len, wstr_len. lia.
  - intros L3 A3 regs3 mem3 md3 RP (b3 & cap3 & R4) KEEP.
    rewrite G1.
    pose proof (ts_keep R1 mem1 mem3 Sp1 SV3 KEEP) as SV4.
    pose proof R4 as ((M4 & _) & _).
    destruct (mr_model _ _ (aa_laws API) _ _ _ _ M4) as (Hh4 & Hlz4 & _).
    eapply (sr_evt B SEGS regs3 (Z_to_bv 64 0x159d8) mem3 md3 _ _ Hh4 Hlz4); [apply ts_call2 |].
    intros ms4 (can4 & HQ4 & EQV4).
    destruct HQ4 as (y5 & y6 & y7 & c3 & c4 & c5 & c6 & c7 & y28 & y29 & y30 & y31 & m4 & -> & _ & _ & ->).
    destruct (eqv_final _ _ _ _ _ _ _ EQV4 eq_refl eq_refl) as (EMS4 & HR4).
    assert (K2 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 2 = Z_to_bv 64 FP) by rp RP HR 2.
    assert (K3 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 3 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) by rp RP HR 3.
    assert (K4 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 4 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) by rp RP HR 4.
    assert (K8 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 8 = Z_to_bv 64 t) by rp RP HR 8.
    assert (K9 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 9 = Z_to_bv 64 (s + i)) by rp RP HR 9.
    assert (K18 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 18 = Z_to_bv 64 0x102e9) by rp RP HR 18.
    assert (K19 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 19 = Z_to_bv 64 92) by rp RP HR 19.
    assert (K20 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 20 = Z_to_bv 64 9) by rp RP HR 20.
    assert (K21 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 21 = Z_to_bv 64 48) by rp RP HR 21.
    assert (K22 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 22 = Z_to_bv 64 (2 ^ 64 - 1)) by rp RP HR 22.
    assert (K23 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 23 = Z_to_bv 64 34) by rp RP HR 23.
    assert (K24 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 24 = Z_to_bv 64 32) by rp RP HR 24.
    assert (K25 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 25 = Z_to_bv 64 13) by rp RP HR 25.
    assert (K26 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 26 = Z_to_bv 64 10) by rp RP HR 26.
    assert (K27 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 27 = Z_to_bv 64 0x104a8) by rp RP HR 27.
    rewrite K2, K3, K4, K8, K9, K18, K19, K20, K21, K22, K23, K24, K25, K26, K27 in HR4.
    set (R4' := ms_regs ms4) in *.
    assert (G41 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R4' 1 = Z_to_bv 64 0x159e8) by gval HR4.
    assert (G42 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R4' 2 = Z_to_bv 64 FP) by gval HR4.
    assert (Sp4 : spZ R4' = FP).
    { unfold spZ in *. transitivity (bv_unsigned (Z_to_bv 64 FP)); [f_equal; exact G42 | apply unsigned_lit; lia]. }
    rewrite EMS4.
    replace (seg_rom rsegs) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B)) by (rewrite SEGS; reflexivity).
    change (Z_to_bv 64 0x154b8) with (Z_to_bv 64 TX_PUT).
    destruct (tx_rel_cstr B API F TS_STACK regs t b0 len0 cap0 txt _ bnd L A mem md L3 A3 mem3 md3 b3 cap3 _
                Lam peak cnt fail s k bs R4 LED NB CS) as ((_ & _ & _ & HB3) & _).
    rewrite SEGS in HB3. apply (bytes_at_mbytes B SEGS) in HB3.
    eapply (tx_put_call B API SEGS ERRB AX CTX F TXP TS_STACK L A regs mem md t b0 len0 cap0 txt bnd (plen (strp bs)) NEED
              (accs bs i ++ [Z_to_bv 8 92]) L3 A3 mem3 md3 b3 cap3 (ksb bs i ++ [1]) R4' (s + i) 1 [Z_to_bv 8 (cat bs i)] rest _
              ST R4).
    + rewrite ERS, spcs_b by exact Hc. rewrite <- app_assoc. reflexivity.
    + rewrite Sp4. unfold spZ, TS_STACK in *. lia.
    + rewrite Sp4. unfold spZ in *. lia.
    + rewrite Sp4. unfold spZ in *. Z.div_mod_to_equations. lia.
    + rewrite G41. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok. vm_compute. reflexivity.
    + gval HR4.
    + gval HR4.
    + gval HR4.
    + gval HR4.
    + lia.
    + lia.
    + lia.
    + unfold cat. exact (mbytes_one B API SEGS ERRB AX CTX HG mem3 s (bs ++ [0]) i HB3
                           ltac:(rewrite length_app; cbn [length]; lia)).
    + reflexivity.
    + eapply (str_src_ok (accs bs i ++ [Z_to_bv 8 92]) L3 A3 mem3 md3 b3 cap3 _ R4' i R4 Hi).
      rewrite Sp4. unfold spZ, TX_STACK, REALLOC_STACK, ALLOC_STACK in *. lia.
    + rewrite length_app, Nat2Z.inj_add, accs_len, wstr_len. cbn [length Z.of_nat]. lia.
    + intros L5 A5 regs5 mem5 md5 RP5 (b5 & cap5 & R5) KEEP5.
      rewrite G41.
      apply (ts_resume1 i regs5 mem5 md5 L5 A5 b5 cap5 Hi); try (rpa RP5 HR4).
      * assert (E : accs bs (i + 1) = (accs bs i ++ [Z_to_bv 8 92]) ++ [Z_to_bv 8 (cat bs i)]).
        { rewrite accs_step by lia. rewrite special_q by exact Hc. rewrite <- app_assoc. reflexivity. }
        assert (EK : ksb bs (i + 1) = (ksb bs i ++ [1]) ++ [1]).
        { rewrite ksb_step by lia. rewrite spcs_b by exact Hc. rewrite <- app_assoc. reflexivity. }
        rewrite E, EK. exact R5.
      * exact (ts_keep R4' mem3 mem5 Sp4 SV4 KEEP5).
      * exact IH.
Qed.

Lemma ts_step : forall i, 0 <= i < N -> ts_inv (i + 1) -> ts_inv i.
Proof.
  intros i Hi IH regs2 pc2 mem2 md2 L2 A2 b2 cap2 HE R2 SV.
  pose proof R2 as ((M2 & _) & _ & _ & _ & _ & _ & _ & _ & RA2 & _).
  assert (RA2r : ro_agree rsegs mem2) by (rewrite <- SEGS; exact RA2).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ M2) as (Hh & Hlz & _).
  eapply (sr_evt_n B SEGS regs2 pc2 mem2 md2 _ _ Hh Hlz RA2r HE).
  intros ms' (can & s0 & HQ & HREL & RS & EQV).
  unfold ts_Q in HQ.
  destruct HQ as [(Hi' & _)|[(_ & Hc & HQ)|[(_ & Hc1 & Hc2 & Hc3 & HQ)|(_ & Hc & HQ)]]]; [lia | | |].
  - destruct HQ as (x5 & x6 & x7 & a3 & a4 & a5 & a6 & a7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & _).
    exact (ts_case_b i mem2 md2 L2 A2 b2 cap2 ms' can x5 x6 x7 a3 a4 a5 a6 a7 x28 x29 x30 x31 m'
             Hi Hc IH R2 SV MU WM HREL RS EQV).
  - destruct HQ as (x5 & x6 & x7 & a3 & a4 & a5 & a6 & a7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & _).
    exact (ts_case_p i mem2 md2 L2 A2 b2 cap2 ms' can x5 x6 x7 a3 a4 a5 a6 a7 x28 x29 x30 x31 m'
             Hi Hc1 Hc2 Hc3 IH R2 SV MU WM HREL RS EQV).
  - destruct HQ as (x5 & x6 & x7 & a3 & a4 & a5 & a6 & a7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & HB).
    exact (ts_case_c i mem2 md2 L2 A2 b2 cap2 ms' can x5 x6 x7 a3 a4 a5 a6 a7 x28 x29 x30 x31 m'
             Hi Hc IH R2 SV MU WM HB HREL RS EQV).
Qed.

Lemma ts_all : forall n : nat, Z.of_nat n <= N -> ts_inv (N - Z.of_nat n).
Proof.
  induction n as [|n IH]; intros Hn.
  - replace (N - Z.of_nat 0) with N by lia. exact ts_all_end.
  - apply ts_step; [lia|]. replace (N - Z.of_nat (S n) + 1) with (N - Z.of_nat n) by lia. apply IH. lia.
Qed.

Lemma ts_resume0 : forall regs3 mem3 md3 L3 A3 b3 cap3,
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 2 = Z_to_bv 64 FP -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 3 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 4 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 8 = Z_to_bv 64 t ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 9 = Z_to_bv 64 s ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 18 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 18 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 19 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 19 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 20 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 20 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 21 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 21 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 22 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 22 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 23 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 23 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 24 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 24 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 25 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 25 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 26 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 26 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 27 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 27 ->
  tx_relx B API F TS_STACK regs t b0 len0 cap0 txt (accs bs 0) bnd L A mem md L3 A3 mem3 md3 b3 cap3 (ksb bs 0) ->
  rw_cells rsegs mem3 (FP + 8) SVC ->
  SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs3 (Z_to_bv 64 0x15928) mem3 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md3) PP.
Proof.
  intros regs3 mem3 md3 L3 A3 b3 cap3 G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 R3 SV.
  destruct ts_num as (SPK & SP63 & SPal & SPT & Thi & RET & R10 & S1 & S2 & S3 & HF & M0 & INV0).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  destruct (ts_norm _ mem3 md3 L3 A3 b3 cap3 _ R3 SV) as (HBN & (j & RCN) & SVN & MIN & HXN).
  destruct (cat_facts bs 0 HF ltac:(lia)) as [Hc Hcn].
  pose proof (ts_all (length bs) ltac:(lia)) as H0. replace (N - Z.of_nat (length bs)) with 0 in H0 by lia.
  apply (H0 regs3 (Z_to_bv 64 0x15928) mem3 md3 L3 A3 b3 cap3); [| exact R3 | exact SV].
  unfold canR. rewrite G2, G3, G4, G8, G9, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27.
  replace (s + 0) with s by lia.
  unfold spZ in *.
  eapply ts_go0 with (j := j);
    [lia | lia | lia | lia | exact Hc | lia | | | exact RCN | exact SVN | exact MIN | exact HXN].
  - rewrite Hcn. split; intro; lia.
  - pose proof (str_read _ 0 HBN ltac:(lia)) as RD0. rewrite Z.add_0_r in RD0. exact RD0.
Qed.

End Loop.

Theorem tx_string_holds : tx_put_contract B API F -> tx_string_contract B API F.
Proof.
  intros TXP. unfold tx_string_contract.
  intros L A regs mem md t s k b0 len0 cap0 bs txt bnd Lam peak cnt fail. cbv zeta. intros ST R11 LED CS NB.
  destruct (ts_num L A regs mem md t s k b0 len0 cap0 bs txt bnd Lam peak cnt fail TXP ST LED CS NB)
    as (SPK & SP63 & SPal & SPT & Thi & RET & R10 & S1 & S2 & S3 & HF & M & INV).
  pose proof ST as ((_ & W & BD & _ & _ & _ & _ & SWR & _ & _ & _) & IN & RA & _ & _ & _ & _ & TW & _ & _ & _ & REC &
                    _ & _ & RES & _).
  destruct (tx_start_facts B API SEGS ERRB AX CTX F _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST) as (_ & _ & _ & _ & _ & WIN & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ M) as (Hh & Hlz & _).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  unfold TS_STACK, TX_STACK, REALLOC_STACK, ALLOC_STACK in SWR.
  assert (RAr : ro_agree rsegs mem) by (rewrite <- SEGS; exact RA).
  assert (FRP : forall i, 0 <= i < 112 -> present mem (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -112 + i)).
  { intros i Hi. unfold spZ in *. apply (present_of_writable B SEGS); [lia | left; lia | apply SWR; lia]. }
  edestruct (rw_of_present mem (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -112) 112) as [j FRJ];
    [unfold spZ in *; lia | unfold spZ in *; lia | lia | exact FRP |].
  change (Z.to_nat 112) with 112%nat in FRJ.
  assert (FRN : rw_cells rsegs (normalize rsegs mem) (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -112) [CB 112 j]).
  { apply rw_cells_norm; [exact RAr | exact FRJ |]. intros i Hi. cbn in Hi. unfold spZ in *.
    apply (ro_false B SEGS); [lia | left; lia]. }
  pose proof (mem_inv_normalize rsegs mem) as MIN.
  eapply (sr_evt_n B SEGS regs _ mem md); [exact Hh | exact Hlz | exact RAr | |].
  { unfold TX_STRING. rewrite R10, R11. eapply ts_pro; [unfold spZ in *; lia | lia | exact FRN | exact MIN]. }
  intros ms' (can & s0 & HQ & HREL & RS & EQV).
  destruct HQ as (x5 & x6 & x7 & a3 & a4 & a5 & a6 & a7 & x28 & x29 & x30 & x31 & m0' & -> & MU & WM & (j' & FR0)).
  destruct (final_n _ _ _ _ _ _ _ _ HREL EQV eq_refl eq_refl) as (EMS & HR & MRL & EM).
  rewrite <- EM in RS.
  pose proof (munch_rel rsegs _ mem (normalize rsegs mem) (ms_mem ms') m0' (mem_rel_normalize rsegs mem RAr) MRL RS MU)
    as MU'.
  pose proof (wmono_rel rsegs mem (normalize rsegs mem) (ms_mem ms') m0' (mem_rel_normalize rsegs mem RAr) MRL RS WM)
    as WM'.
  pose proof (ro_agree_same rsegs mem (ms_mem ms') RAr RS) as RA1.
  pose proof (rw_tail_cb _ _ _ _ (rw_cells_rel _ _ _ _ MRL FR0)) as SV1.
  clear MU WM FR0.
  set (R1 := ms_regs ms') in *. set (mem1 := ms_mem ms') in *.
  assert (R0 : tx_relx B API F TS_STACK regs t b0 len0 cap0 txt [] bnd L A mem md L A mem1 md b0 cap0 []).
  { apply (tx_rel_frame B API SEGS ERRB AX CTX F TS_STACK regs t b0 len0 cap0 txt bnd L A mem md mem1
             (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -112) (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -112 + 112)); try assumption.
    - rewrite SEGS. exact RA1.
    - intros a Ha. unfold spZ, TS_STACK, TX_STACK, REALLOC_STACK, ALLOC_STACK in *. lia. }
  assert (G1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 1 = Z_to_bv 64 0x15928) by gval HR.
  assert (G2 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 2 = Z_to_bv 64 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -112)) by gval HR.
  assert (Sp1 : spZ R1 = bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -112).
  { unfold spZ in *. transitivity (bv_unsigned (Z_to_bv 64 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -112)));
      [f_equal; exact G2 | apply unsigned_lit; lia]. }
  rewrite EMS.
  replace (seg_rom rsegs) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B)) by (rewrite SEGS; reflexivity).
  change (Z_to_bv 64 0x154b8) with (Z_to_bv 64 TX_PUT).
  eapply (tx_put_call B API SEGS ERRB AX CTX F TXP TS_STACK L A regs mem md t b0 len0 cap0 txt bnd (plen (strp bs)) _ [] L A mem1 md
            b0 cap0 [] R1 0x10394 1 [Z_to_bv 8 34] (plen (concat (map spcs bs) ++ [[34]])) _ ST R0).
  - reflexivity.
  - rewrite Sp1. unfold spZ, TS_STACK in *. lia.
  - rewrite Sp1. unfold spZ in *. lia.
  - rewrite Sp1. unfold spZ in *. Z.div_mod_to_equations. lia.
  - rewrite G1. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok. vm_compute. reflexivity.
  - gval HR.
  - gval HR.
  - gval HR.
  - gval HR.
  - lia.
  - lia.
  - lia.
  - apply (img1 B API SEGS ERRB AX CTX HG); [rewrite SEGS; exact RA1 | vm_compute; reflexivity | vm_compute; reflexivity].
  - reflexivity.
  - intros x Hx. assert (x = 0) as -> by lia. rewrite Sp1.
    split; [unfold spZ in *; lia|]. split; [unfold spZ, TX_STACK, REALLOC_STACK, ALLOC_STACK in *; lia|].
    split.
    + intros X. pose proof R0 as ((M1 & _) & _ & _ & _ & _ & _ & _ & INV1 & _).
      destruct (inv_low B API SEGS ERRB AX CTX _ _ _ _ _ _ _ _ _ M1 INV1 X) as [_ NI].
      apply NI. apply (ro_img B SEGS); [lia | vm_compute; reflexivity].
    + right. right. left. rewrite SEGS. vm_compute. reflexivity.
  - cbn [length Z.of_nat]. rewrite wstr_len. lia.
  - intros L2 A2 regs2 mem2 md2 RP (b2 & cap2 & R2) KEEP.
    rewrite G1.
    apply (ts_resume0 L A regs mem md t s k b0 len0 cap0 bs txt bnd Lam peak cnt fail TXP ST LED CS NB
             regs2 mem2 md2 L2 A2 b2 cap2); try (rpa RP HR).
    + exact R2.
    + exact (ts_keep L A regs mem md t s k b0 len0 cap0 bs txt bnd Lam peak cnt fail TXP ST LED CS NB
               R1 mem1 mem2 Sp1 SV1 KEEP).
Qed.

End KB.
