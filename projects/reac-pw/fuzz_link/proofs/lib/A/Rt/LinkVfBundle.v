(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: relocated to omx-clap-core fuzz_manifest.asan (module paths). kcall generalizes A/AE3h.v vf_icpt_xcall (callee post handed in, regions after the
   stack region constrained by what they must avoid); kentry, kenv, st_ok_pc_mem_out and kstore0 are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSnpK.v, with its module paths changed; 741 of its 850 lines of code are new or changed and 228 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/FMsnprintfSk.v, with its module paths, module names and numbers changed; 196 of its 271 lines of code are new or changed and 775 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): the premise bundle of the two memory-FILE print
   contracts of LinkVfDefs.v (avfprintf_mf_realizes / afprintf_mf_realizes) as the runtime bodies
   ___interceptor_vfprintf 0x46a7c (LinkVfBody.v) and ___interceptor_fprintf 0x46e48 (LinkFpBody.v) carry it from
   their entry to the call of musl vfprintf 0x973e0, in the kit's vocabulary (FMsnprintfSk.v: sw_frame over the
   window [sp - K, sp), ARU with no user-poisoned range, which is AR by ARU_nil).
   - mf_pre: the parts of the contract that hold at every point of a body's walk: AR, the window, the FILE block apart
     from it, the FILE's words (amf_k / amf_dyn / amf_pend) and the fit k + |T| <= 1024, the read-only invariant
     arodata_okP, the stack-protector cells, the format family over (vmf_out K sp f), |T| < 2^31 - 1. Where the
     argument words lie is not in it (the vfprintf body reads them at ap, the fprintf body spills a2..a7 into its
     frame), so each body states them beside it;
   - mf_intro (from the contract's premises), mf_keep (a memory that changed only inside the window), mf_shrink (a
     callee's window inside it), mf_pcom (printf_common's premises at link's family and PCM_CR: consts_view from
     arodata_okP and AR, as disco's FMsnprintfRomO.v fm_cr_consts_of_arodata, through FMsnprintfCr.fm_cr_consts_view
     and RtBzAdapt.rom_viewO_of_ARm), mf_apply (musl vfprintf's contract applied to the bundle), mf_post_keep (the
     FILE post at a memory that kept the FILE block);
   - vmf_post: the post of both contracts, as a definition.
   arodata_okP is kept across a write to the window for any rlo rhi: a window byte the invariant covers would read
   as the image (seg_rom is None above the image), so it would be absent, and every window byte is present.
   The FILE record is link's (link_amf), the runtime's record PcapB. New file. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YI00 YI16 YK06.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE20 AE2y.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import SnUpoison.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMH_Base FMsnprintfImg FMsnprintfK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import PfFacts SnShared SnSx.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMsnprintfSk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFileSink AMemFile AD2l.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkVfDefs LinkPfPiece LinkVfInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require RT_pf_sh RT_pf_shU FMsnprintfFmI FMsnprintfCr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtBzAdapt.
Import ListNotations.
Open Scope Z_scope.

(* ---- the two regions of vmf_out ---- *)
Lemma Forall_vmf : forall (P : Z * Z -> Prop) K sp f, Forall P (vmf_out K sp f) <-> P (sp - K, K) /\ P (f, AMF_BLOCK).
Proof.
intros P K sp f. unfold vmf_out. split.
- intros HF. inversion HF as [|? ? H1 HF2]; subst. inversion HF2; subst. split; assumption.
- intros [H1 H2]. repeat (apply Forall_cons; [assumption|]). apply Forall_nil.
Qed.
Lemma pairwise_vmf : forall K sp f, pairwise zdisjoint (vmf_out K sp f) <-> zdisjoint (sp - K, K) (f, AMF_BLOCK).
Proof.
intros K sp f. unfold vmf_out. cbn [pairwise]. split.
- intros (H1 & _ & _). inversion H1; subst. assumption.
- intros H. split; [apply Forall_cons; [exact H | apply Forall_nil]|]. split; [apply Forall_nil | exact I].
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Abbreviation H W := (w_H W).
#[local] Abbreviation B := PcapB.
#[local] Abbreviation MS := link_amf.
(* ---- the FILE's words at a memory that kept the FILE block ---- *)
Lemma mf_file_keep : forall (m m' : word -> option byte) f k fl om wend wpos wbase pos len pb,
  (forall x, f <= x < f + AMF_BLOCK -> mbyte tfibsegs m' x = mbyte tfibsegs m x) ->
  Z.of_nat (length pb) <= AMF_BUFSIZ ->
  amf_k tfibsegs link_amf m f k -> amf_dyn tfibsegs link_amf m f fl om wend wpos wbase pos len ->
  amf_pend tfibsegs m f pb ->
  amf_k tfibsegs link_amf m' f k /\ amf_dyn tfibsegs link_amf m' f fl om wend wpos wbase pos len /\
  amf_pend tfibsegs m' f pb.
Proof.
intros m m' f k fl om wend wpos wbase pos len pb Hfr Hl (Hat & Hwin) Hdyn Hpend.
assert (HV : forall off n v, 0 <= off -> off + Z.of_nat n <= AMF_BLOCK ->
  val_mem tfibsegs m (f + off) n v -> val_mem tfibsegs m' (f + off) n v).
{ intros off n v H0 H1 Hv. eapply amf_val_mem_frame; [|exact Hv]. intros x Hx. apply Hfr. lia. }
split; [split|split].
- apply (amemfile_at_frame tfibsegs link_amf m m' f); [|exact Hat].
  intros x Hx. apply Hfr. unfold AMF_ZEROED, AMF_BLOCK in *. lia.
- unfold amf_win in *. unfold AMF_BLOCK in HV.
  destruct Hwin as [(H0 & H1 & H2 & H3) | (H0 & H1 & H2 & H3)]; [left | right];
    (split; [exact H0|]); (split; [|split]); (apply HV; [lia | cbn; lia | assumption]).
- unfold amf_dyn in *. unfold AMF_BLOCK, AMF_COOKIE in *.
  destruct Hdyn as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & V1 & V2 & V3 & V4 & V5 & V6 & V7).
  repeat (split; [assumption|]).
  split; [apply HV; [lia | cbn; lia | exact V1]|]. split; [apply HV; [lia | cbn; lia | exact V2]|].
  split; [apply HV; [lia | cbn; lia | exact V3]|]. split; [apply HV; [lia | cbn; lia | exact V4]|].
  split; [apply HV; [lia | cbn; lia | exact V5]|]. split; [apply HV; [lia | cbn; lia | exact V6]|].
  apply HV; [lia | cbn; lia | exact V7].
- unfold amf_pend, azbytes, amf_rd in *. intros i Hi. rewrite Hfr; [exact (Hpend i Hi)|].
  unfold AMF_BLOCK, AMF_BUF, AMF_BUFSIZ in *. lia.
Qed.

(* the FILE block lies in [1, 2^64) *)
Lemma amf_k_range : forall (m : word -> option byte) f k, amf_k tfibsegs link_amf m f k -> 0 < f /\ f + AMF_BLOCK <= 2 ^ 64.
Proof. intros m f k ((H0 & H1 & _) & _). split; assumption. Qed.

(* ---- the read-only invariant across a write to a present window above the image ---- *)
Lemma mf_arodata_keep : forall rlo rhi (W : world tfibsegs) mem mem' lo hi,
  TFIB_IMG_END <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> apresent (w_H W) mem a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  arodata_okP tfibsegs rlo rhi PcapB (aview tfibsegs (w_H W) mem) ->
  arodata_okP tfibsegs rlo rhi PcapB (aview tfibsegs (w_H W) mem').
Proof.
intros rlo rhi W mem mem' lo hi Hlo Hhi Hp KEEP HR a Hro Ho He.
assert (E1 : aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem' (a mod 2 ^ 64)) by apply AE2y.aview_mod.
assert (E2 : aview tfibsegs (w_H W) mem a = aview tfibsegs (w_H W) mem (a mod 2 ^ 64)) by apply AE2y.aview_mod.
assert (Ha' : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
pose proof (HR a Hro Ho He) as X. rewrite E2 in X. rewrite E1.
destruct (Z_lt_le_dec (a mod 2 ^ 64) lo) as [L1|L1]; [|destruct (Z_lt_le_dec (a mod 2 ^ 64) hi) as [L2|L2]].
- rewrite (KEEP _ Ha' ltac:(lia)). exact X.
- exfalso. rewrite <- (Z_to_bv64_of_mod a), (seg_rom_none_high (a mod 2 ^ 64) ltac:(lia)) in X.
  exact (aview_some_of_apresent (w_H W) mem (a mod 2 ^ 64) (Hp (a mod 2 ^ 64) ltac:(lia)) X).
- rewrite (KEEP _ Ha' ltac:(lia)). exact X.
Qed.


(* ---- the bundle at a walk's entry sp with window K ---- *)
Definition mf_pre (rlo rhi : Z) (FF : fmt_fam) (K gc gv : Z) (ly : alayout) (S : astate) (W : world tfibsegs)
  (mem : word -> option byte) (md : Model) (sp f fmt k fl om wend wpos wbase pos len : Z) (pb ws T : list Z)
  (cval : Z) : Prop :=
  ARU tfibsegs B ly S [] W mem md /\ ly_stk_lo ly + K <= sp /\ sp <= ly_stk_hi ly /\ sp mod 16 = 0 /\ ESTACK <= K /\
  (forall a, sp - K <= a < sp -> apresent (H W) mem a) /\
  In (f, AMF_BLOCK) (ablocks B ly S) /\ pairwise zdisjoint (vmf_out K sp f) /\
  amf_k tfibsegs MS (mrestrict (H W) mem) f k /\
  amf_dyn tfibsegs MS (mrestrict (H W) mem) f fl om wend wpos wbase pos len /\
  amf_pend tfibsegs (mrestrict (H W) mem) f pb /\ Z.of_nat (length pb) = k /\
  k + Z.of_nat (length T) <= AMF_BUFSIZ /\
  arodata_okP tfibsegs rlo rhi B (aview tfibsegs (H W) mem) /\
  rdword (aview tfibsegs (H W) mem) gc = Some gv /\ rdword (aview tfibsegs (H W) mem) gv = Some cval /\
  0 <= gc /\ gc + 8 <= 2 ^ 63 /\ 0 <= gv /\ gv + 8 <= 2 ^ 63 /\
  Forall (zdisjoint (gc, 8)) (vmf_out K sp f) /\ Forall (zdisjoint (gv, 8)) (vmf_out K sp f) /\
  FF (aview tfibsegs (H W) mem) (vmf_out K sp f) fmt ws T /\
  Z.of_nat (length T) < 2 ^ 31 - 1.

(* the post of both contracts (LinkVfDefs.v), at the entry registers, memory and model *)
Definition vmf_post (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (K f k : Z) (pb T : list Z) (fl om wend pos len : Z) :
  world tfibsegs -> config -> Prop :=
  fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
    c' = @cfg_at fx' tfibsegs (raZ regs) regs' mem' md' /\
    (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
    Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
    AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
    getr regs' 10 = w64 (Z.of_nat (length T)) /\
    apf_file_post tfibsegs MS (mrestrict (w_H W) mem') f k pb T fl om wend pos len /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (f <= a < f + AMF_BLOCK) ->
       ~ (spZ regs - K <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).

Lemma mf_intro : forall rlo rhi FF K gc gv ly S W regs mem md f fmt k fl om wend wpos wbase pos len pb ws T cval,
  ESTACK <= K ->
  ecall_pre tfibsegs B ly S W regs mem md ->
  ly_stk_lo ly + K <= spZ regs ->
  (forall a, spZ regs - K <= a < spZ regs -> apresent (H W) mem a) ->
  In (f, AMF_BLOCK) (ablocks B ly S) ->
  pairwise zdisjoint (vmf_out K (spZ regs) f) ->
  amf_k tfibsegs MS (mrestrict (H W) mem) f k ->
  amf_dyn tfibsegs MS (mrestrict (H W) mem) f fl om wend wpos wbase pos len ->
  amf_pend tfibsegs (mrestrict (H W) mem) f pb -> Z.of_nat (length pb) = k ->
  k + Z.of_nat (length T) <= AMF_BUFSIZ ->
  arodata_okP tfibsegs rlo rhi B (aview tfibsegs (H W) mem) ->
  rdword (aview tfibsegs (H W) mem) gc = Some gv -> rdword (aview tfibsegs (H W) mem) gv = Some cval ->
  0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
  Forall (zdisjoint (gc, 8)) (vmf_out K (spZ regs) f) ->
  Forall (zdisjoint (gv, 8)) (vmf_out K (spZ regs) f) ->
  FF (aview tfibsegs (H W) mem) (vmf_out K (spZ regs) f) fmt ws T ->
  Z.of_nat (length T) < 2 ^ 31 - 1 ->
  mf_pre rlo rhi FF K gc gv ly S W mem md (spZ regs) f fmt k fl om wend wpos wbase pos len pb ws T cval.
Proof.
intros rlo rhi FF K gc gv ly S W regs mem md f fmt k fl om wend wpos wbase pos len pb ws T cval HK
  (HAR & _ & H16 & _ & Hhi & _ & _ & _) HKlo HKp.
intros. unfold mf_pre.
split; [apply (proj2 (ARU_nil tfibsegs B ly S W mem md)); exact HAR|].
repeat (split; [assumption|]). assumption.
Qed.

(* the bundle at a memory that changed only inside the window *)
Lemma mf_keep : forall rlo rhi FF K gc gv ly S W mem md mem' md' sp f fmt k fl om wend wpos wbase pos len pb ws T cval,
  ff_stable64 FF ->
  mf_pre rlo rhi FF K gc gv ly S W mem md sp f fmt k fl om wend wpos wbase pos len pb ws T cval ->
  ARU tfibsegs B ly S [] W mem' md' ->
  (forall a, sp - K <= a < sp -> apresent (H W) mem' a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - K <= a < sp) -> aview tfibsegs (H W) mem' a = aview tfibsegs (H W) mem a) ->
  mf_pre rlo rhi FF K gc gv ly S W mem' md' sp f fmt k fl om wend wpos wbase pos len pb ws T cval.
Proof.
intros rlo rhi FF K gc gv ly S W mem md mem' md' sp f fmt k fl om wend wpos wbase pos len pb ws T cval STAB
  (HA & Hlo & Hhi & H16 & HK & Hp & Hblk & Hpw & Hk & Hdyn & Hpend & Hlpb & Hfit & Hro & Hgc & Hgv &
   G1 & G2 & G3 & G4 & Hgcd & Hgvd & HFF & HT)
  HA' Hp' KEEP.
pose proof (stk_kHighMemBeg B ly S _ (ARU_ARm tfibsegs B ly S [] W mem md HA)) as [K1 K2].
assert (HIE : TFIB_IMG_END < kHighMemBeg) by reflexivity.
assert (KHB : kHighMemBeg = 0x10007fff8000) by reflexivity. assert (KHE : kHighMemEnd = 2 ^ 47) by reflexivity.
pose proof Hpw as P1. apply pairwise_vmf in P1. unfold zdisjoint in P1. cbn [fst snd] in P1.
pose proof (amf_k_range _ f k Hk) as [F0 F1].
assert (MB : forall x, f <= x < f + AMF_BLOCK -> mbyte tfibsegs (mrestrict (H W) mem') x = mbyte tfibsegs (mrestrict (H W) mem) x).
{ intros x Hx. apply AE2y.mbyte_of_aview. apply KEEP; lia. }
assert (Hlpb' : Z.of_nat (length pb) <= AMF_BUFSIZ) by lia.
destruct (mf_file_keep _ _ f k fl om wend wpos wbase pos len pb MB Hlpb' Hk Hdyn Hpend) as (Hk' & Hdyn' & Hpend').
pose proof Hgcd as Gc. apply Forall_vmf in Gc as [Gc1 _]. pose proof Hgvd as Gv. apply Forall_vmf in Gv as [Gv1 _].
unfold zdisjoint in Gc1, Gv1. cbn [fst snd] in Gc1, Gv1.
unfold mf_pre.
split; [exact HA'|]. do 4 (split; [assumption|]). split; [exact Hp'|].
split; [exact Hblk|]. split; [exact Hpw|].
split; [exact Hk'|]. split; [exact Hdyn'|]. split; [exact Hpend'|]. split; [exact Hlpb|]. split; [exact Hfit|].
split; [exact (mf_arodata_keep rlo rhi W mem mem' (sp - K) sp ltac:(lia) ltac:(lia) Hp KEEP Hro)|].
split; [apply (rdword_keep (aview tfibsegs (H W) mem)); [|exact Hgc]; intros a Ha; apply KEEP; lia|].
split; [apply (rdword_keep (aview tfibsegs (H W) mem)); [|exact Hgv]; intros a Ha; apply KEEP; lia|].
do 6 (split; [assumption|]).
split; [|exact HT].
apply (STAB (aview tfibsegs (H W) mem)); [exact HFF|].
intros a Ha. destruct (Z_lt_le_dec a (sp - K)) as [L1|L1]; [left; apply KEEP; [exact Ha | lia]|].
destruct (Z_lt_le_dec a sp) as [L2|L2]; [|left; apply KEEP; [exact Ha | lia]].
right. split; [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia|]. unfold SHADOW_OFF in *; lia.
Qed.

(* the bundle at a callee's window inside the walk's window *)
Lemma mf_shrink : forall rlo rhi FF K K' gc gv ly S W mem md sp sp' f fmt k fl om wend wpos wbase pos len pb ws T cval,
  ff_mono FF ->
  mf_pre rlo rhi FF K gc gv ly S W mem md sp f fmt k fl om wend wpos wbase pos len pb ws T cval ->
  sp - K <= sp' - K' -> sp' <= sp -> ESTACK <= K' -> sp' mod 16 = 0 ->
  mf_pre rlo rhi FF K' gc gv ly S W mem md sp' f fmt k fl om wend wpos wbase pos len pb ws T cval.
Proof.
intros rlo rhi FF K K' gc gv ly S W mem md sp sp' f fmt k fl om wend wpos wbase pos len pb ws T cval MONO
  (HA & Hlo & Hhi & H16 & HK & Hp & Hblk & Hpw & Hk & Hdyn & Hpend & Hlpb & Hfit & Hro & Hgc & Hgv &
   G1 & G2 & G3 & G4 & Hgcd & Hgvd & HFF & HT)
  L1 L2 HK' H16'.
assert (SUB : forall x, Forall (zdisjoint x) (vmf_out K sp f) -> Forall (zdisjoint x) (vmf_out K' sp' f)).
{ intros x Hx. apply Forall_vmf in Hx as [X1 X2]. apply Forall_vmf. split; [|exact X2].
  apply (zdisjoint_sub x (sp - K, K)); [exact X1 | cbn [fst snd]; lia | cbn [fst snd]; lia]. }
unfold mf_pre.
split; [exact HA|]. split; [lia|]. split; [lia|]. split; [exact H16'|]. split; [exact HK'|].
split; [intros a Ha; apply Hp; lia|].
split; [exact Hblk|].
split; [apply pairwise_vmf in Hpw; apply pairwise_vmf; unfold zdisjoint in *; cbn [fst snd] in *; lia|].
do 12 (split; [assumption|]).
split; [exact (SUB _ Hgcd)|]. split; [exact (SUB _ Hgvd)|].
split; [|exact HT].
apply (MONO _ (vmf_out K sp f)); [exact HFF|].
intros r' Hr'. unfold vmf_out in Hr'. destruct Hr' as [<-|[<-|[]]].
- exists (sp - K, K). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (f, AMF_BLOCK). split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.

(* printf_common's premises at link's family and the read-only image PCM_CR, at its window [sp' - Kp, sp') *)
Lemma mf_pcom : forall rlo rhi K Kp gc gv ly S W mem md sp sp' f fmt k fl om wend wpos wbase pos len pb ws T cval,
  PcapSyms B ->
  mf_pre rlo rhi link_vf_FF K gc gv ly S W mem md sp f fmt k fl om wend wpos wbase pos len pb ws T cval ->
  sp - K <= sp' - Kp -> sp' <= sp ->
  consts_view tfibsegs W mem RT_pf_shU.PCM_CR /\
  Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) RT_pf_shU.PCM_CR /\
  Forall (zdisjoint (sp' - Kp, Kp)) RT_pf_shU.PCM_CR /\
  RT_pf_sh.FF_pcomK pf_link_piece (aview tfibsegs (H W) mem) [(sp' - Kp, Kp)] fmt ws T.
Proof.
intros rlo rhi K Kp gc gv ly S W mem md sp sp' f fmt k fl om wend wpos wbase pos len pb ws T cval TB
  (HA & Hlo & Hhi & H16 & HK & Hp & Hblk & Hpw & Hk & Hdyn & Hpend & Hlpb & Hfit & Hro & Hgc & Hgv &
   G1 & G2 & G3 & G4 & Hgcd & Hgvd & HFF & HT)
  L1 L2.
pose proof (stk_kHighMemBeg B ly S _ (ARU_ARm tfibsegs B ly S [] W mem md HA)) as [K1 K2].
assert (KHB : kHighMemBeg = 0x10007fff8000) by reflexivity.
pose proof (ARU_ARm tfibsegs B ly S [] W mem md HA) as HM. rewrite unpoison_nil in HM.
split.
{ apply (FMsnprintfCr.fm_cr_consts_view B W mem TB).
  - intros a Hrom Ho He. exact (Hro a (or_introl Hrom) Ho He).
  - exact (RtBzAdapt.rom_viewO_of_ARm B TB ly S W mem HM). }
split; [exact FMsnprintfCr.fm_cr_bounds|].
split.
{ pose proof FMsnprintfCr.fm_cr_in_image as HI. rewrite Forall_forall in HI |- *. intros r Hr.
  specialize (HI r Hr). unfold zdisjoint. cbn [fst snd]. lia. }
apply (FMsnprintfFmI.FF_fmP_pcomK pf_link_piece pf_link_piece (fun p Hp => Hp)).
apply (FMsnprintfFmI.FF_fmP_mono pf_link_piece _ (vmf_out K sp f)); [exact HFF|].
intros r' Hr'. destruct Hr' as [<-|[]]. exists (sp - K, K). split; [left; reflexivity | cbn [fst snd]; lia].
Qed.

(* musl vfprintf's contract applied to the bundle at its entry sp and window Kv *)
Lemma mf_apply : forall rlo rhi FF Kv gc gv pc ly S W regs mem md f fmt ap k fl om wend wpos wbase pos len pb ws T cval,
  avfprintf_mf_realizes tfibsegs B MS rlo rhi FF Kv gc gv pc ->
  mf_pre rlo rhi FF Kv gc gv ly S W mem md (spZ regs) f fmt k fl om wend wpos wbase pos len pb ws T cval ->
  YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 f -> getr regs 11 = w64 fmt -> getr regs 12 = w64 ap ->
  words_at (aview tfibsegs (H W) mem) ap ws -> spZ regs <= ap -> ap + 8 * Z.of_nat (length ws) <= 2 ^ 47 ->
  Forall (zdisjoint (ap, 8 * Z.of_nat (length ws))) (vmf_out Kv (spZ regs) f) ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) (vmf_post ly S W regs mem md Kv f k pb T fl om wend pos len).
Proof.
intros rlo rhi FF Kv gc gv pc ly S W regs mem md f fmt ap k fl om wend wpos wbase pos len pb ws T cval AVF
  (HA & Hlo & Hhi & H16 & HK & Hp & Hblk & Hpw & Hk & Hdyn & Hpend & Hlpb & Hfit & Hro & Hgc & Hgv &
   G1 & G2 & G3 & G4 & Hgcd & Hgvd & HFF & HT)
  Hra Hgp Htp R10 R11 R12 Hws Hsap H47 Ad Hfrm.
assert (HE : ecall_pre tfibsegs B ly S W regs mem md).
{ split; [exact (proj1 (ARU_nil tfibsegs B ly S W mem md) HA)|].
  split; [exact Hra|]. split; [exact H16|]. split; [lia|]. split; [exact Hhi|].
  split; [intros a Ha; apply Hp; lia|]. split; assumption. }
exact (AVF ly S W regs mem md f fmt ap k fl om wend wpos wbase pos len pb ws T cval HE Hlo Hp R10 R11 R12 Hblk Hpw
  Hk Hdyn Hpend Hlpb Hfit Hro Hgc Hgv G1 G2 G3 G4 Hgcd Hgvd Hws Hsap H47 Ad HFF HT Hfrm).
Qed.

(* the FILE post at a memory that kept the FILE block *)
Lemma mf_post_keep : forall (W : world tfibsegs) mem mem' f k pb T fl om wend pos len,
  Z.of_nat (length pb) = k -> k + Z.of_nat (length T) <= AMF_BUFSIZ ->
  (forall x, f <= x < f + AMF_BLOCK -> aview tfibsegs (H W) mem' x = aview tfibsegs (H W) mem x) ->
  apf_file_post tfibsegs MS (mrestrict (H W) mem) f k pb T fl om wend pos len ->
  apf_file_post tfibsegs MS (mrestrict (H W) mem') f k pb T fl om wend pos len.
Proof.
intros W mem mem' f k pb T fl om wend pos len Hlpb Hfit KEEP (Hk & Hdyn & Hpend).
assert (MB : forall x, f <= x < f + AMF_BLOCK -> mbyte tfibsegs (mrestrict (H W) mem') x = mbyte tfibsegs (mrestrict (H W) mem) x).
{ intros x Hx. apply AE2y.mbyte_of_aview. apply KEEP. exact Hx. }
assert (HL : Z.of_nat (length (pb ++ T)) <= AMF_BUFSIZ) by (rewrite length_app; lia).
destruct (mf_file_keep _ _ f _ _ _ _ _ _ _ _ _ MB HL Hk Hdyn Hpend) as (Hk' & Hdyn' & Hpend').
split; [exact Hk'|]. split; [exact Hdyn' | exact Hpend'].
Qed.
End k.
