(* reac-pw/fuzz_link, image A: link's snprintf contract (lib/A/Rt/LinkSnpDef.v, at the trampoline LA_W_SNPRINTF
   0x43088) as ONE STEP OF THE CALLER'S JOURNAL, the form the own-function walks take it in (link-a/form/FORM.md
   (internal record, sha256 13aeff774164) section 3a; link_amem.v `apre` / `apost`, over `ajournal_gx G XO OUT`).

   `link_snprintf_journal` takes the contract as a hypothesis, so it holds for whatever proves it (today the port
   built on the ported FM layer; LinkSnpInst.v's `link_asnprintf_contract` is its instance at link's own
   segments and asyms). It is the snprintf twin of lib/A/Prog/link_ajkit.v's lifts of the checked copy / fill and
   of the string wrappers.

   What the caller gives at the call, beside its journal:
   - the journal's window holds the call's window: sp0 - STK <= sp - LINK_SNP_STK and sp <= sp0 (link_amem.v apre's
     stack conjuncts), with sp 16-aligned, ret_ok ra, gp and tp (the same four register facts every A contract
     takes). From these lib/A/Prog/link_ajkit.v `aj_gx_ecall_pre` builds the runtime-call pre-state the contract
     asks for (YG0d.v ecall_pre, the window present), so no caller states ecall_pre itself.
   - arodata_okP (apre carries it). No world premise: the world record carries w_H8 (Reusable/YA0n.v:25).
   - the contract's own premise bundle `asnprintf_link_fpre` (the registers, the canary cells, the argument words,
     the format family, the bounds, the destination's bytes and shadow, its placement and its separation from the
     runtime cells) -- LinkSnpWit.v shows it is satisfiable at each of the three call sites.
   - `ajw` of every written byte: exactly what link_amem.v's apre asks of a write set, so a caller that lists
     [d, d + sn_len (n - 1) T) in its `Wr` has it already. With the bundle's writability it also gives
     `~ aowned` of those bytes (link_ajkit.v aj_gx_dest_byte), which is the contract's last destination premise, so
     the caller states no ownership fact of its own.
   The step: the journal at the return is the caller's journal at the same event index k (snprintf raises no event),
   and beside it the contract's own post, with the written bytes at d.

   The journal lift is `aj_gx_call_atFo` (link_ajkit.v), the variant whose presence premise is only
   `alloc_ceiling <= a < 2 ^ 64` plus each written byte visible after the call: a destination in .bss is an image
   byte, and link's image models .bss with ROM zero bytes, so the contract's post pins the written NUL's value but
   not the store's domain there (LinkSnpDef.v, the post's presence clause).

   Proves no function (kind: segment lemma of the snprintf call's journal step). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import PfFacts SnShared.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkSnpDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Variables rlo rhi : Z.

Theorem link_snprintf_journal :
  sh_asnprintf_link_realizes segs B rlo rhi FF_link LINK_SNP_STK LA_W_SNPRINTF ->
  forall G XO OUT (W : world segs) regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw
         d n f (xs ws T : list Z) cval,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  sp0 - STK <= spZ regsT - LINK_SNP_STK -> spZ regsT <= sp0 -> spZ regsT mod 16 = 0 ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  arodata_okP segs rlo rhi B (aview segs (w_H W) memT) ->
  asnprintf_link_fpre segs FF_link LINK_SNP_STK W memT regsT d n f xs ws T cval ->
  (forall a, d <= a < d + sn_len (n - 1) T -> ajw B G XO OUT STK sp0 FP ly S lyc Sc own a) ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 LA_W_SNPRINTF) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists (fx' : YK11.FPState) regs2 mem2 md2,
       c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       (forall kk : bv 5, bv_unsigned kk <> 10 -> Sem.reg_get (@fp_regs fx') kk = Sem.reg_get (@fp_regs fx) kk) /\
       Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
       AR segs B lyc Sc W mem2 md2 /\ aregs_preserved regsT regs2 /\ same_but_materialized mdc md2 /\
       getr regs2 10 = w64 (Z.of_nat (length T)) /\
       (forall i, 0 <= i < sn_len (n - 1) T ->
          aview segs (w_H W) mem2 (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
          ~ (spZ regsT - LINK_SNP_STK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, 0 <= a < 2 ^ 64 -> apresent (w_H W) memT a ->
          ~ (d <= a < d + sn_len (n - 1) T /\ YImgTop.IMG_LO <= a < YImgTop.IMG_TOP) ->
          apresent (w_H W) mem2 a)).
Proof.
intros CONTRACT G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw
  d n f xs ws T cval HG HJX Hlo Hhi H16 Hra Hraw Hgp Htp HRO HPRE HAJW HFRM.
assert (HK : ESTACK <= LINK_SNP_STK) by (unfold LINK_SNP_STK, ESTACK; lia).
pose proof HPRE as (R10 & R11 & R12 & HGC & HGV & HVA & HXS & HDX & HFF & Hn & HT & Hd0 & Hdw & HW & HAMR &
  HRAD & HSHV & HPL & HRT).
(* the runtime-call pre-state, from the journal *)
destruct (aj_gx_ecall_pre SK segs B LINK_SNP_STK G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT
  mdc k regsT HJX HK H16 Hlo Hhi ltac:(rewrite Hra; exact Hraw) Hgp Htp) as (HPREC & HSTKLO & HWIN).
(* the destination bytes are writable and not the runtime's *)
assert (HDEST : forall a, d <= a < d + sn_len (n - 1) T ->
  writable_at segs (mrestrict (w_H W) memT) a /\ ~ aowned B lyc Sc a).
{ intros a Ha.
  apply (aj_gx_dest_byte SK segs B LAWS G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k a HG HJX).
  destruct (HAJW a Ha) as [Hw | [HGa | Ho]]; [left; exact Hw | right; left | right; right; exact Ho].
  split; [exact HGa|].
  exact (proj1 (HW a Ha)). }
(* the journal step over the contract's post *)
eapply (aj_gx_call_atFo SK segs B LAWS segs_low LINK_SNP_STK (fun a => d <= a < d + sn_len (n - 1) T)
  LA_W_SNPRINTF G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw
  (fun fx' regs2 mem2 md2 =>
     (forall kk : bv 5, bv_unsigned kk <> 10 -> Sem.reg_get (@fp_regs fx') kk = Sem.reg_get (@fp_regs fx) kk) /\
     Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
     AR segs B lyc Sc W mem2 md2 /\ aregs_preserved regsT regs2 /\ same_but_materialized mdc md2 /\
     getr regs2 10 = w64 (Z.of_nat (length T)) /\
     (forall i, 0 <= i < sn_len (n - 1) T ->
        aview segs (w_H W) mem2 (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
        ~ (spZ regsT - LINK_SNP_STK <= a < spZ regsT) ->
        aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
     (forall a, 0 <= a < 2 ^ 64 -> apresent (w_H W) memT a ->
        ~ (d <= a < d + sn_len (n - 1) T /\ YImgTop.IMG_LO <= a < YImgTop.IMG_TOP) ->
        apresent (w_H W) mem2 a))
  HG HJX ltac:(unfold LINK_SNP_STK, ESTACK; lia) Hlo Hhi Hra).
- (* every written byte is one the journal lets a callee write *)
  intros a Ha. exact (HAJW a Ha).
- (* what the contract's post gives the journal *)
  intros fx' regs2 mem2 md2 (Hfp & Hfrm & HAR2 & Hpres & Hsame & Ha0 & Hby & Hkept & Hoff).
  split; [exact HAR2|]. split; [exact Hsame|].
  split; [intros a Ha Hw He; exact (Hkept a Ha He Hw)|].
  split.
  + intros a Ha. replace a with (d + (a - d)) by lia.
    rewrite (Hby (a - d) ltac:(lia)). discriminate.
  + (* the journal asks presence above alloc_ceiling only, which lies above the image *)
    intros a Ha Hp. pose proof alloc_ceiling_value as (HC1 & _).
    apply (Hoff a ltac:(lia) Hp). unfold YImgTop.IMG_TOP. lia.
- (* the contract at the call *)
  eapply SRr_mono.
  { exact (CONTRACT lyc Sc W regsT memT mdc d n f xs ws T cval HPREC HRO HSTKLO HWIN HPRE
      (fun a Ha => proj2 (HDEST a Ha)) HFRM). }
  cbv beta. intros W' c' _ (-> & fx' & regs2 & mem2 & md2 & -> & Hfp & Hfrm & HAR2 & Hpres & Hsame & Ha0 & Hby & Hkept & Hoff).
  split; [reflexivity|]. exists fx', regs2, mem2, md2. split; [reflexivity|].
  split; [exact Hfp|]. split; [exact Hfrm|]. split; [exact HAR2|]. split; [exact Hpres|].
  split; [exact Hsame|]. split; [exact Ha0|]. split; [exact Hby|].
  split; [intros a Ha Hd Hw; exact (Hkept a Ha Hd Hw) | exact Hoff].
Qed.

End j.
