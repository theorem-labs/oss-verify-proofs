(* copy of proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfSharedCf.v@0ddf65fd8cc; module paths fuzz_manifest -> fuzz_preset, lib.A -> lib.Reusable *)
(* The _cf twin of the shared snprintf top (FMsnprintfShared.v sh_asnprintf_realizes, cold/port-fm-rtprintf-param
   4de9999bfe7, lines 156-188), for fuzz_preset's cf allocator instance (h-mani-a8). AR form only (preset has no
   ecall_preU_cf). The changes follow c-libc-stdio's astrcmp_realizes_cf (origin/cold/h-mani-a8-preset-alloc
   9d68c8a66d34, lib/Reusable/YGcfStr.v:123-, header :96), and nothing else changes:
   - ecall_pre -> ecall_pre_cf (YG0dcf.v:80-), with the ghost list Hp;
   - AR -> ARcf (YG0ncf.v:299-301) in the post, Hp threaded unchanged (snprintf allocates nothing);
   - the destination's premise is the top's amem_range d (sn_len (n - 1) T + 8) (cold/port-fm-rtprintf-param, the
     destination slack); preset's amem_range8 (YGcfStr.v:117) gives it (amem8_of_amem_range8 below);
   - the per-call rom_view before SRr, as astrcmp_realizes_cf has it.
   FF, K, gc / gv, img_lo / img_hi, cr, dest_off_globals, frm0_entry, the 2^47 slot bound, the Sem.reg_get FP clause
   and the sn_bytes post are FMsnprintfShared's text. Image-neutral: a Section over segs B. Statement only. New file. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcfStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FMupoison FMsnprintfPf FMsnprintfShared.
Import ListNotations.
Local Open Scope Z_scope.

Section s.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable segs : list Segment.
Variable B : asyms.
Definition sh_asnprintf_realizes_cf (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S Hp W regs mem md d n f (xs ws T : list Z) cval,
ecall_pre_cf segs B ly S Hp W regs mem md ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f ->
consts_view segs W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (fun r => Forall (zdisjoint r) (snp_out K (spZ regs) d (sn_len (n - 1) T))) cr ->
rdword (aview segs (w_H W) mem) gc = Some gv -> rdword (aview segs (w_H W) mem) gv = Some cval ->
0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
Forall (zdisjoint (gc, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
Forall (zdisjoint (gv, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
va_words regs (aview segs (w_H W) mem) (spZ regs) xs ws ->
spZ regs + 8 * Z.of_nat (length xs) <= 2 ^ 47 ->
Forall (zdisjoint (spZ regs, 8 * Z.of_nat (length xs))) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
FF (aview segs (w_H W) mem) (snp_out K (spZ regs) d (sn_len (n - 1) T)) f ws T ->
1 <= n < 2 ^ 31 -> Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < d -> d + sn_len (n - 1) T <= 2 ^ 63 ->
pairwise zdisjoint (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
dest_ok segs B ly S W regs mem d (sn_len (n - 1) T) -> amem_range d (sn_len (n - 1) T + 8) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d (sn_len (n - 1) T) ->
shadow_hull_vis (aview segs (w_H W) mem) d (sn_len (n - 1) T) ->
(* dest_off_globals: the caller discharges it by measurement *) zdisjoint (d, sn_len (n - 1) T) (img_lo, img_hi - img_lo) ->
(* frm0_entry: rounding mode 0 at entry (GXA VfprintfCall.v:37) *) Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
rom_view segs W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
ARcf segs B ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

End s.

(* preset's amem_range8 (8 bytes to spare past the bytes read) gives the top's destination premise *)
Lemma amem8_of_amem_range8 : forall p n, amem_range8 p n -> amem_range p (n + 8).
Proof. intros p n H. unfold amem_range8 in H. unfold amem_range. lia. Qed.
