(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31 (the world relation R): aj_snprintf_at_xromR is the call-site rule over a
   journal at a reflexive and transitive world relation R (binders first; the call keeps the world, so no law of R is
   read); aj_snprintf_at_xrom keeps its statement and is the instance at wle. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcallSnp.v, with its module paths and module names changed; 366 of its 437 lines of code are new or changed and 191 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/FMsnprintfShared.v, with its module paths and module names changed; 30 of its 65 lines of code are new or changed and 402 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YC8g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnShared.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnFF SnprintfDef.
Import ListNotations.
Local Open Scope Z_scope.

(* The guarded twin of SnprintfDef.asnprintf_realizes (a Theorem Labs lane ruling (B), 2026-10-29 18:38Z): the same contract
   with ONE more premise at the call, that every unowned read-only byte of the image (and of the relro range) reads
   as the image (the walk invariant arodata_okP). A caller that carries arodata_okP (every disco snprintf call site
   does) can use the snprintf tops through this form; AR alone does not fix unowned read-only bytes. *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variables relro_lo relro_hi : Z.

Definition sh_asnprintf_realizesR (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S W regs mem md d n f (xs ws T : list Z) cval,
ecall_pre segs B ly S W regs mem md ->
YC8g.arodata_okP segs relro_lo relro_hi B (aview segs (w_H W) mem) ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f ->
SnShared.consts_view segs W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (fun r => Forall (zdisjoint r) (SnShared.snp_out K (spZ regs) d (SnShared.sn_len (n - 1) T))) cr ->
rdword (aview segs (w_H W) mem) gc = Some gv -> rdword (aview segs (w_H W) mem) gv = Some cval ->
0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
Forall (zdisjoint (gc, 8)) (SnShared.snp_out K (spZ regs) d (SnShared.sn_len (n - 1) T)) ->
Forall (zdisjoint (gv, 8)) (SnShared.snp_out K (spZ regs) d (SnShared.sn_len (n - 1) T)) ->
SnShared.va_words regs (aview segs (w_H W) mem) (spZ regs) xs ws ->
spZ regs + 8 * Z.of_nat (length xs) <= 2 ^ 47 ->
Forall (zdisjoint (spZ regs, 8 * Z.of_nat (length xs))) (SnShared.snp_out K (spZ regs) d (SnShared.sn_len (n - 1) T)) ->
FF (aview segs (w_H W) mem) (SnShared.snp_out K (spZ regs) d (SnShared.sn_len (n - 1) T)) f ws T ->
1 <= n < 2 ^ 31 -> Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < d -> d + SnShared.sn_len (n - 1) T <= 2 ^ 63 ->
pairwise zdisjoint (SnShared.snp_out K (spZ regs) d (SnShared.sn_len (n - 1) T)) ->
dest_ok segs B ly S W regs mem d (SnShared.sn_len (n - 1) T) -> amem_range d (SnShared.sn_len (n - 1) T + 8) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d (SnShared.sn_len (n - 1) T) ->
shadow_hull_vis (aview segs (w_H W) mem) d (SnShared.sn_len (n - 1) T) ->
(* dest_off_globals: the caller discharges it by measurement *) zdisjoint (d, SnShared.sn_len (n - 1) T) (img_lo, img_hi - img_lo) ->
(* frm0_entry: rounding mode 0 at entry (GXA VfprintfCall.v:37) *) Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < SnShared.sn_len (n - 1) T -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (SnShared.sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + SnShared.sn_len (n - 1) T) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* the unguarded contract implies the guarded one, for every FF, K and cr *)
Lemma sh_asnprintf_realizesR_of : forall FF K gc gv img_lo img_hi cr pc,
  SnShared.sh_asnprintf_realizes (fx := fx) segs B FF K gc gv img_lo img_hi cr pc ->
  sh_asnprintf_realizesR FF K gc gv img_lo img_hi cr pc.
Proof. intros FF K gc gv img_lo img_hi cr pc H ly S W regs mem md d n f xs ws T cval Hpre _. exact (H ly S W regs mem md d n f xs ws T cval Hpre). Qed.

(* the form de_asnprintf names: SnprintfDef.asnprintf_realizes with the arodata_okP guard *)
Definition asnprintf_realizesR (gc gv img_lo img_hi flo fhi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
sh_asnprintf_realizesR (SnFF.FF_disco flo fhi) SnprintfDef.SNPRINTF_STK gc gv img_lo img_hi cr pc.

Lemma asnprintf_realizesR_of : forall gc gv img_lo img_hi flo fhi cr pc,
  SnprintfDef.asnprintf_realizes (fx := fx) segs B gc gv img_lo img_hi flo fhi cr pc ->
  asnprintf_realizesR gc gv img_lo img_hi flo fhi cr pc.
Proof. intros. apply sh_asnprintf_realizesR_of. exact H. Qed.
End s.
