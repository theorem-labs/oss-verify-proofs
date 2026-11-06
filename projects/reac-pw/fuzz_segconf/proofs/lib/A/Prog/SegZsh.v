(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Prog/CmdZsh.v (origin/ossv/recipes 501c0d516c69) for reac-pw/fuzz_segconf's image A (fuzz_segconf.asan): module paths; CmdBSyms -> SegBSyms, cmd_ -> seg_. *)
(* The shadow of the image's registered objects, for the program walks.

   A walk's inline check reads the shadow byte at (a >> 3) + 0x7fff8000 of every address it loads or stores. For a
   byte of one of the image's registered objects (g_rec, record.spill, rec_codes, g_shapes, the string literals),
   that byte is 0, because the allocator invariant AR keeps every range of `as_zero_shadow B` at zero shadow
   (AR_laws' al_zshadow, Reusable/YG0d.v:443-446) and the allocator record names the ranges (CmdBSyms' ts_zsh,
   lib/A/AF0m.v:313). This is the donor's own derivation (cgif lib/A/AD1k.v:205-212, rodata_zero_shadow), stated
   once for any range of the record, so that a contract states only the address range and a walk takes
   `HB : CmdBSyms B` beside `LAWS : AR_laws SEGS B`. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section z. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis HB : SegBSyms B.
(* every range the record names is at zero shadow *)
Lemma seg_zshadow_rec : forall ly S (W : world segs) mem md r,
AR segs B ly S W mem md -> In r Tfib_zero_shadow ->
zero_shadow (aview segs (w_H W) mem) SHADOW_OFF (fst r) (snd r).
Proof.
intros ly S W mem md r HAR Hin.
exact (al_zshadow _ _ LAWS ly S W mem md r HAR
ltac:(unfold zero_shadow_ranges; right; rewrite (ts_zsh B HB); exact Hin)).
Qed.
(* a granule-aligned piece of such a range is at zero shadow *)
Lemma seg_zshadow_sub : forall ly S (W : world segs) mem md r a n,
AR segs B ly S W mem md -> In r Tfib_zero_shadow ->
fst r mod 8 = 0 -> a mod 8 = 0 -> fst r <= a -> a + n <= fst r + snd r ->
zero_shadow (aview segs (w_H W) mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md r a n HAR Hin Hr Ha Hlo Hhi i Hi.
pose proof (seg_zshadow_rec ly S W mem md r HAR Hin) as Z.
assert (Hd : a - fst r = 8 * ((a - fst r) / 8)).
{ apply Z_div_exact_2; [lia|]. rewrite Zminus_mod, Hr, Ha. reflexivity. }
assert (Ha8 : a / 8 = fst r / 8 + (a - fst r) / 8).
{ replace a with (fst r + (a - fst r) / 8 * 8) at 1 by lia. rewrite Z.div_add by lia. reflexivity. }
unfold shadow_of_addr in *. rewrite Ha8.
replace (SHADOW_OFF + (fst r / 8 + (a - fst r) / 8) + i) with (SHADOW_OFF + fst r / 8 + ((a - fst r) / 8 + i)) by lia.
apply Z. Z.div_mod_to_equations. lia.
Qed.
(* any byte range inside such a range is addressable: what an inline check of a load or store needs *)
Lemma seg_addressable_in : forall ly S (W : world segs) mem md r a n,
AR segs B ly S W mem md -> In r Tfib_zero_shadow ->
fst r mod 8 = 0 -> snd r mod 8 = 0 -> fst r <= a -> a + n <= fst r + snd r ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md r a n HAR Hin Hr Hs Hlo Hhi.
apply (range_addressable_sub _ _ (fst r) (snd r)); [|lia|lia].
apply zero_shadow_range; [exact Hr|exact Hs|].
exact (seg_zshadow_rec ly S W mem md r HAR Hin).
Qed.
End z.
