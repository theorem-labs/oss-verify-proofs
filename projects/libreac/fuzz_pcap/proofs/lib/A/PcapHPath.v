From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2m.v (origin/ossv/recipes
   c8557374ad2e, tfib_trailer_shadow) for libreac/fuzz_pcap, with its module paths changed, TfibSyms -> PcapSyms,
   the object moved to fuzz_pcap's "<fuzz-input>" literal, and the statement general in segs (its proof never uses
   segs). The image-global shadow fact of HPATH (lib/A/Prog/PcapSourceOpen.v, PcapEntryInst.v): under
   AR, the 13 bytes of the listing's object 3 (PcapFuzzFopen.FO_PATH, the path passed to fopen) are range_addressable
   and their shadow hull is visible. Proved from PcapSyms B (A/AF0m.v): the const-shadow cells (ts_const,
   Tfib_const_shadow) and the zero-shadow ranges (ts_zsh, Tfib_zero_shadow, through YG0s.AR_zshadow_law_ok); no
   function walk.
   Measured on the pin fuzz_pcap.asan (sha256 b7a91d9b1fb0017df0462bf382b3211837851bf801e792673b1cee0797cdca2a),
   symbols from its unstripped twin, pyelftools:
   - the object: symbol `.str` 0x20d00 (STT_OBJECT, local, st_size 32), in .rodata [0x102e0, 0x2266c) of the
     read-only PT_LOAD at 0x10000; bytes "<fuzz-input>" and NUL = 13 bytes. PcapAddr.pcap_obj 3 = 0x20d00.
   - its ASan descriptor: asan_globals descriptor 0 (0x9e100): beg 0x20d00, size 0xd, size_with_redzone 0x20, so
     the right redzone is [0x20d0d, 0x20d20) (19 bytes; AF0m Tfib_owned_static row 25).
   - its shadow (shadow_addr a = 0x7fff8000 + a / 8): 0x7fffc1a0 (granule 0x20d00) = 0x00, Tfib_zero_shadow's range
     (0x10000, 0x20d08 - 0x10000); 0x7fffc1a1 (granule 0x20d08, bytes 0x20d08..0x20d0c) = 0x05, AF0m const-shadow
     cell; 0x7fffc1a2 / 0x7fffc1a3 (granules 0x20d10 / 0x20d18, the redzone) = 0xf9, AF0m const-shadow cells.
   - the hull of the 13 bytes is the 8 shadow bytes [0x7fffc1a0, 0x7fffc1a8); its last four, 0x7fffc1a4..0x7fffc1a7
     (granules 0x20d20..0x20d38, not an ASan global), are 0x00, Tfib_zero_shadow's range (0x20d20, 0x20d40 - 0x20d20).
   The same eight shadow bytes in every one of the 50 at-main states AF0m was generated from (the HSDUMP of the side-A
   pass-2 log, sha256 fd2fb3eca6b5f04d...): KZero [0x7fffa000, 0x7fffc1a1), KWord 0x7fffc1a1 1 = 5,
   KFill 0x7fffc1a2 2 = 249, KZero [0x7fffc1a4, 0x7fffc1a8). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AF0m AF0x AE2y.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* 0x20d00 = PcapAddr.pcap_obj 3, the listing's object 3 (PcapFuzzFopen.FO_PATH); 13 = its ASan descriptor's size. *)
Lemma pcap_path_addressable : forall B, PcapSyms B -> forall segs ly S (W : world segs) mem md,
AR segs B ly S W mem md ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (symaddr (Symbols.Asan.Sec.s_rodata + 68128)%Z) 13 /\
shadow_hull_vis (aview segs (w_H W) mem) (symaddr (Symbols.Asan.Sec.s_rodata + 68128)%Z) 13.
Proof.
intros B TB segs ly S W mem md HAR. set (rd := aview segs (w_H W) mem).
pose proof (proj1 HAR) as HM.
assert (C1 : forall a v, const_chk ly a 1%N v = true -> rd a = Some (le_byte v 1 0)).
{ intros a v Hc. pose proof (const_chk_sound _ _ _ _ Hc) as E.
assert (X : cell_holds B ly rd (ACell (ANum a) (N.to_nat 1) (AV (ANum v)))).
{ apply (proj1 (Forall_forall (cell_holds B ly rd) (as_const B ly)) (am_const B ly S _ HM)).
rewrite (ts_const B TB ly). exact (cell_lookup_In _ _ _ E). }
unfold cell_holds in X. cbn [c_at c_val c_w aeval N.to_nat] in X.
specialize (X 0%nat ltac:(lia)). rewrite Z.add_0_r in X. exact X. }
assert (ZS : forall lo len i, In (lo, len) Tfib_zero_shadow -> 0 <= i < len / 8 -> rd (SHADOW_OFF + lo / 8 + i) = Some 0).
{ intros lo len i Hin Hi.
exact (AR_zshadow_law_ok segs B ly S W mem md (lo, len) HAR ltac:(right; rewrite (ts_zsh B TB); exact Hin) i Hi). }
(* The granule 0x20d00 (shadow 0x7fffc1a0) and the four shadow bytes 0x7fffc1a4..0x7fffc1a7 are zero shadow. *)
assert (Z0 : rd (symaddr ((Symbols.Asan.Sec.s_rodata + 68128) / 8 + 0x7fff8000)%Z) = Some 0).
{ pose proof (ZS 0x10000 ((symaddr (Symbols.Asan.Sec.s_rodata + 68136)%Z) - 0x10000) 0x21a0 ltac:(unfold Tfib_zero_shadow; left; reflexivity)
    ltac:(change (((symaddr (Symbols.Asan.Sec.s_rodata + 68136)%Z) - 0x10000) / 8) with 0x21a1; lia)) as H.
change (SHADOW_OFF + 0x10000 / 8 + 0x21a0) with (symaddr ((Symbols.Asan.Sec.s_rodata + 68128) / 8 + 0x7fff8000)%Z) in H. exact H. }
assert (Z4 : forall s, (symaddr ((Symbols.Asan.Sec.s_rodata + 68160) / 8 + 0x7fff8000)%Z) <= s < (symaddr ((Symbols.Asan.Sec.s_rodata + 68192) / 8 + 0x7fff8000)%Z) -> rd s = Some 0).
{ intros s Hs.
pose proof (ZS (symaddr (Symbols.Asan.Sec.s_rodata + 68160)%Z) ((symaddr (Symbols.Asan.Sec.s_rodata + 68192)%Z) - (symaddr (Symbols.Asan.Sec.s_rodata + 68160)%Z)) (s - (symaddr ((Symbols.Asan.Sec.s_rodata + 68160) / 8 + 0x7fff8000)%Z)) ltac:(unfold Tfib_zero_shadow; right; left; reflexivity)
    ltac:(change (((symaddr (Symbols.Asan.Sec.s_rodata + 68192)%Z) - (symaddr (Symbols.Asan.Sec.s_rodata + 68160)%Z)) / 8) with 4; lia)) as H.
assert (E : SHADOW_OFF + (symaddr (Symbols.Asan.Sec.s_rodata + 68160)%Z) / 8 = (symaddr ((Symbols.Asan.Sec.s_rodata + 68160) / 8 + 0x7fff8000)%Z)) by reflexivity.
rewrite E in H. replace ((symaddr ((Symbols.Asan.Sec.s_rodata + 68160) / 8 + 0x7fff8000)%Z) + (s - (symaddr ((Symbols.Asan.Sec.s_rodata + 68160) / 8 + 0x7fff8000)%Z))) with s in H by lia. exact H. }
split.
- intros x Hx. unfold shadow_of_addr.
pose proof (Z.div_mod x 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M.
destruct (Z_lt_le_dec x (symaddr (Symbols.Asan.Sec.s_rodata + 68136)%Z)) as [L|G].
+ assert (Q : x / 8 = 0x41a0) by lia. rewrite Q.
exists 0. split; [| left; reflexivity].
change (SHADOW_OFF + 0x41a0) with 0x7fffc1a0. exact Z0.
+ assert (Q : x / 8 = 0x41a1) by lia. rewrite Q.
exists (le_byte 0x5 1 0). split.
* change (SHADOW_OFF + 0x41a1) with 0x7fffc1a1. apply C1. vm_compute. reflexivity.
* right. change (le_byte 0x5 1 0) with 5. lia.
- intros s Hs.
assert (E1 : shadow_addr (symaddr (Symbols.Asan.Sec.s_rodata + 68128)%Z) / 8 * 8 = (symaddr ((Symbols.Asan.Sec.s_rodata + 68128) / 8 + 0x7fff8000)%Z)) by reflexivity.
assert (E2 : shadow_addr ((symaddr (Symbols.Asan.Sec.s_rodata + 68128)%Z) + 13 - 1) / 8 * 8 + 8 = (symaddr ((Symbols.Asan.Sec.s_rodata + 68192) / 8 + 0x7fff8000)%Z)) by reflexivity.
rewrite E1, E2 in Hs.
destruct (Z_lt_le_dec s (symaddr ((Symbols.Asan.Sec.s_rodata + 68160) / 8 + 0x7fff8000)%Z)) as [L|G].
+ assert (C : s = (symaddr ((Symbols.Asan.Sec.s_rodata + 68128) / 8 + 0x7fff8000)%Z) \/ s = (symaddr ((Symbols.Asan.Sec.s_rodata + 68136) / 8 + 0x7fff8000)%Z) \/ s = (symaddr ((Symbols.Asan.Sec.s_rodata + 68144) / 8 + 0x7fff8000)%Z) \/ s = (symaddr ((Symbols.Asan.Sec.s_rodata + 68152) / 8 + 0x7fff8000)%Z)) by lia.
destruct C as [-> | [-> | [-> | ->]]].
* rewrite Z0. discriminate.
* rewrite (C1 (symaddr ((Symbols.Asan.Sec.s_rodata + 68136) / 8 + 0x7fff8000)%Z) 0x5); [discriminate | vm_compute; reflexivity].
* rewrite (C1 (symaddr ((Symbols.Asan.Sec.s_rodata + 68144) / 8 + 0x7fff8000)%Z) 0xf9); [discriminate | vm_compute; reflexivity].
* rewrite (C1 (symaddr ((Symbols.Asan.Sec.s_rodata + 68152) / 8 + 0x7fff8000)%Z) 0xf9); [discriminate | vm_compute; reflexivity].
+ rewrite (Z4 s ltac:(lia)). discriminate.
Qed.
End b.
