(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0l YK0s YK0o YQ0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10 YP0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o YA0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YB1u YE3h YF9i YE3r YE3s YE33 YE3u YE3t YF9j YE31 YFa1 YE2z YE3c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YF00 YE1w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section b.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition F_STDOUT : Z := 0xa7930.
Definition STDOUT_BUFA : Z := 0x5fe920.
Definition STDOUT_BSZ : Z := 1024.
Definition FMT_d : Z := 0x14881.
Definition stdout_fields0 : list (Z * N * Z) :=
[(0, 4%N, 5); (4, 4%N, 0); (8, 8%N, 0); (16, 8%N, 0); (24, 8%N, 0x97e88); (32, 8%N, 0); (40, 8%N, 0); (48, 8%N, 0); (56, 8%N, 0); (64, 8%N, 0);
(72, 8%N, 0x98c78); (80, 8%N, 0x97fcc); (88, 8%N, STDOUT_BUFA); (96, 8%N, STDOUT_BSZ); (104, 8%N, 0); (112, 8%N, 0); (120, 8%N, 1);
(128, 8%N, 0); (136, 4%N, 0); (140, 4%N, 0xffffffff); (144, 8%N, 10);
(152, 8%N, 0); (160, 8%N, 0); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0); (192, 8%N, 0); (200, 8%N, 0); (208, 8%N, 0);
(216, 8%N, 0); (224, 8%N, 0)].
Definition stdout_fields1 : list (Z * N * Z) :=
[(0, 4%N, 5); (4, 4%N, 0); (8, 8%N, 0); (16, 8%N, 0); (24, 8%N, 0x97e88); (32, 8%N, STDOUT_BUFA + STDOUT_BSZ); (48, 8%N, 0);
(56, 8%N, STDOUT_BUFA); (64, 8%N, 0); (72, 8%N, 0x97fd4); (80, 8%N, 0x97fcc); (88, 8%N, STDOUT_BUFA); (96, 8%N, STDOUT_BSZ);
(104, 8%N, 0); (112, 8%N, 0); (120, 8%N, 1); (128, 8%N, 0); (136, 4%N, 0xffffffff); (140, 4%N, 0xffffffff); (144, 4%N, 0xffffffff);
(152, 8%N, 0); (160, 8%N, 0); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0); (192, 8%N, 0); (200, 8%N, 0); (208, 8%N, 0);
(216, 8%N, 0); (224, 8%N, 0)].
Definition ofile_is (flds : list (Z * N * Z)) (m : word -> option byte) : Prop :=
Forall (fun f => match f with (o, n, v) => val_mem trbsegs m (F_STDOUT + o) (N.to_nat n) v end) flds.
Definition stdout_pristine : (word -> option byte) -> Prop := ofile_is stdout_fields0.
Definition stdout_mid (wp : Z) (m : word -> option byte) : Prop :=
ofile_is stdout_fields1 m /\ val_mem trbsegs m (F_STDOUT + 40) 8 wp.
Definition vo_file (a : Z) : Prop := F_STDOUT <= a < F_STDOUT + FILE_SZ.
Definition vo_mut (blo bhi : Z) (a : Z) : Prop := vo_file a \/ blo <= a < bhi.
Section S.
Variable B : asyms.
Hypothesis TL : TrbSyms B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis AMEMSET : aintrin_realizes trbsegs B OSet (pc_wrap_memset (as_code B)).
Theorem trb_vfprintf_stdout_first : forall ly S (W : world trbsegs) regs mem md ch ap cval T,
ecall_pre trbsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDOUT -> getr regs 11 = w64 FMT_d -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem trbsegs (mrestrict (w_H W) mem) ap 8 0 ->
stdout_pristine (mrestrict (w_H W) mem) ->
(forall a, vo_file a \/ STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
val_mem trbsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem trbsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
range_addressable (aview trbsegs (w_H W) mem) SHADOW_OFF STDOUT_BUFA STDOUT_BSZ ->
shadow_hull_vis (aview trbsegs (w_H W) mem) STDOUT_BUFA STDOUT_BSZ ->
fdchan (Z_to_bv 64 1) ch md -> AI trbsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR trbsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 2 ->
stdout_mid STDOUT_BUFA (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band (spZ regs) a -> ~ vo_mut STDOUT_BUFA (STDOUT_BUFA + 1) a ->
aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vo_mut STDOUT_BUFA (STDOUT_BUFA + 1) a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI trbsegs (w_H W) (w_A W) md' ->
srealizes trbsegs (cfg_at trbsegs (raZ regs) regs' mem' md') T) ->
srealizes trbsegs (cfg_at trbsegs A_vfprintf regs mem md) (t_emit (map (WriteEv ch) (map (Z_to_bv 8) [48; 10])) T).
Proof. first [ exact (YE1w.tfx_vfprintf_stdout_first (imgk := YF00.K_trb)) | exact ((YE1w.tfx_vfprintf_stdout_first (imgk := YF00.K_trb)) B TL LAWS AMEMCPY AMEMSET) | exact ((YE1w.tfx_vfprintf_stdout_first (imgk := YF00.K_trb)) B TL LAWS AMEMCPY) | exact ((YE1w.tfx_vfprintf_stdout_first (imgk := YF00.K_trb)) B TL LAWS AMEMSET) | exact ((YE1w.tfx_vfprintf_stdout_first (imgk := YF00.K_trb)) B TL AMEMCPY AMEMSET) | exact ((YE1w.tfx_vfprintf_stdout_first (imgk := YF00.K_trb)) B LAWS AMEMCPY AMEMSET) | exact ((YE1w.tfx_vfprintf_stdout_first (imgk := YF00.K_trb)) TL LAWS AMEMCPY AMEMSET) | exact ((YE1w.tfx_vfprintf_stdout_first (imgk := YF00.K_trb)) B TL LAWS) | exact ((YE1w.tfx_vfprintf_stdout_first (imgk := YF00.K_trb)) B TL AMEMCPY) | exact ((YE1w.tfx_vfprintf_stdout_first (imgk := YF00.K_trb)) B LAWS AMEMCPY) | exact ((YE1w.tfx_vfprintf_stdout_first (imgk := YF00.K_trb)) TL LAWS AMEMCPY) | exact ((YE1w.tfx_vfprintf_stdout_first (imgk := YF00.K_trb)) B TL AMEMSET) | exact ((YE1w.tfx_vfprintf_stdout_first (imgk := YF00.K_trb)) B LAWS AMEMSET) | exact ((YE1w.tfx_vfprintf_stdout_first (imgk := YF00.K_trb)) TL LAWS AMEMSET) | exact ((YE1w.tfx_vfprintf_stdout_first (imgk := YF00.K_trb)) B AMEMCPY AMEMSET) | exact ((YE1w.tfx_vfprintf_stdout_first (imgk := YF00.K_trb)) TL AMEMCPY AMEMSET) | exact ((YE1w.tfx_vfprintf_stdout_first (imgk := YF00.K_trb)) LAWS AMEMCPY AMEMSET) | solve [ eapply (YE1w.tfx_vfprintf_stdout_first (imgk := YF00.K_trb)); eassumption ] | solve [ intros; eapply (YE1w.tfx_vfprintf_stdout_first (imgk := YF00.K_trb)); eassumption ] ]. Qed.
Theorem trb_vfprintf_stdout_next : forall ly S (W : world trbsegs) regs mem md ap cval wp T,
ecall_pre trbsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDOUT -> getr regs 11 = w64 FMT_d -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem trbsegs (mrestrict (w_H W) mem) ap 8 0 ->
stdout_mid wp (mrestrict (w_H W) mem) -> STDOUT_BUFA <= wp -> wp + 2 <= STDOUT_BUFA + STDOUT_BSZ ->
(forall a, vo_file a \/ STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
val_mem trbsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem trbsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
range_addressable (aview trbsegs (w_H W) mem) SHADOW_OFF STDOUT_BUFA STDOUT_BSZ ->
shadow_hull_vis (aview trbsegs (w_H W) mem) STDOUT_BUFA STDOUT_BSZ ->
range_addressable (aview trbsegs (w_H W) mem) SHADOW_OFF FMT_d 4 ->
shadow_hull_vis (aview trbsegs (w_H W) mem) FMT_d 4 ->
AI trbsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR trbsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 2 ->
stdout_mid (wp + 2) (mrestrict (w_H W) mem') ->
aview trbsegs (w_H W) mem' wp = Some 48 -> aview trbsegs (w_H W) mem' (wp + 1) = Some 10 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band (spZ regs) a -> ~ vo_mut wp (wp + 2) a ->
aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vo_mut wp (wp + 2) a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI trbsegs (w_H W) (w_A W) md' ->
srealizes trbsegs (cfg_at trbsegs (raZ regs) regs' mem' md') T) ->
srealizes trbsegs (cfg_at trbsegs A_vfprintf regs mem md) T.
Proof. first [ exact (YE1w.tfx_vfprintf_stdout_next (imgk := YF00.K_trb)) | exact ((YE1w.tfx_vfprintf_stdout_next (imgk := YF00.K_trb)) B TL LAWS AMEMCPY AMEMSET) | exact ((YE1w.tfx_vfprintf_stdout_next (imgk := YF00.K_trb)) B TL LAWS AMEMCPY) | exact ((YE1w.tfx_vfprintf_stdout_next (imgk := YF00.K_trb)) B TL LAWS AMEMSET) | exact ((YE1w.tfx_vfprintf_stdout_next (imgk := YF00.K_trb)) B TL AMEMCPY AMEMSET) | exact ((YE1w.tfx_vfprintf_stdout_next (imgk := YF00.K_trb)) B LAWS AMEMCPY AMEMSET) | exact ((YE1w.tfx_vfprintf_stdout_next (imgk := YF00.K_trb)) TL LAWS AMEMCPY AMEMSET) | exact ((YE1w.tfx_vfprintf_stdout_next (imgk := YF00.K_trb)) B TL LAWS) | exact ((YE1w.tfx_vfprintf_stdout_next (imgk := YF00.K_trb)) B TL AMEMCPY) | exact ((YE1w.tfx_vfprintf_stdout_next (imgk := YF00.K_trb)) B LAWS AMEMCPY) | exact ((YE1w.tfx_vfprintf_stdout_next (imgk := YF00.K_trb)) TL LAWS AMEMCPY) | exact ((YE1w.tfx_vfprintf_stdout_next (imgk := YF00.K_trb)) B TL AMEMSET) | exact ((YE1w.tfx_vfprintf_stdout_next (imgk := YF00.K_trb)) B LAWS AMEMSET) | exact ((YE1w.tfx_vfprintf_stdout_next (imgk := YF00.K_trb)) TL LAWS AMEMSET) | exact ((YE1w.tfx_vfprintf_stdout_next (imgk := YF00.K_trb)) B AMEMCPY AMEMSET) | exact ((YE1w.tfx_vfprintf_stdout_next (imgk := YF00.K_trb)) TL AMEMCPY AMEMSET) | exact ((YE1w.tfx_vfprintf_stdout_next (imgk := YF00.K_trb)) LAWS AMEMCPY AMEMSET) | solve [ eapply (YE1w.tfx_vfprintf_stdout_next (imgk := YF00.K_trb)); eassumption ] | solve [ intros; eapply (YE1w.tfx_vfprintf_stdout_next (imgk := YF00.K_trb)); eassumption ] ]. Qed.
End S.
End b.
