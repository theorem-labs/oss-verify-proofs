(* The image-B twin of section 3 of lib/A/FSupoisonARX.v (POISON-U lane, a working branch
   d37bcb51c52): the image premises [inst_low] and [zones_free] discharged for fuzz_state's image B
   (fuzz_state.asan-ubsan, sha256 5ac5ce0954f8...).  The image-independent part of section 3 (inst_ok_window,
   inst_low_window, DZONE_shape, CZONE_shape, owned_ext_free, zones_free_shape) is lib/A/FSupoisonARX.v's own,
   imported, since it names no address of either image.  Only the five lemmas below read an image, and they are
   stated here with B's segments and B's constants under the SAME names as A's, so a later change to A's section 3
   mirrors mechanically:
   - fs_inst_ok / fs_inst_low: B's instance TFIB_INST = 0xa4dd8 (lib/B/YF0m.v:16; A: 0xa48d8);
   - fs_img_end: B's image cover from ALedger.al_img (lib/B/YF0x.v img_cover_of_ledger: TFIB_IMG_END = 0x5fd000);
   - fs_zones_free: the same six inequalities, over B's TFIB_TSD = 0x5fc7d8 (lib/B/YF0m.v:16);
   - fs_zones_free_ex: B's relocated AGis text (lib/B/YFis.v:226-227) is DZONE_shape 0x17a308 0x5caa90 (A's
     0x179e08 0x5ca590, each object + 0x500); the CZONE band [0x7fff8000, 0x80050000) is cgif's AGif0 band, kept
     exactly as A keeps it (any band ending at or below shadow_addr TFIB_IMG_END = 0x800b7a00 is covered by
     [fs_zones_free]).
   No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0q YG0s YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison.
(* the image-free premises ([inst_low], [zones_free], [ush_free]) and the image-independent shapes of section 3 *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoisonARXm FSupoisonARX.
(* fs's image B: its segments, its symbols' addresses, its image cover *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YB1v YF0m YF0x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section prem. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* fs's instance (image B): TFIB_INST = 0xa4dd8 (lib/B/YF0m.v:16). *)
Definition fs_inst_ok (inst : Z) : Prop := inst = YF0m.TFIB_INST.

Lemma fs_inst_low : inst_low fs_inst_ok.
Proof. intros inst ->. unfold YF0m.TFIB_INST, SHADOW_OFF. lia. Qed.

(* The ledger fact for fs's image B: every segment of B lies in [ly_img] (ALedger.al_img), so the image ends at
   or above TFIB_IMG_END = 0x5fd000 (YF0x.img_cover_of_ledger). *)
Lemma fs_img_end : forall B ly S W mem md, AR YB1v.tfibsegs B ly S W mem md ->
YF0x.TFIB_IMG_END <= fst (ly_img ly) + snd (ly_img ly).
Proof. intros B ly S W mem md HAR. exact (proj2 (YF0x.img_cover_of_ledger ly S md (proj1 (proj2 HAR)))). Qed.

(* zones_free for B, for every DZONE / CZONE of the two shapes whose literal bounds satisfy six inequalities
   (shadow_addr TFIB_IMG_END = 0x800b7a00). *)
Lemma fs_zones_free : forall B dlo dhi ilo ihi slo shi,
0 <= dlo -> dhi <= SHADOW_OFF -> 0 <= ilo -> ihi <= SHADOW_OFF -> 0 <= slo -> shi <= shadow_addr YF0x.TFIB_IMG_END ->
zones_free YB1v.tfibsegs B (DZONE_shape dlo dhi) (CZONE_shape ilo ihi slo shi YF0m.TFIB_TSD).
Proof.
intros B dlo dhi ilo ihi slo shi Hd0 Hd1 Hi0 Hi1 Hs0 Hs1.
apply (zones_free_shape YB1v.tfibsegs B YF0x.TFIB_IMG_END dlo dhi ilo ihi slo shi YF0m.TFIB_TSD (fs_img_end B)
  Hd0 Hd1 Hi0 Hi1); [unfold YF0m.TFIB_TSD; lia | unfold YF0m.TFIB_TSD, SHADOW_OFF; lia | exact Hs0 | exact Hs1].
Qed.

(* The concrete check: B's DZONE (lib/B/YFis.v:226-227) and AGif0.v:54's CZONE read over B's image range and B's
   TSD, with cgif's shadow band [0x7fff8000, 0x80050000), as lib/A/FSupoisonARX.v's fs_zones_free_ex. *)
Lemma fs_zones_free_ex : forall B,
zones_free YB1v.tfibsegs B (DZONE_shape 0x17a308 0x5caa90)
  (CZONE_shape YF0x.TFIB_IMG_LO YF0x.TFIB_IMG_END 0x7fff8000 0x80050000 YF0m.TFIB_TSD).
Proof.
intros B. apply fs_zones_free; unfold YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END, SHADOW_OFF; try lia.
unfold shadow_addr, SHADOW_OFF. assert (E : 6279168 / 8 = 784896) by reflexivity. rewrite E. lia.
Qed.

End prem.
