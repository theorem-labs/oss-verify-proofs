(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGtopcgifC.v (cold/c-frame-alloc-dgraw-frozen ced28ed2383, file sha256 847ee765efb4) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/omx-clap-core/fuzz_state/lib/A/AGtopcgifC.v (donor image sha256 64b53ff86172), with its module paths changed, names TfibSyms -> SegBSyms and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/AGtopcgifC.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* The cgif_file primary-size Allocate contract with its MISS arms discharged: AllocGcgif.aalloc_prim_realizes_cgif,
   from AGtopcgif.aalloc_prim_realizes_cgif_g, whose two premises ARM_MISSGc / ARM_MISSKc are the miss arms.

   The arms, each proved over the c5 interface (AGif0n.AIface / AIfaceM) and instantiated here at cgif's instance:
   - k miss, can_fill in {0, 1}: AGin0.alloc_missk_cf (h-rw-dec-3), whose cf = 1 case is AGin.alloc_missk (h-decbox-a5);
   - g miss, can_fill in {0, 1}: AGim0.alloc_missg_cf (h-rw-dec-3), whose cf = 1 case is AGim.alloc_missg (h-decbox-a2).
   So [aalloc_prim_realizes_cgif_closed] has no arm premise at all, and [aalloc_prim_realizes_cgif_cf1] is its
   can_fill = 1 case stated alone.
   cgif's AIfaceM instance is AGif1m.iface_cgif_m (h-decbox-a9's frozen-dm AGif0n), which takes tfib_depot_spec B
   ([HD1]) for the interface field if_depot_miss.  That field is what the arms read after a depot miss; it replaced
   if_U_refill, which is false for fuzz_state, whose universe reads st_nev.
   The discharges follow h-rw-dec-3's AGtop.aalloc_prim_realizes_if at cold/h-rw-dec-3-agtop2 0b82402d3e3, which was
   written on the c5 tree before the AGtop split (c-asan-realloc-c5 2bd8ae006ef); here they sit above the split
   AGtopcgif.v, and the AIfaceM instance is no longer a premise. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YB1q YF0l YF0m YFl0 YFl1.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YGAlloc.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import AllocGcgif AGtop AGtopcgif.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require AGif0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require AGif1 AGif1k AGif1m AGim AGim0 AGin0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import AGif2cgif AGif0cgif.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Section d.
Variable B : asyms.
Hypothesis TS : SegBSyms B.
Hypothesis HD1 : tfib_depot_spec B.

(* can_fill = 1, no premise: the g arm is AGim.alloc_missg, the k arm AGin0.alloc_missk_cf. *)
Theorem aalloc_prim_realizes_cgif_cf1 : aalloc_prim_realizes_cgif B 1.
Proof.
pose proof (AGif1.iface_cgif B TS HD1) as IF. pose proof (AGif1m.iface_cgif_m B TS HD1) as IFM.
apply (aalloc_prim_realizes_cgif_g B TS HD1 1 (or_intror eq_refl)).
- intros inst so bp ly S W regs mem md n tr _ HPRE Hn El.
  eapply AGim.alloc_missg; eassumption.
- intros inst so bp ly S W regs mem md n tr Hcf HPRE Hn El.
  eapply AGin0.alloc_missk_cf; eassumption.
Qed.

(* can_fill in {0, 1}, NO ARM PREMISE AT ALL: both arms carry their own cf, by AGim0.alloc_missg_cf (whose cf = 1
   case is AGim.alloc_missg) and AGin0.alloc_missk_cf (whose cf = 1 case is AGin.alloc_missk). *)
Variable cf : Z.
Hypothesis HCF : cf = 0 \/ cf = 1.
Theorem aalloc_prim_realizes_cgif_closed : aalloc_prim_realizes_cgif B cf.
Proof.
pose proof (AGif1.iface_cgif B TS HD1) as IF. pose proof (AGif1m.iface_cgif_m B TS HD1) as IFM.
apply (aalloc_prim_realizes_cgif_g B TS HD1 cf HCF).
- intros inst so bp ly S W regs mem md n tr Hcf HPRE Hn El.
  eapply AGim0.alloc_missg_cf; eassumption.
- intros inst so bp ly S W regs mem md n tr Hcf HPRE Hn El.
  eapply AGin0.alloc_missk_cf; eassumption.
Qed.
End d.
End a.
