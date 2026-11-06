From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Definition MID_OFF : Z := 2256.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Definition d_rM (cx : dcx) (i n now op dt : Z) (regs : bvmap 5 word) : Prop :=
  d_rL B cx regs /\
  getr regs 6 = w64 i /\ getr regs 7 = w64 n /\ getr regs 10 = w64 (dt * 1000000) /\ getr regs 11 = w64 now /\
  getr regs 14 = w64 (d_obj cx OT) /\ getr regs 16 = w64 (d_cur cx n) /\
  getr regs 17 = w64 (if op <? 128 then op else op - 256) /\
  getr regs 22 = w64 (d_obj cx OS) /\ getr regs 26 = w64 (d_obj cx OOUR).

Definition hdr_mid (cx : dcx) (h i : Z) : world SEGS -> config -> Prop :=
  fun W c => exists n now op dt,
    d_at B MT XM_LIB RLO RHI tfib_K cx MID_OFF (EV_HEAD i) (ACC_HEAD MT i) (fun regs ly3 S3 W3 mem3 md3 =>
      0 <= i < MAX_OPS /\ 0 <= n /\ 0 <= now < 2 ^ 64 /\ 0 <= op < 256 /\ 0 <= dt < 65536 /\
      d_rM cx i n now op dt regs /\ d_body B cx h n [] dsh_loop ly3 S3 W3 mem3) W c.

Definition hdr_Q (cx : dcx) (h i : Z) : world SEGS -> config -> Prop :=
  fun W' c' => exists n now op,
    (op mod 4 = 3 /\ arm3_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W' c') \/
    (op mod 4 <> 3 /\ rec_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W' c').

Definition hdr_seg1 : Prop :=
  forall (cx : dcx) (h i : Z) (W : world SEGS) (c : config),
  loop_inv B MT XM_LIB RLO RHI tfib_K cx h i W c -> SRr SEGS W c (hdr_mid cx h i).

Definition hdr_seg2 : Prop :=
  forall (cx : dcx) (h i : Z) (W : world SEGS) (c : config),
  hdr_mid cx h i W c -> SRr SEGS W c (hdr_Q cx h i).

Theorem hdr_of_parts : hdr_seg1 -> hdr_seg2 -> hdr_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros S1 S2 cx h i W c HL.
apply (SRr_bind SEGS W c (hdr_mid cx h i) (hdr_Q cx h i) (S1 cx h i W c HL)).
intros W' c' _ HM. exact (S2 cx h i W' c' HM).
Qed.
End h.
End f.
End d.
