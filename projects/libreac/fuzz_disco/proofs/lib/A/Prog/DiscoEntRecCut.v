From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_frame.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition REC_J : Z := 0xc60.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Definition rec_c1 (cx : dcx) (h i n now op : Z) : world SEGS -> config -> Prop :=
  d_at B MT XM_LIB RLO RHI tfib_K cx REC_J (EV_HEAD i) (ACC_HEAD MT i) (fun regs ly3 S3 W3 mem3 md3 =>
    0 <= i < MAX_OPS /\ 0 <= n /\ 0 <= now < 2 ^ 64 /\ 0 <= op < 256 /\ op mod 4 <> 3 /\
    exists lo hi : Z,
      0 <= lo < 256 /\ 0 <= hi < 65536 /\ hi mod 256 = 0 /\ lo + hi = rec_want (rest_of (c_pl cx) n) /\
      d_rL B cx regs /\
      getr regs 11 = w64 lo /\ getr regs 12 = w64 hi /\
      getr regs 16 = w64 (d_cur cx (rec_rem n)) /\ getr regs 23 = w64 (rec_rem n) /\
      getr regs 27 = w64 op /\ getr regs 19 = w64 (op mod 4) /\
      getr regs 14 = w64 (d_obj cx OT) /\ getr regs 22 = w64 (d_obj cx OS) /\
      getr regs 26 = w64 (d_obj cx OOUR) /\
      val_mem SEGS (rd W3 mem3) (d_A cx + 392) 8 (if op <? 128 then op else op - 256) /\
      d_sp0 cx i now W3 mem3 /\
      d_body B cx h n [] dsh_loop ly3 S3 W3 mem3).

Definition rec_p1_stmt : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W : world SEGS) (c : config),
  rec_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W c -> SRr SEGS W c (rec_c1 cx h i n now op).
Definition rec_p2_stmt : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W : world SEGS) (c : config),
  rec_c1 cx h i n now op W c ->
  SRr SEGS W c (fun W' c' => exists nb fr len,
    nb = rec_rem n /\ len = rec_len (rest_of (c_pl cx) n) n /\
    ((op mod 4 <> 2 /\ cls_in B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W' c') \/
     (op mod 4 = 2 /\ hobs_in B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W' c'))).
End h.
End f.
End d.
