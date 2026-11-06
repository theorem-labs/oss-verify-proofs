(* Case 1 of fuzz_boxreg's LLVMFuzzerTestOneInput on the ASan build, 0x803a8 .. 0x80ab4 (fuzz_boxreg.c:287-362),
   as one step of the turn: from the cut GI_T 1 i to the cut GI_K i of lib/A/Prog/BoxLxDefs.v.

   The walk is cut into four pieces at three places (lib/A/Prog/BoxLxC1Defs.v: PC1_nch 0x806cc, PC1_dec 0x807a8,
   PC1_call 0x807e8), and the piece after the calls again at the return slot of each call
   (lib/A/Prog/BoxLxC1AddDefs.v: CA_PR1 .. CA_PR5):

     GI_T 1 i -> C1_nch   read_mac inlined, then the nch byte           c1_seg_mac   BoxLxC1Mac.v
     C1_nch   -> C1_dec   bcmp (mac, ZERO) and the scan of prev's rows  c1_seg_scan  BoxLxC1Defs.v
     C1_dec   -> C1_call  the legal width, and lowest_free when needed  c1_seg_want  BoxLxC1Defs.v
     C1_call  -> GI_K     find, add, and the checks after them          c1_seg_add   below, from
                                                                       ca_s1 .. ca_s6 (BoxLxC1AddS1.v,
                                                                       BoxLxC1AddS2.v, BoxLxC1Add.v (s3),
                                                                       BoxLxC1AddS4.v, BoxLxC1AddS5.v,
                                                                       BoxLxC1AddS6.v) *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC1g YC1h YC81 YC85 BoxFrame BoxCJ BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregInit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require ReacBoxregFind ReacBoxregAdd LowestFree.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxDefs BoxLxSeat BoxLxC1Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
BoxLxC1AddDefs BoxLxC1Mac BoxLxC1AddS1 BoxLxC1AddS2 BoxLxC1AddS4 BoxLxC1AddS5 BoxLxC1AddS6 BoxLxC1Add.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require
Boxreg LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_case1
reac_boxreg_add_c reac_boxreg_find_c lowest_free_c reac_boxreg_add_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HISV : img_shadow_vis SEGS B.
Hypothesis HGLOB : globs_marked SEGS B BX_G.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA BS___asan_memcpy).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA BS___interceptor_trampoline_bcmp).
Hypothesis TFIND : ReacBoxregFind.treac_boxreg_find_spec B.
Hypothesis TADD : ReacBoxregAdd.treac_boxreg_add_spec B.
Hypothesis TLOWFREE : LowestFree.tlowest_free_spec B.
Hypothesis HZERO : SnprintfDef.asn_rom_bytes SEGS B (VAL (A_OBJ 6))
  (map (fun b : byte => bv_unsigned b) Boxreg.zero6).
Hypothesis HRMB : SnprintfDef.asn_rom_bytes SEGS B (VAL (A_OBJ 4)) [0; 64; 171; 0; 0].
Hypothesis HMRG : Forall (fun g => IMG_LO + 64 <= fst g /\ fst g + snd g + 64 <= IMG_HI) BX_G.
Variable POST : bcx -> world SEGS -> config -> Prop.

(* 0x807e8 .. 0x80ab4: reac_boxreg_find, reac_boxreg_add, and the checks the case makes on what they return,
   as the six segments of BoxLxC1AddDefs.v's cuts. ca_s3 splits on the index add returns: a new row goes on
   through the bcmp of 0x80868 and the two calls that repeat find and add, a refused one joins at once. *)
Lemma c1_seg_add : forall i, gb_from B MT POST (GI_K B MT i) -> gb_from B MT POST (C1_call B MT i).
Proof.
  intros i HK.
  apply ca_s1; try assumption.
  apply ca_s2; try assumption.
  apply ca_s3; try assumption.
  apply ca_s4; try assumption.
  apply ca_s5; try assumption.
  apply ca_s6; try assumption.
Qed.

(* The case, from its four pieces. *)
Theorem gb_case1 : forall i, gb_from B MT POST (GI_K B MT i) -> gb_from B MT POST (GI_T B MT 1 i).
Proof.
  intros i HK.
  apply c1_seg_mac; try assumption.
  apply c1_seg_scan; try assumption.
  apply c1_seg_want; try assumption.
  apply c1_seg_add; try assumption.
Qed.

End c.
End b.
End a.
