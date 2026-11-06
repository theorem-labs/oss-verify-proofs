(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_TopA_iodefs () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3appC47Corelib5Lists7ListDef3mapK47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23;TopA_iodefs5io_rwC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23;TopA_iodefs5io_roC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow3accC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1C69OSSVerify5KrLib2K53B236ImageA5asegsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23;TopA_iodefs6io_accC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x227c68, [C8 (Z_to_bv 64 0x21e308)]); (0x227c80, [C8 (Z_to_bv 64 0x2101e0)]) (* [comment removed for export] *)              (* [comment removed for export] *)
  ; (0x242370, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0x21f580, [C8 (Z_to_bv 64 0xfae10); C8 (Z_to_bv 64 0xa001c)])              (* [comment removed for export] *)
  ; (0x225c18, [C8 (Z_to_bv 64 0x22a798)])                                        (* [comment removed for export] *)
  ; (0x225cf0, [C8 (Z_to_bv 64 0x20736c); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0x2269a0, [C8 (Z_to_bv 64 0x225c18); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0x2269c8, [C8 (Z_to_bv 64 0x22aa90); C8 (Z_to_bv 64 0x2413d0)])              (* [comment removed for export] *)
  ; (0x226ba0, [C8 (Z_to_bv 64 0x21f590); C8 (Z_to_bv 64 0x21f580)])              (* [comment removed for export] *)
  ; (0x227c20, [C8 (Z_to_bv 64 0x227c20)])                                        (* [comment removed for export] *)
  ; (0x227cc0, [C8 (Z_to_bv 64 0x216b90); C8 (Z_to_bv 64 0x210840); C8 (Z_to_bv 64 0x216bb0)])  (* [comment removed for export] *)
  ; (0x2422d0, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x2d663c, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x2d6960, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x11697, 10)     (* [comment removed for export] *)
  ; (0x1848b, 4)      (* [comment removed for export] *)
  ; (0x1a2c0, 128)    (* [comment removed for export] *)
  ; (0x21cd0, 33)     (* [comment removed for export] *)
  ; (0x29ec6, 21)     (* [comment removed for export] *)
  ; (0x29edb, 23)     (* [comment removed for export] *)
  ; (0x2df40, 128)    (* [comment removed for export] *)
  ; (0x302b3, 7)      (* [comment removed for export] *)
  ; (0x30a78, 16)     (* [comment removed for export] *)
  ; (0x767100, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0x227c68, 0x227c70); (0x227c80, 0x227c88); (0x242370, 0x242378);
    (0x21f580, 0x21f590); (0x225c18, 0x225c20); (0x225cf0, 0x225d00); (0x2269a0, 0x2269b0); (0x2269c8, 0x2269d8); (0x226ba0, 0x226bb0);
    (0x227c20, 0x227c28); (0x227cc0, 0x227cd8); (0x2422d0, 0x2422d4); (0x2d663c, 0x2d663d); (0x2d6960, 0x2d6961) ].

Lemma io_rngs_of : io_rngs = map (fun p => (fst p, fst p + Z.of_nat (cells_size (snd p)))) (io_rw ++ io_ro).
Proof.
ltac2:(KReplay.run1 (kr_t_TopA_iodefs ()) [] "h01pp;2p;1p;3p;4p-1R0p10000p4p710p8P0g000QR1p4p710p8P0P1p4p7210p8g000nj20Tg001Nj11TP1j33Tg001nj32Tg002Kj1:Tg003Gj19Tg003gj28Tg004Dj44Tg004dj35Tg005Aj46Tg005]j27Tg0067R1/01R0#1g006U#1R2,01R3P0P1P1f0R09312R4A2120#:#9,84C4X03g007Mg008J553C6'7o"). Qed.

Section Get.
Variable m : mem.
Hypothesis H : io_consts m.
Lemma io_rw_at : forall a cs, In (a, cs) io_rw -> rw_cells asegs m a cs.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA_iodefs ()) ["Get"] "h01ph12H0h23Hinh31Xh42_Hh53_H0h61ah72csh81ih91rh:1xp;1p;2p;4p;3p;6g001Nj1<Tg000nj27Tg004Dj43Tg009Gj32Tg000Qj36Tg001nj34Tg009^j40Tg0000j31Tg00:Wj4;Tg00;Pj4:Tg00<ER0j25Tg00<`j38Tg00=Bj69Tg0067R1g006U#<R21712R3P1P2f1R4f0R5C3g007MR632p,1Hg00=]R7p,1mR8A6125R9A4125R:C0X03R;=136R<P7P8P9P:C;X03g008J513R:1711R9P7P8A6115A4115C:X99g00>U31R9'5R='5P0P<P=P7P8f4f3C0P5P0P:P9P7P8f8f7C0P5A2356P;P4O1[^:3R8\<P<\8A83;6f5P1P2f;f:C3f9E9X59X4:P4P5O2n2001000000120000000X1=X3<P4P5O2n2001000000121000000b8W2W7W6o"). Qed.
Lemma io_ro_at : forall a cs, In (a, cs) io_ro -> ro_cells asegs m a cs.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA_iodefs ()) ["Get"] "h01ph12H0h23Hinh31Xh42_Hh53_H0h61ah72csh81ih91rh:1xp;1p;2p;4p;3p;6g001Nj1<Tg000nj24Tg004Dj43Tg009Gj36Tg000Qj37Tg001nj35Tg009^j4;Tg0000j30Tg00:Wj41Tg00;Pj49Tg00<ER0j22Tg00<`j38Tg00=Bj6:Tg0067R1g006U#<R21412R3P1P2f1R4f0R5C3g008JR636p,1Hg00=]R7p,1mR8A7125R9A5125R:C;X03g007M503R;P7P8P9P:C1X03R:=036R91411R<P7P8A7115A5115C9X9<g00>U30R<'2R='2P0P;P=P7P8f4f3C1P5P0P9P<P7P8f8f7C1P5A6356P:P4O1[^:3R8\9P9\8A83:6P4P1P2f;f:C3f9E:X5<X39P4P5O2n2001000000120000000X1=X4;P4P5O2n2001000000121000000b8W2W7W6o"). Qed.
Lemma io_acc_at : forall a n, In (a, n) io_acc -> acc asegs m a n.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA_iodefs ()) ["Get"] "h01ph12H0h23Hinh31Xh42_Hh53_H0h61ah71ih81nh91rh:1xp;2p;4p;3p;1p;6g000nj27Tg004Dj43Tg009Gj32Tg001Nj18Tg000Qj36Tg001nj34Tg009^j4<Tg0000j31Tg00:Wj4;Tg00;Pj40Tg00<ER0j25Tg00<`j39Tg00=Bj6:Tg0067R11711R2P1P1f1R3f0R4C3g00>UR532p,1Hg006U#8R6,71R7g00=]R8p,1mR9A6164R:A4164R6C<X07g007M31R;P8P9P:P6C;X07g008J517R7P8P9A6114A4114C0X92R6=125R:'5R<'5P0P;P<P8P9f4f3C0P4P0P7P:P8P9f8f7C0P4A2245P6P3O1[^:2R9\:P:\9A9265P4P1P1f;f:C3f9E:X3:X57P3P4O2n2001000000120000000X1<X4;P3P4O2n2001000000121000000b7W2X81W6o"). Qed.
End Get.

Ltac io_in := cbn [io_rw io_ro io_acc In]; repeat (first [ left; reflexivity | right ]).
