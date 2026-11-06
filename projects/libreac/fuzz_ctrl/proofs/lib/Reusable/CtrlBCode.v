(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

(* Modified by Theorem Labs, 2026-10: ctrlb_lib_consts_chk and ctrlb_libS (Reusable.YCeg.TfibLib at CtrlB) port tfib_lib_consts_chk and TfibB_libS of proofs/cgif/cgif_file_fuzzer/lib/YCfi.v:19-39 (c8557374ad2e): the check covers ctrl's three lib_const_addr ranges instead of cgif's two, and errno's segment is tfibsegs' index 3, (0xa2000, 0x55c000). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify Require Import Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f Proofs.libreac.fuzz_ctrl.lib.Reusable.YF0l
  Proofs.libreac.fuzz_ctrl.lib.Reusable.YD2l.
From OSSVerify Require Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d Proofs.libreac.fuzz_ctrl.lib.Reusable.YB1v
  Proofs.libreac.fuzz_ctrl.lib.Reusable.YF0m Proofs.libreac.fuzz_ctrl.lib.Reusable.YCeg.
Local Open Scope Z_scope.
Lemma ctrlb_as_code : YG0f.as_code YD2l.CtrlB = YF0l.Tfib_code.
Proof. reflexivity. Qed.
Lemma ctrlb_pc_stack_malloc_0 : YG0f.pc_stack_malloc (YG0f.as_code YD2l.CtrlB) 0 = 0x3d6f4.
Proof. reflexivity. Qed.
Lemma ctrlb_pc_stack_malloc_1 : YG0f.pc_stack_malloc (YG0f.as_code YD2l.CtrlB) 1 = 0x3d868.
Proof. reflexivity. Qed.
Lemma ctrlb_pc_stack_malloc_2 : YG0f.pc_stack_malloc (YG0f.as_code YD2l.CtrlB) 2 = 0x3d9f8.
Proof. reflexivity. Qed.
Lemma ctrlb_pc_stack_malloc_6 : YG0f.pc_stack_malloc (YG0f.as_code YD2l.CtrlB) 6 = 0x3db94.
Proof. reflexivity. Qed.
Lemma ctrlb_lib_consts_chk :
forallb (fun r => ((fst r + snd r <=? 0x9f580) || (0x9f580 + 112 <=? fst r)) && ((fst r + snd r <=? 0x9f620) || (0x9f620 + 3256 <=? fst r))
&& ((fst r + snd r <=? 0xa0600) || (0xa0600 + 264 <=? fst r)))%bool
YF0m.Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ctrlb_libS : YCeg.TfibLib YD2l.CtrlB.
Proof.
constructor; try reflexivity.
-   cbn [YG0f.as_errno YD2l.CtrlB]. unfold YF0m.TFIB_ERRNO, YG0f.kLowMemEnd. lia.
-
intros a Ha. cbn [YG0f.as_errno YD2l.CtrlB] in Ha. unfold YF0m.TFIB_ERRNO in Ha. unfold YG0d.in_img.
assert (Hb : nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) YB1v.tfibsegs) 3 = Some (0xa2000, 0x55c000))
by (vm_compute; reflexivity).
rewrite nth_error_map in Hb. destruct (nth_error YB1v.tfibsegs 3) as [sg|] eqn:E; [|discriminate Hb]. cbn in Hb. injection Hb as H1 H2.
exists sg. split; [exact (nth_error_In _ 3 E) | rewrite H1, H2; lia].
-   intros a Ha. cbn [YG0f.as_owned_static YG0f.as_errno YD2l.CtrlB]. unfold YF0m.TFIB_ERRNO. unfold YCeg.lib_const_addr in Ha. split; [|lia].
intros HE. apply Exists_exists in HE as (r & Hr & [H1 H2]).
pose proof (proj1 (forallb_forall _ _) ctrlb_lib_consts_chk r Hr) as Hb. cbn beta in Hb.
apply andb_prop in Hb as [Hb12 Hb3]. apply andb_prop in Hb12 as [Hb1 Hb2].
apply Bool.orb_prop in Hb1 as [Hb1|Hb1]; apply Z.leb_le in Hb1;
apply Bool.orb_prop in Hb2 as [Hb2|Hb2]; apply Z.leb_le in Hb2;
apply Bool.orb_prop in Hb3 as [Hb3|Hb3]; apply Z.leb_le in Hb3; lia.
-   cbn [YG0f.as_gp YD2l.CtrlB]. unfold YF0m.TFIB_GP. lia.
Qed.
