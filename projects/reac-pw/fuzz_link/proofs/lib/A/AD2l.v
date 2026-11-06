(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD2l.v, with its module paths changed, names TfibSyms -> PcapSyms, TfibB -> PcapB, TfibB_syms -> PcapB_syms, TfibB_ok -> PcapB_ok and its addresses moved to libreac/fuzz_pcap's ASan build. The field ts_universe_drv cites lib/A/ACejTfib.v Tfib_universe_drv (a Theorem Labs lane's trace lane), and PcapB_universe states lib/A/PcapClose.v's row 12 (H_TRACES_B) for PcapB. *)
(* Modified by Theorem Labs, 2026-10: the four const-cell memberships of PcapB_ok are index-free (ruling a Theorem Labs lane): each cites lib/A/AF0x.v:202 cell_lookup_In at the cell's ADDRESS instead of the donor's literal position in Tfib_const_abs (donor AD2l.v:63-66 nth_error_In 49 / 50 / 144 / 155), so the table's order is no longer part of the proof. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG01 YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0l AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import ACej ACejTfib ACejUniv.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Definition PcapB : asyms := {|
as_code := Tfib_code;
as_inst := TFIB_INST;
as_gp := TFIB_GP;
as_tp := TFIB_TP;
as_tsd := TFIB_TSD;
as_shadow_cell := 0xaa438;
as_uar_cell := 0xaa440;
as_got_shadow := 0xa19d0;
as_got_uar := 0xa1a28;
as_errno := TFIB_ERRNO;
as_depot := TFIB_DEPOT;
as_store := TFIB_STORE;
as_ialloc_lo := TFIB_IAL_LO;
as_ialloc_hi := TFIB_IAL_HI;
as_ialloc_w := TFIB_IAL_W;
as_ialloc_flag := TFIB_IAL_FLAG;
as_oom_byte := TFIB_OOM;
as_dhash := tfib_dhash;
as_const := Tfib_const;
as_junk := fun _ => [(ANum 0xa7088, 40)];
as_owned_static := Tfib_owned_static;
as_zero_shadow := Tfib_zero_shadow;
as_universe := Tfib_univ |}.
(* lib/A/PcapClose.v row 12 (H_TRACES_B) at B := PcapB: the trace universe is the trace lane's (donor AD2l.v:37). *)
Lemma PcapB_universe : as_universe PcapB = ACejUniv.Tfib_univ.
Proof. reflexivity. Qed.
Lemma zr_sub_of_b : forall r l,
existsb (fun r' => (fst r' <=? fst r) && (fst r + snd r <=? fst r' + snd r'))%bool l = true -> Exists (zr_sub r) l.
Proof.
intros r l H. apply existsb_exists in H as (r' & Hr' & Hb). apply Exists_exists. exists r'. split; [exact Hr'|].
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold zr_sub. split; [exact H1 | exact H2].
Qed.
Lemma PcapB_ok : asyms_ok PcapB.
Proof.
constructor.
-   cbn [as_owned_static PcapB]. unfold Tfib_owned_static, kImgEnd, pcap_img_end, YImgTop.IMG_TOP, YImgTop.IMG_TOP.
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
-
apply Forall_forall. intros r Hr. apply zr_sub_of_b.
assert (R : forallb (fun r => existsb (fun r' => (fst r' <=? fst r) && (fst r + snd r <=? fst r' + snd r'))%bool Tfib_owned_static)
(asyms_areas PcapB) = true) by (vm_compute; reflexivity).
exact (proj1 (forallb_forall _ _) R r Hr).
-   intros ly. cbn [as_const as_shadow_cell as_uar_cell as_got_shadow as_got_uar PcapB]. unfold Tfib_const.
assert (A : forall c, In c Tfib_const_abs -> In c (Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow)).
{ intros c Hc. apply in_app_iff. right. apply in_app_iff. left. exact Hc. }
split; [|split; [|split]]; apply A.
+ apply (cell_lookup_In _ (ANum 0xaa438)). vm_compute. reflexivity.
+ apply (cell_lookup_In _ (ANum 0xaa440)). vm_compute. reflexivity.
+ apply (cell_lookup_In _ (ANum 0xa19d0)). vm_compute. reflexivity.
+ apply (cell_lookup_In _ (ANum 0xa1a28)). vm_compute. reflexivity.
-   cbn [as_zero_shadow PcapB]. unfold Tfib_zero_shadow, kLowMemEnd, PcapImgEnd.pcap_img_end, YImgTop.IMG_LO, YImgTop.IMG_TOP.
repeat (apply Forall_cons; [cbn [fst snd]; repeat split; try lia; reflexivity|]). apply Forall_nil.
-   cbn [as_ialloc_lo as_ialloc_w as_ialloc_hi PcapB]. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W. lia.
-   cbn -[Z.le Z.lt Z.add Z.sub Z.mul Z.pow]. unfold TFIB_INST, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_OOM, TFIB_TP, kLowMemEnd. lia.
Qed.
Theorem PcapB_syms : PcapSyms PcapB.
Proof.
constructor; try reflexivity.
- exact PcapB_ok.
-   intros ly r Hr. destruct Hr as [<- | []]. exists 0xa7088. cbn [fst snd]. refine (conj eq_refl _). unfold YImgTop.IMG_TOP. lia.
-   intros ly. left. reflexivity.
-   exact Tfib_universe_ok.
-   intros t Ht. exact (ACejTfib.Tfib_universe_drv t Ht).
-   intros h Hh. cbn [as_dhash PcapB]. destruct h as [|[|h]]; [vm_compute; reflexivity | vm_compute; reflexivity | lia].
Qed.
Definition TfibB_pair : asyms_ok PcapB /\ PcapSyms PcapB := conj PcapB_ok PcapB_syms.
