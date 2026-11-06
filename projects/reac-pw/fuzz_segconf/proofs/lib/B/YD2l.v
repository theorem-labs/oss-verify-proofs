(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD2l.v, with its module paths changed, names TfibB -> CmdB, TfibSyms -> CmdBSyms, TfibB_syms -> CmdB_syms, TfibB_ok -> CmdB_ok, its addresses moved to plugin-hostd/fuzz_command's ASan build, the use-after-return cell at 0xb10c0, the four const-cell memberships found by search instead of by cgif's list positions (fuzz_command's cell list is generated), the program's writable statics (g_rec, record.spill, g_quitting) in the record's new as_prog_static field, and CmdB_errno_rom (the errno cell lies in the loaded image) for the program's walks; CmdB_lib (TfibLib CmdB) is cgif's A/ACed.v tfibX_lib for fuzz_command's segments and lib_const_addr. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AD2l.v (donor image sha256 c0661b96b5bd), with its module paths changed, names CmdBSyms -> SegBSyms, CmdB -> SegB and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/AD2l.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YF0l YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YCej YCeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YB13 YB1v.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Definition SegB : asyms := {|
as_code := Tfib_code;
as_inst := TFIB_INST;
as_gp := TFIB_GP;
as_tp := TFIB_TP;
as_tsd := TFIB_TSD;
as_shadow_cell := 0xac7b8;
as_uar_cell := 0xac7c0;
as_got_shadow := 0xa3210;
as_got_uar := 0xa3268;
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
as_junk := fun _ => [(ANum 0xa9408, 40)];
as_owned_static := Tfib_owned_static;
as_zero_shadow := Tfib_zero_shadow;
as_universe := Tfib_universe;
as_prog_static := TFIB_PROG_STATIC |}.
Lemma In_of_existsb : forall (t : list Z) (U : list (list Z)),
existsb (fun u => if list_eq_dec Z.eq_dec u t then true else false) U = true -> In t U.
Proof.
intros t U H. apply existsb_exists in H as (u & Hu & Hb). destruct (list_eq_dec Z.eq_dec u t) as [<-|]; [exact Hu | discriminate].
Qed.
Lemma zr_sub_of_b : forall r l,
existsb (fun r' => (fst r' <=? fst r) && (fst r + snd r <=? fst r' + snd r'))%bool l = true -> Exists (zr_sub r) l.
Proof.
intros r l H. apply existsb_exists in H as (r' & Hr' & Hb). apply Exists_exists. exists r'. split; [exact Hr'|].
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold zr_sub. split; [exact H1 | exact H2].
Qed.
Lemma SegB_ok : asyms_ok SegB.
Proof.
constructor.
-   cbn [as_owned_static SegB]. unfold Tfib_owned_static, kImgEnd.
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
-
apply Forall_forall. intros r Hr. apply zr_sub_of_b.
assert (R : forallb (fun r => existsb (fun r' => (fst r' <=? fst r) && (fst r + snd r <=? fst r' + snd r'))%bool Tfib_owned_static)
(asyms_areas SegB) = true) by (vm_compute; reflexivity).
exact (proj1 (forallb_forall _ _) R r Hr).
-   intros ly. cbn [as_const as_shadow_cell as_uar_cell as_got_shadow as_got_uar SegB]. unfold Tfib_const.
assert (A : forall c, In c Tfib_const_abs -> In c (Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow)).
{ intros c Hc. apply in_app_iff. right. apply in_app_iff. left. exact Hc. }
split; [|split; [|split]]; apply A.
+ unfold Tfib_const_abs; repeat (first [left; reflexivity | right]).
+ unfold Tfib_const_abs; repeat (first [left; reflexivity | right]).
+ unfold Tfib_const_abs; repeat (first [left; reflexivity | right]).
+ unfold Tfib_const_abs; repeat (first [left; reflexivity | right]).
-   cbn [as_zero_shadow SegB]. unfold Tfib_zero_shadow, kLowMemEnd.
repeat (apply Forall_cons; [cbn [fst snd]; repeat split; try lia; reflexivity|]). apply Forall_nil.
-   cbn [as_ialloc_lo as_ialloc_w as_ialloc_hi SegB]. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W. lia.
-   cbn -[Z.le Z.lt Z.add Z.sub Z.mul Z.pow]. unfold TFIB_INST, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_OOM, TFIB_TP, kLowMemEnd. lia.
-   vm_compute. reflexivity.
Qed.
Theorem SegB_syms : SegBSyms SegB.
Proof.
constructor; try reflexivity.
- exact SegB_ok.
-   intros ly r Hr. destruct Hr as [<- | []]. exists 0xa9408. cbn [fst snd]. refine (conj eq_refl _). lia.
-   intros ly. left. reflexivity.
-   exact Tfib_universe_ok.
-   intros t Ht. cbn [as_universe SegB].
assert (R : forallb (fun t0 => existsb (fun u => if list_eq_dec Z.eq_dec u t0 then true else false) Tfib_universe) DRV_TRACES = true)
by (vm_compute; reflexivity).
exact (In_of_existsb t Tfib_universe (proj1 (forallb_forall _ _) R t Ht)).
-   intros h Hh. cbn [as_dhash SegB]. destruct h as [|[|h]]; [vm_compute; reflexivity | vm_compute; reflexivity | lia].
Qed.
Definition TfibB_pair : asyms_ok SegB /\ SegBSyms SegB := conj SegB_ok SegB_syms.
Lemma SegB_errno_rom : forall B, SegBSyms B -> YCbq.errno_rom YB1v.tfibsegs B.
Proof.
intros B HB a Ha. rewrite (ts_errno _ HB) in Ha. unfold TFIB_ERRNO in Ha.
apply YB13.tfib_rw_rom. lia.
Qed.
(* Gate on the generated tables (copy of A/AD1g.v xowned): every constant cell lies in Tfib_owned_static, its
   shadow, or a core extent, as ARm's am_const_owned (Reusable/YG0n.v:212) requires. *)
Definition cmd_zcovered (z w : Z) : bool := existsb (fun r : Z * Z => (fst r <=? z) && (z + w <=? fst r + snd r))%bool Tfib_owned_static.
Definition cmd_zshcovered (z w : Z) : bool :=
existsb (fun r : Z * Z => (shadow_addr (fst r) <=? z) && (z + w <=? shadow_addr (fst r) + (snd r + 7) / 8))%bool Tfib_owned_static.
Definition cmd_xowned (c : acell) : bool :=
let w := Z.max 1 (Z.of_nat (c_w c)) in
match c_at c with
| ANum z => cmd_zcovered z w || cmd_zshcovered z w
| ATp o => cmd_zcovered (TFIB_TP + o) w
| ATsd o => cmd_zcovered (TFIB_TSD + o) w
| AInst o => cmd_zcovered (TFIB_INST + o) w
| ADepot o => cmd_zcovered (TFIB_DEPOT + o) w
| AStore o => cmd_zcovered (TFIB_STORE + o) w
| YG0f.AT o => (0 <=? o) && (o + w <=? kThreadObjSize)
| AC o => (0 <=? o) && (o + w <=? 256)
| AQ o => (0 <=? o) && (o + w <=? kPtrArrayResv)
| ANB o => (0 <=? o) && (o + w <=? kNodesBlockSize)
| ASB o => (0 <=? o) && (o + w <=? kStoreBlockSize)
| AD o => (0 <=? o) && (o + w <=? 4096)
| _ => false
end%bool.
Lemma SegB_const_owned : forall ly, forallb cmd_xowned (as_const SegB ly) = true.
Proof. intros ly. cbn [as_const SegB]. unfold Tfib_const. vm_compute. reflexivity. Qed.
(* Witness that the program-side record TfibLib (A/ACeg.v) holds of SegB (cgif's A/ACed.v tfibX_lib, for
   fuzz_command's lib_const_addr = the program's GOT words 0xa7068..0xa7088). *)
Lemma SegB_lib_consts_chk :
forallb (fun r => (fst r + snd r <=? 0xa31b0) || (0xa31b0 <=? fst r))%bool Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.
Theorem SegB_lib : TfibLib SegB.
Proof.
constructor; try reflexivity.
- cbn [as_errno SegB]. unfold TFIB_ERRNO, kLowMemEnd. lia.
- intros a Ha. cbn [as_errno SegB] in Ha. unfold TFIB_ERRNO in Ha. unfold YG0d.in_img.
assert (Hb : nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) YB1v.tfibsegs) 3 = Some (0xa4000, 0x55e000))
by (vm_compute; reflexivity).
rewrite nth_error_map in Hb. destruct (nth_error YB1v.tfibsegs 3) as [sg|] eqn:E; [|discriminate Hb]. cbn in Hb. injection Hb as H1 H2.
exists sg. split; [exact (nth_error_In _ 3 E) | rewrite H1, H2; lia].
- intros a Ha. cbn [as_owned_static as_errno SegB]. unfold TFIB_ERRNO. unfold lib_const_addr in Ha. split; [|lia].
intros HE. apply Exists_exists in HE as (r & Hr & [H1 H2]).
pose proof (proj1 (forallb_forall _ _) SegB_lib_consts_chk r Hr) as Hb. cbn beta in Hb.
apply Bool.orb_prop in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
- cbn [as_gp SegB]. unfold TFIB_GP. lia.
Qed.
