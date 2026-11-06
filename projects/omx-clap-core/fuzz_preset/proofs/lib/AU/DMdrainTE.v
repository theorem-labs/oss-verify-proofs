(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMdrainTE.v (commit ce1a656b52b7, file sha256 399901e3c2e6) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainTE.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 ea5405446b5a) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainTE.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the ERRNO and MEMNORM keeps of the drain, and the presence of the
   quarantine's header at a cut - the first two are what MnDrain's contract (MnEnq.acall_raw_em_x, MnEnq.v:41-44)
   asks beyond the frame; the third DMiface.dmem_q no longer asks (its presence clause is stated for
   0 <= a < 2^64 and excludes the header there, DMiface.v:121-125), so DMdrainTF takes no premise for it.  All
   three follow from what Drain's entry walk may write (YFgj.WIN): errno is an image word outside that window;
   memnorm only cares that no NEW address becomes mapped, and the walk stores into bytes that were already mapped;
   and the header's own values at the cut show its bytes are still there.
   rule 24: no function proved (kind: frame consequences of segments already walked; the lane's reuse search is
   the internal file LOOKUP-B1-drain.txt, `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain`
   2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YFeq YFew YFeu YFey YFgj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMwalkIF DMdrainG1 DMdrainG4.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoG MemnormT.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variable B : asyms.
Variables (W : world tfibsegs) (ly : alayout) (X : astate).
Variables (regs0 : bvmap 5 word) (mem0 mem' : word -> option byte).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Local Notation G := (qc_list (st_qglobal X)).
Hypothesis TB : TfibSyms B.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis HSP : ly_stk_lo ly + DSTACK <= sp0 /\ sp0 <= ly_stk_hi ly.
Hypothesis HM : forall x : word, ~ YFgj.WIN ly regs0 (st_qglobal X) (bv_unsigned x) -> mem' x = mem0 x.
(* every address the walk may write was already mapped at the entry *)
Hypothesis HMAP : forall a, YFgj.WIN ly regs0 (st_qglobal X) a -> exists b, mem0 (Z_to_bv 64 a) = Some b.
(* the global list's last batch, when there is one, is a batch object of the state *)
Hypothesis Hglast : forall lastb initr, rev G = lastb :: initr ->
  kHighMemBeg <= YFgj.GLv ly (st_qglobal X).

(* a decidable test for the walk's window *)
Definition winb (a : Z) : bool :=
((sp0 - 80 <=? a) && (a <? sp0)) ||
((A_QUAR + 152 <=? a) && (a <? A_QUAR + 156)) ||
((A_QUAR + 160 <=? a) && (a <? A_QUAR + 192)) ||
((ly_T ly + t_qc <=? a) && (a <? ly_T ly + t_qc + 32)) ||
(match G with [] => false | _ :: _ => (YFgj.GLv ly (st_qglobal X) <=? a) && (a <? YFgj.GLv ly (st_qglobal X) + 8) end).
Lemma win_winb : forall a, YFgj.WIN ly regs0 (st_qglobal X) a -> winb a = true.
Proof.
intros a HW. unfold winb. unfold YFgj.WIN, YFgj.WINF, YFgj.WINA in HW. fold sp0 in HW.
assert (T1 : forall x y z : Z, x <= z < y -> ((x <=? z) && (z <? y))%bool = true)
  by (intros x y z [H1 H2]; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; assumption).
destruct HW as [HW|[[HW|[HW|HW]]|[Hne HW]]].
- assert (HA : ((sp0 - 80 <=? a) && (a <? sp0))%bool = true) by (apply T1; lia).
  repeat rewrite Bool.orb_true_iff; tauto.
- assert (HA : ((A_QUAR + 152 <=? a) && (a <? A_QUAR + 156))%bool = true) by (apply T1; lia).
  repeat rewrite Bool.orb_true_iff; tauto.
- assert (HA : ((A_QUAR + 160 <=? a) && (a <? A_QUAR + 192))%bool = true) by (apply T1; lia).
  repeat rewrite Bool.orb_true_iff; tauto.
- assert (HA : ((ly_T ly + t_qc <=? a) && (a <? ly_T ly + t_qc + 32))%bool = true) by (apply T1; lia).
  repeat rewrite Bool.orb_true_iff; tauto.
- assert (HA : (match G with [] => false | _ :: _ =>
    (YFgj.GLv ly (st_qglobal X) <=? a) && (a <? YFgj.GLv ly (st_qglobal X) + 8) end)%bool = true).
  { destruct G as [|b t]; [exfalso; apply Hne; reflexivity | apply T1; lia]. }
  repeat rewrite Bool.orb_true_iff; tauto.
Qed.

Lemma win_of_winb : forall a, winb a = true -> YFgj.WIN ly regs0 (st_qglobal X) a.
Proof.
intros a Hb. unfold winb in Hb. unfold YFgj.WIN, YFgj.WINF, YFgj.WINA. fold sp0.
repeat (apply Bool.orb_prop in Hb as [Hb|Hb]);
repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end;
repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end.
- left. lia.
- right; left; left. lia.
- right; left; right; left. lia.
- right; left; right; right. lia.
- destruct G as [|b t]; [discriminate|].
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end;
  repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end.
  right; right. split; [discriminate | lia].
Qed.

(* errno is an image word, outside everything the walk writes. *)
Theorem errno_keep : ErrnoG.errno_kept B mem0 mem'.
Proof.
intros i Hi. apply HM.
pose proof (DMdrainG1.LYB2 ly LY) as (_ & _ & _ & _ & _ & _ & _ & _ & K9). pose proof HSP as [S1 S2].
pose proof (ts_errno _ TB) as EE. pose proof (ts_inst _ TB) as EI.
unfold w64. rewrite unsigned_lit_small by (rewrite EE; unfold TFIB_ERRNO; lia).
unfold YFgj.WIN, YFgj.WINF, YFgj.WINA. fold sp0.
intros [HW | [[HW | [HW | HW]] | [Hne HW]]].
- unfold DSTACK, kHighMemBeg in *. rewrite EE in HW. unfold TFIB_ERRNO in HW. lia.
- rewrite EE in HW. unfold A_QUAR, A_ALLOCATOR, o_quar, TFIB_ERRNO in HW. lia.
- rewrite EE in HW. unfold A_QUAR, A_ALLOCATOR, o_quar, TFIB_ERRNO in HW. lia.
- pose proof (DMdrainG1.TOBJ ly LY IMG (T_app ly LY) (T_img ly LY)) as (_ & TZ & _).
  apply (zone3_apart_img _ _ (as_errno B + i) TZ);
  [ rewrite EE; unfold TFIB_ERRNO, TFIB_IMG_LO, TFIB_IMG_END; lia
  | rewrite EE in HW; unfold TFIB_ERRNO, t_qc, kThreadObjSize in *; lia ].
- destruct (rev G) as [|lastb initr] eqn:ER.
  + apply Hne. rewrite <- (rev_involutive G), ER. reflexivity.
  + pose proof (Hglast lastb initr eq_refl) as HG. rewrite EE in HW. unfold TFIB_ERRNO, kHighMemBeg in *. lia.
Qed.

(* memnorm only says that every mapped byte is at a normal address; the walk maps nothing new. *)
Theorem memnorm_keep_of_frame : MemnormT.memnorm_keep tfibsegs mem0 mem'.
Proof.
intros [HN1 HN2]. split.
- intros a b Hb.
  destruct (winb (bv_unsigned a)) eqn:EW.
  + destruct (HMAP (bv_unsigned a) ltac:(apply win_of_winb; exact EW)) as [b0 Hb0].
    rewrite Z_to_bv_bv_unsigned in Hb0. exact (HN1 a b0 Hb0).
  + rewrite (HM a ltac:(intros HW; rewrite (win_winb _ HW) in EW; discriminate)) in Hb. exact (HN1 a b Hb).
- intros a b Hb.
  destruct (winb (bv_unsigned a)) eqn:EW.
  + destruct (HMAP (bv_unsigned a) ltac:(apply win_of_winb; exact EW)) as [b0 Hb0].
    rewrite Z_to_bv_bv_unsigned in Hb0. exact (HN2 a b0 Hb0).
  + rewrite (HM a ltac:(intros HW; rewrite (win_winb _ HW) in EW; discriminate)) in Hb. exact (HN2 a b Hb).
Qed.
End g.
End f.
