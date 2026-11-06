(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MemnormDnull.v (a working branch 5ad50e61fc6a, file sha256 575892d86698) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53; pin f8f98a95bc52); module paths changed; its 2 image addresses moved by code-verified function pairs (2 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin B (pinned fuzz_preset.asan-ubsan f8f98a95bc52, twin 3b5e1a099b53; this file at 7bf67ee2d69f) to B' (#102 pin d663f82d7f48, twin c90d4fa54d43) by the relocation route of record, frozen alreloc a5c53bb2bed4ad03 (a Theorem Labs lane's internal file alreloc.py.frozen-a5c53bb2bed4ad03), --assume-source, --resolve resolve-B102-r6h.txt (sha256 68493e550d6f; internal record) (0 lines name this file); 2 numerals changed. *)
(* Theorem Labs, 2026-10 (task MEMNORM): the NULL arm of DGg3.v with memnorm kept.  [null_arm_c_em] /
   [dealloc_null_arm_em] are DGg3.null_arm_c_e / dealloc_null_arm_e with MemnormDleafB.dealloc_leaf_raw_eem
   (DGleafE.dealloc_leaf_raw_ee plus `memnorm mem -> memnorm mem'`) in place of DGleafE.dealloc_leaf_raw_ee.
   rule 24: no function proved (kind: arm twin, frame corollary).

   The keep comes from the arm's own raw frame: DGh1.at_RETN's MEQI (first conjunct) keeps every byte outside DGgn.WIN
   (Deallocate's stack window and the thread's unwinding byte) and DGgn.IZONE (the internal allocator's zone), and none
   of those zones holds a read-only byte or reaches TASK_SIZE ([memnorm_MEQN]): the stack window lies in the layout's
   stack (above kImgEnd, below kHighMemEnd = TASK_SIZE: lo_top, YG0f.v:321-323), the unwinding byte in the thread
   object, an owned extent (MemnormHitGB.mn_safe_owned), and IZONE in tfibsegs' read-write segments
   (MemnormSafeAB.mn_safe_rw).
   The proof of null_arm_c_em is DGg3.v:427-494 (blocks marked as copies; the section headers are DGg3.v:57-85), plus
   the memnorm conjunct from the same MEQR.  DGg3's section-local lemmas PREd, LOv, HIGH, STK64, R1, R2 and null_main
   are taken by `Let` at this file's identical section variables.  No runner is swapped and no walk is touched.
   DGg3.v is unchanged. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o YG0h.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a YB1w YE3d YFeq YFex.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DGbase DGgn DGfx DGh1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AllocG DeallocG AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFfu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoG DGleafE.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DGg3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require MemnormDleafB MemnormHitGB MemnormSafeAB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* memnorm is kept by a memory that equals [mem] outside at_RETN's raw frame zones (DGgn.MEQI's first conjunct). *)
Lemma memnorm_MEQN : forall ly (regs0 : bvmap 5 word) (mem mem' : word -> option byte),
  layout_ok ly -> img_cover ly ->
  ly_stk_lo ly + DGbase.DFSTACK <= bv_unsigned (getr regs0 2) -> bv_unsigned (getr regs0 2) <= ly_stk_hi ly ->
  (forall x : word, ~ DGgn.WIN ly regs0 (bv_unsigned x) -> ~ DGgn.IZONE (bv_unsigned x) -> mem' x = mem x) ->
  MemnormT.memnorm_keep tfibsegs mem mem'.
Proof.
intros ly regs0 mem mem' LY IMG HSP HSH MEQ.
pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
apply (MemnormT.memnorm_frame tfibsegs (fun a => DGgn.WIN ly regs0 a \/ DGgn.IZONE a) mem mem').
- intros x [Hw|Hz].
  + unfold DGgn.WIN in Hw. cbv beta zeta in Hw. destruct Hw as [Hw|Hw].
    * apply MemnormHitGB.mn_safe_high. unfold DGbase.DFSTACK, kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
    * apply (MemnormHitGB.mn_safe_owned ly (ly_T ly, kThreadObjSize) x LY IMG
        ltac:(unfold owned_extents; right; right; left; reflexivity)).
      cbn [fst snd]. unfold kThreadObjSize, t_unwinding in *. lia.
  + unfold DGgn.IZONE in Hz. apply MemnormSafeAB.mn_safe_rw.
    unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TASK_SIZE in *. lia.
- intros x NZ. apply MEQ; intros X; apply NZ; [left | right]; exact X.
Qed.

(* copy of DGg3.v:57-85 (the section headers), unchanged *)
Section b.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Variable U : list Z -> astate -> Prop.
Variable ft : sptr -> list Z -> M unit.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world tfibsegs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable dbody : astate -> M unit.
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable MP : (word -> option byte) -> Prop.
Hypothesis IF : DIface B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP.

Section c.
Variables (inst so bp : Z) (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (n : Z) (tr : list Z).
Hypothesis PRE : DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md PNull n tr.
Let regs0 : bvmap 5 word := dregs regs 0 inst bp so.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation E0 := (DGgn.E0 ly regs0 tr).
Local Notation LENv := (DGgn.LENv tr).
(* DGg3's section-local lemmas (DGg3.v:87, :102, :108, :153, :155, :156, :405) at this section's variables *)
Let PREd := DGg3.PREd B TS U ARX rpre fpre inst so bp ly S W regs mem md n tr PRE.
Let LOv := DGg3.LOv B TS U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF inst so bp ly S W regs mem md n tr PRE.
Let HIGH := DGg3.HIGH B TS U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF inst so bp ly S W regs mem md n tr PRE.
Let STK64 := DGg3.STK64 B TS U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF inst so bp ly S W regs mem md n tr PRE.
Let R1 := DGg3.R1 inst so bp regs.
Let R2 := DGg3.R2 inst so bp regs.
Let null_main := DGg3.null_main B TS U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF inst so bp ly S W regs mem md n tr PRE.

(* null_arm_c_e with memnorm kept. *)
Theorem null_arm_c_em : amreal tfibsegs (ft PNull tr S) W (cfg_at tfibsegs 0x32390 regs mem md)
(MemnormDleafB.dealloc_leaf_raw_eem B ft ARX AOX lpost inst ly S W regs mem md PNull n tr).
Proof.
(* copy of DGg3.v:427-488, unchanged *)
pose proof PREd as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & _).
pose proof PRE as PRE'. unfold DeallocG.dealloc_pre in PRE'.
do 27 (destruct PRE' as [_ PRE']). destruct PRE' as (HTU & _ & HFP).
pose proof (dn_unw _ _ _ _ _ LOv) as HUNW0. pose proof HIGH as (_ & _ & _ & _ & hT1 & _).
eapply amreal_mono; [| exact (amreal_apath_gflag tfibsegs _ _ _ _ null_main)].
intros r W' c' [[-> HR] HPATH].
destruct HR as (-> & regs' & mem' & mat & -> & RCS & MEQR & UNW & PRES').
rewrite R2 in PRES'. fold sp0 in PRES'.
assert (DM : dmem_n W ly sp0 mem mem').
{ split; [|split; [exact (proj2 MEQR) | split; [exact UNW | exact PRES']]].
  intros x N1 N2 N3. apply (proj1 MEQR x); [| exact N3].
  unfold DGgn.WIN. rewrite R2. fold sp0. intros [X|X]; [exact (N1 X) | exact (N2 X)]. }
destruct (di_post_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md n tr sp0 mem' mat HARX HRP HFP HTU
  ltac:(unfold DFSTACK, DGbaseC.DFSTACK in *; lia) Hhi Hbot Hal DM HPATH) as [HARX' HLP].
exists ly, regs', mem', (with_vm_backing (m_vm_lazy md) mat md).
split. { unfold cfg_at, raZ, w64. rewrite R1, Z_to_bv_bv_unsigned. reflexivity. }
split.
{ split; [exact HARX'|]. split; [apply layout_le_refl|]. split; [apply wle_refl|].
  split.
  { intros r Hr. assert (HrZ : bv_unsigned (Z_to_bv 5 r) = r).
    { rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32. unfold acallee_saved in Hr. apply Z.mod_small. lia. }
    rewrite <- (dregs_other regs 0 inst bp so (Z_to_bv 5 r)) by (rewrite HrZ; unfold acallee_saved in Hr; lia). fold regs0.
    apply RCS. unfold callee_saved. unfold acallee_saved in Hr. exact Hr. }
  split; [apply same_io_wvb|].
  (* the raw frame, from the arm's raw memory facts; the aview clause follows *)
  assert (FRAWn : forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly (dtick S) (bv_unsigned x) ->
    ~ ascratch B DeallocG.DFSTACK_G regs (bv_unsigned x) ->
    ~ (PNull <> PNull /\ sptr_addr B ly PNull <= bv_unsigned x < sptr_addr B ly PNull + req_size n) ->
    mem' x = mem x).
  { intros x NO NO' NS NE. assert (Ra : 0 <= bv_unsigned x < 2 ^ 64) by apply u64_range.
    destruct (Z.eq_dec (bv_unsigned x) (ly_T ly + t_unwinding)) as [Ea|Ea].
    - assert (OFF : off_img (bv_unsigned x))
        by (rewrite Ea; apply (zone3_off_img _ _ _ hT1); unfold kThreadObjSize, t_unwinding; lia).
      pose proof (UNW 0%nat ltac:(lia)) as V1. pose proof (HUNW0 0%nat ltac:(lia)) as V2.
      cbn [Z.of_nat] in V1, V2. rewrite Z.add_0_r in V1, V2. rewrite <- Ea in V1, V2.
      assert (Ex : Z_to_bv 64 (bv_unsigned x) = x) by apply Z_to_bv_bv_unsigned.
      rewrite <- Ex. rewrite (mbyte_off_raw _ _ _ _ OFF V1), (mbyte_off_raw _ _ _ _ OFF V2). reflexivity.
    - apply (proj1 MEQR x).
      + unfold DGgn.WIN. rewrite R2. fold sp0. intros [Hs|Hu].
        * apply NS. left. unfold spZ, DeallocG.DFSTACK_G. fold sp0. unfold DFSTACK in Hs. exact Hs.
        * apply Ea. lia.
      + intros Hi. apply NO. exact (di_owned_i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md _ HARX Hi). }
  split.
  { intros a Ra NO NO' NS NE. apply aview_same.
    assert (Ex : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ra).
    apply (FRAWn (Z_to_bv 64 a)); rewrite Ex; assumption. }
  split; [exact FRAWn|].
  intros a Ha. unfold spZ, DeallocG.DFSTACK_G in Ha. fold sp0 in Ha. unfold DFSTACK in PRES'. exact (PRES' a Ha). }
(* errno: its 4 bytes are outside MEQR's excluded set (DGgn.WIN, DGgn.IZONE). errno is in the image at TFIB_ERRNO
   (TfibSyms.ts_errno); the stack window is above kHighMemBeg, the unwinding byte is in the thread object, off the
   image (zone3), and IZONE ends below errno. *)
assert (ERR : ErrnoG.errno_kept B mem mem').
{ intros i Hi. pose proof STK64 as [_ K2].
  assert (EB : bv_unsigned (w64 (as_errno B + i)) = TFIB_ERRNO + i)
    by (rewrite (ts_errno _ TS); apply w64_unsigned; unfold TFIB_ERRNO; lia).
  apply (proj1 MEQR).
  - unfold DGgn.WIN. rewrite R2. fold sp0. rewrite EB. intros [Hs|Hu].
    + unfold TFIB_ERRNO, kHighMemBeg, DFSTACK in *. lia.
    + assert (OFF : off_img (TFIB_ERRNO + i))
        by (apply (zone3_off_img _ _ _ hT1); unfold kThreadObjSize, t_unwinding in *; lia).
      unfold off_img, TFIB_IMG_LO, TFIB_IMG_END, TFIB_ERRNO in OFF. lia.
  - unfold DGgn.IZONE. rewrite EB. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_ERRNO. lia. }
(* memnorm: the same raw MEQR keeps it (memnorm_MEQN). *)
assert (MNK : MemnormT.memnorm_keep tfibsegs mem mem').
{ refine (memnorm_MEQN ly (dregs regs 0 inst bp so) mem mem' (dn_ly _ _ _ _ _ LOv) (dn_img _ _ _ _ _ LOv) _ _ (proj1 MEQR)).
  - rewrite R2. exact Hlo.
  - rewrite R2. exact Hhi. }
(* copy of DGg3.v:489-492, unchanged *)
split; [exact ERR|].
split.
{ intros a Ha. apply aview_same. pose proof (ERR (a - as_errno B) ltac:(lia)) as E.
  replace (as_errno B + (a - as_errno B)) with a in E by lia. unfold w64 in E. exact E. }
split; [exact MNK|].
(* copy of DGg3.v:493-494, unchanged *)
split; [exact HLP | exact HPATH].
Qed.
End c.

(* DGg3.dealloc_null_arm_e (DGg3.v:513) with memnorm kept. *)
Theorem dealloc_null_arm_em : forall inst so bp ly S W regs mem md p n tr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr -> p = PNull ->
amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x32390 regs mem md)
(MemnormDleafB.dealloc_leaf_raw_eem B ft ARX AOX lpost inst ly S W regs mem md p n tr).
Proof. intros inst so bp ly S W regs mem md p n tr PRE0 ->. exact (null_arm_c_em inst so bp ly S W regs mem md n tr PRE0). Qed.
End b.
End a.
