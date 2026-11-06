(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/MemnormDnullRh.v (commit eb934de95d13, blob 405abc36d377) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 2 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AE3d AFeq AFex DGbase DGgn DGfx DGh1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AllocG DeallocG AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AGImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFfu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DGleafE.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DGg3Rh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require MemnormDleaf MemnormHitG MemnormSafepreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require DIfaceRh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DGg3Rh.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

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
    * apply MemnormHitG.mn_safe_high. unfold DGbase.DFSTACK, kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
    * apply (MemnormHitG.mn_safe_owned ly (ly_T ly, kThreadObjSize) x LY IMG
        ltac:(unfold owned_extents; right; right; left; reflexivity)).
      cbn [fst snd]. unfold kThreadObjSize, t_unwinding in *. lia.
  + unfold DGgn.IZONE in Hz. apply MemnormSafepreset.mn_safe_rw.
    unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TASK_SIZE in *. lia.
- intros x NZ. apply MEQ; intros X; apply NZ; [left | right]; exact X.
Qed.

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
Hypothesis IF : DIfaceRh.DIface_rh B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP.

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

Let PREd := DGg3Rh.PREd B TS U ARX rpre fpre inst so bp ly S W regs mem md n tr PRE.
Let LOv := DGg3Rh.LOv B TS U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF inst so bp ly S W regs mem md n tr PRE.
Let HIGH := DGg3Rh.HIGH B TS U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF inst so bp ly S W regs mem md n tr PRE.
Let STK64 := DGg3Rh.STK64 B TS U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF inst so bp ly S W regs mem md n tr PRE.
Let R1 := DGg3Rh.R1 inst so bp regs.
Let R2 := DGg3Rh.R2 inst so bp regs.
Let null_main := DGg3Rh.null_main B TS U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF inst so bp ly S W regs mem md n tr PRE.

Theorem null_arm_c_em : amreal tfibsegs (ft PNull tr S) W (cfg_at tfibsegs 0x322a4 regs mem md)
(MemnormDleaf.dealloc_leaf_raw_eem B ft ARX AOX lpost inst ly S W regs mem md PNull n tr).
Proof.

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
destruct (DIfaceRh.dih_post_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md n tr sp0 mem' mat HARX HRP HFP HTU
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
      + intros Hi. apply NO. exact (DIfaceRh.dih_owned_i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md _ HARX Hi). }
  split.
  { intros a Ra NO NO' NS NE. apply aview_same.
    assert (Ex : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ra).
    apply (FRAWn (Z_to_bv 64 a)); rewrite Ex; assumption. }
  split; [exact FRAWn|].
  intros a Ha. unfold spZ, DeallocG.DFSTACK_G in Ha. fold sp0 in Ha. unfold DFSTACK in PRES'. exact (PRES' a Ha). }

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

assert (MNK : MemnormT.memnorm_keep tfibsegs mem mem').
{ refine (memnorm_MEQN ly (dregs regs 0 inst bp so) mem mem' (dn_ly _ _ _ _ _ LOv) (dn_img _ _ _ _ _ LOv) _ _ (proj1 MEQR)).
  - rewrite R2. exact Hlo.
  - rewrite R2. exact Hhi. }

split; [exact ERR|].
split.
{ intros a Ha. apply aview_same. pose proof (ERR (a - as_errno B) ltac:(lia)) as E.
  replace (as_errno B + (a - as_errno B)) with a in E by lia. unfold w64 in E. exact E. }
split; [exact MNK|].

split; [exact HLP | exact HPATH].
Qed.
End c.

Theorem dealloc_null_arm_em : forall inst so bp ly S W regs mem md p n tr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr -> p = PNull ->
amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x322a4 regs mem md)
(MemnormDleaf.dealloc_leaf_raw_eem B ft ARX AOX lpost inst ly S W regs mem md p n tr).
Proof. intros inst so bp ly S W regs mem md p n tr PRE0 ->. exact (null_arm_c_em inst so bp ly S W regs mem md n tr PRE0). Qed.
End b.
End a.
