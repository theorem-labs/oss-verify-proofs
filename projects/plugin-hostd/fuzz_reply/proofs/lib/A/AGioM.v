(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGioM.v (commit fec7cbb6287c, round-2 layer (P'' re-take, sweep parts 1-6); file sha256 ecb060821ea6) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 1 image addresses moved by code-verified function pairs (2 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* Taken by path from a working branch 5ca1fbe20ff9 (the HNW weakening `NMAXW + 4 * 4096 <= 2 ^ 30`), before c5 installs it. *)
(* Theorem Labs, 2026-10 (task MEMNORM, full Allocate): the memnorm-kept twin of AGioE.alloc_sec_e (the SECONDARY arm
   of the frame-generic Allocate contract): [alloc_sec_em] concludes MemnormT.alloc_leaf_em (ErrnoG.alloc_leaf_e plus
   `memnorm mem -> memnorm mem'`) in place of ErrnoG.alloc_leaf_e, from AGioE's hypotheses.
   rule 24: no function proved (kind: arm twin, frame corollary).

   The proof is AGioE.alloc_sec_w_e's (AGioE.v:73-212), with AGk0M.sec_arms_w_em for AGk0E.sec_arms_w_e and the keep
   carried through the leaf conversion (the virtual register file does not touch memory); the changed lines are marked
   (* memnorm *).  AGioE and every existing statement are unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AE3d AFhy AGhy AGi9 AGid AGie AGif.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGjh AGji AGjm AGjw AGjx AGjy AGk0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFi3 AllocG AGif0reply AGif0n AGif2 AGif4 AGik.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply AGif4reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AGk0E ErrnoG ErrnoGS AllocGtopE.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AGk0M AllocGtopM MemnormT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YA00.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

Section fw.
Variable B : asyms.
(* The trace premise (C5): a predicate on the trace and the state (cgif: In tr (as_universe B)). *)
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variables (nmax lmax : Z).
Variable lpost : astate -> Prop.
Variable dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variables (mtag stag : Z).
Hypothesis IF : AGif0n.AIface B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag.
(* The widened bounds, as in AGio.alloc_sec_w: the walk's own cap, the instance's grant-existence bound NOBW and
   its room ROOMW (AGif4.AIfaceSw). *)
Variables (NMAXW NOBW ROOMW : Z).
Hypothesis HNW : NMAXW + 4 * 4096 <= 2 ^ 30.
Hypothesis HNOB : NMAXW + 4 * 4096 <= NOBW.
Hypothesis HROOM : 2 * (NMAXW + 4 * 4096) + (NMAXW + 4 * 4096) / 8 + 8192 + 2 ^ 19 <= ROOMW.
Hypothesis IFS : AGif4.AIfaceSw B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag NMAXW NOBW ROOMW.
Hypothesis TS : TfibSyms B.
(* Every instantiation keeps Allocate's size-too-big branch off (AllocG.v:20). *)
Hypothesis Hnmax : nmax <= NMAXW.
(* The call site's can_fill argument: 1 for malloc / realloc, 0 for calloc (AllocG's [cf]). *)
Variable cf : Z.
Hypothesis Hcfv : cf = 0 \/ cf = 1.
(* The errno add-on of AIfaceS (ErrnoGS.v): aes_post_grant is the errno fact at the grant leaf. *)
Hypothesis IFSE : ErrnoGS.AIfaceSE B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag.

Theorem alloc_sec_w_em : forall inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 cf inst so bp ly S W regs mem md n tr ->
64513 <= n ->
amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regs mem md)
(MemnormT.alloc_leaf_em tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr).
Proof.
intros inst so bp ly S W regs mem md n tr PRE Nlo.
pose proof (AGif4.ifsw_base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IFS) as IFSb.
pose proof (AGif4.ifsw_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IFS) as IFA.
pose proof (AGif4.ifsw_grant _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IFS) as IFG.
pose proof (AGif4.ifsw_room _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IFS) as IFR.
pose proof (ifs_view _ _ _ _ _ _ _ _ _ _ _ _ IFSb) as Fsview.
pose proof (ifs_shape _ _ _ _ _ _ _ _ _ _ _ _ IFSb) as Fsshape.
pose proof (ifs_mwf _ _ _ _ _ _ _ _ _ _ _ _ IFSb) as Fsmwf.
pose proof (ifs_room _ _ _ _ _ _ _ _ _ _ _ _ IFSb) as Fsroom.
pose proof (ifs_ledger _ _ _ _ _ _ _ _ _ _ _ _ IFSb) as Fsledger.
pose proof (ifs_grant _ _ _ _ _ _ _ _ _ _ _ _ IFSb) as Fsgrant.
pose proof (ifs_oom _ _ _ _ _ _ _ _ _ _ _ _ IFSb) as Fsoom.
pose proof (ifs_post_null _ _ _ _ _ _ _ _ _ _ _ _ IFSb) as Fsnull.
pose proof (ifs_post_grant _ _ _ _ _ _ _ _ _ _ _ _ IFSb) as Fsgpost.
pose proof (AGif0n.if_inst _ _ _ _ _ _ _ _ _ _ _ _ IF) as Finst.
pose proof (AGif0n.if_depot _ _ _ _ _ _ _ _ _ _ _ _ IF) as Fdepot.
pose proof (AGif0n.if_dpost_aok _ _ _ _ _ _ _ _ _ _ _ _ IF) as Fdaok.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres0 & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hn0 & Hlive).
unfold spZ, raZ, AFSTACK_G in *. rewrite (ts_tp B TS) in Htp.
assert (Nrange : 64513 <= n < NMAXW) by lia.
assert (NrangeS : 64513 <= n < SEC_NMAX) by (unfold SEC_NMAX; lia).
pose proof (Finst _ _ _ _ _ _ HARX) as HIO. pose proof HIO as (HIO1 & HIO2 & HIO3).
(* the view of the pre-state, and the model's counters *)
set (idx := Z.of_nat (length (st_sec_arr S))) in *. set (res := st_sec_reserved S) in *.
pose proof (Fsview inst ly S W mem md n HARX HRP ltac:(lia)) as SV.
pose proof (sv_idx _ _ _ _ _ _ _ SV) as Hidx. pose proof (sv_resb _ _ _ _ _ _ _ SV) as Hres.
pose proof (sv_ly _ _ _ _ _ _ _ SV) as LY. pose proof (sv_img _ _ _ _ _ _ _ SV) as IMG.
pose proof (sv_tsd _ _ _ _ _ _ _ SV) as HTSD.
(* the walk's virtual register file (AGik.vregs): a0 = this, a1 = n, a2 = 8, a3 = the stack object *)
set (regs0 := AGik.vregs regs n inst bp).
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
assert (Hso64 : 0 <= so < 2 ^ 64) by (unfold kHighMemEnd, kHighMemBeg in T4, T7; lia).
assert (Hbp64 : 0 <= bp < 2 ^ 64) by (unfold kHighMemEnd, kHighMemBeg in T4, T7; lia).
assert (Hinst64 : 0 <= inst < 2 ^ 64) by lia.
assert (HUo : forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> bv_unsigned r <> 12 -> getr regs r = getr regs0 r)
by (intros r H10 H11 H12; unfold regs0; symmetry; exact (AGik.vregs_other regs n inst bp r H10 H11 H12)).
assert (HU10 : getr regs 10%bv = getr regs0 11%bv) by (unfold regs0; rewrite Hr10, AGik.vregs_11; reflexivity).
assert (HU11 : getr regs 11%bv = getr regs0 10%bv) by (unfold regs0; rewrite Hr11, AGik.vregs_10; reflexivity).
assert (HU12 : getr regs 12%bv = w64 8) by exact Hr12.
assert (HU14 : getr regs 14%bv = w64 1) by exact Hr14.
assert (Hn : getr regs0 10 = w64 n) by (unfold regs0; apply AGik.vregs_10).
assert (Hi11 : getr regs0 11 = w64 inst) by (unfold regs0; apply AGik.vregs_11).
assert (R2 : getr regs0 2 = getr regs 2) by (unfold regs0; apply AGik.vregs_other; vm_compute; lia).
assert (R1 : getr regs0 1 = getr regs 1) by (unfold regs0; apply AGik.vregs_other; vm_compute; lia).
assert (R12 : bv_unsigned (getr regs0 12) = bp) by (unfold regs0; rewrite AGik.vregs_12; apply w64_unsigned; exact Hbp64).
assert (R13 : bv_unsigned (getr regs0 13) = so)
by (unfold regs0; rewrite (AGik.vregs_other regs n inst bp 13%bv) by (vm_compute; lia); rewrite Hr13; apply w64_unsigned; exact Hso64).
assert (R11 : bv_unsigned (getr regs0 11) = inst) by (rewrite Hi11; apply w64_unsigned; exact Hinst64).
assert (Htp0 : getr regs0 4 = w64 TFIB_TP) by (unfold regs0; rewrite (AGik.vregs_other regs n inst bp 4%bv) by (vm_compute; lia); exact Htp).
assert (Hgp0 : getr regs0 3 = w64 (as_gp B)) by (unfold regs0; rewrite (AGik.vregs_other regs n inst bp 3%bv) by (vm_compute; lia); exact Hgp).
assert (Hcf : bv_unsigned (getr regs0 15) = 0 \/ bv_unsigned (getr regs0 15) = 1).
{ unfold regs0. rewrite (AGik.vregs_other regs n inst bp 15%bv) by (vm_compute; lia). rewrite Hr15.
  destruct Hcfv as [E | E]; rewrite E; [left | right]; vm_compute; reflexivity. }
assert (HcfW : getr regs0 15 = w64 0 \/ getr regs0 15 = w64 1).
{ unfold regs0. rewrite (AGik.vregs_other regs n inst bp 15%bv) by (vm_compute; lia). rewrite Hr15.
  destruct Hcfv as [E | E]; rewrite E; [left | right]; reflexivity. }
assert (Hra0 : YK0s.ret_ok (getr regs0 1)) by (rewrite R1; exact Hra).
assert (Hra40 : 4096 <= bv_unsigned (getr regs0 1)) by (rewrite R1; exact Hra4096).
assert (Hsp : ly_stk_lo ly + AFSTACK <= bv_unsigned (getr regs0 2) /\ ly_bot ly < bv_unsigned (getr regs0 2) /\
bv_unsigned (getr regs0 2) <= ly_stk_hi ly /\ bv_unsigned (getr regs0 2) mod 16 = 0) by (rewrite R2; unfold AFSTACK; repeat split; assumption).
assert (Hso : bv_unsigned (getr regs0 2) <= bv_unsigned (getr regs0 13) /\ bv_unsigned (getr regs0 13) + 16 <= ly_stk_hi ly /\
bv_unsigned (getr regs0 13) mod 8 = 0) by (rewrite R2, R13; repeat split; assumption).
assert (Hbp : bv_unsigned (getr regs0 2) <= bv_unsigned (getr regs0 12) /\ bv_unsigned (getr regs0 12) + 8 * 30 <= ly_stk_hi ly /\
bv_unsigned (getr regs0 12) mod 8 = 0) by (rewrite R2, R12; repeat split; assumption).
(* the instance window of the walk (AGjh / AGjw's Hinst), from the interface's inst_ok *)
assert (Hinst : 0x9d000 <= bv_unsigned (getr regs0 11) /\ bv_unsigned (getr regs0 11) + 0xe60 <= 0x128320 /\
bv_unsigned (getr regs0 11) mod 8 = 0) by (rewrite R11; repeat split; lia).
(* AIface's instance window, over the walk's x11 (AGjx / AGk0's HIO) *)
assert (HIO0 : AGif0reply.inst_ok (bv_unsigned (getr regs0 11))) by (rewrite R11; exact HIO).
(* [from_primary] is the model's own size test (needed_primary n <=? kMaxSize), so it comes from the walk's
   size arithmetic (AGjy.sizes_model), not from [lia] on n. *)
assert (FP : from_primary n = false)
by (pose proof (AGjy.sizes_model ly regs0 n tr (st_sec_reserved S) Htrlen Hinst NrangeS S) as SM; tauto).
assert (Hpres00 : forall a, bv_unsigned (getr regs0 2) - AFSTACK <= a < bv_unsigned (getr regs0 2) -> apresent (w_H W) mem a)
by (rewrite R2; unfold AFSTACK; exact Hpres0).
assert (PSO0 : val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 13)) 8 (bv_unsigned (getr regs0 12))) by (rewrite R13, R12; exact PSO).
assert (PLEN0 : val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 13) + 8) 8 (Z.of_nat (length tr))) by (rewrite R13; exact PLEN).
assert (PBUF0 : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 12) + 8 * Z.of_nat i) 8 (nth i tr 0))
by (rewrite R12; exact PBUF).
assert (SVr : AGif2.sview B W ly (bv_unsigned (getr regs0 11)) mem idx res) by (rewrite R11; exact SV).
(* the seed's junk atoms: the thread's and the instance's stats words (AGi9.SREG0's atoms) *)
pose proof (@AGjm.BSLv_range ly regs0 n tr idx res 0 Htrlen Hinst NrangeS Hidx) as HB.
destruct (AGif2.sv_junk_values B W ly (bv_unsigned (getr regs0 11)) mem idx res TS SVr (AGjm.BSLv regs0 n)
ltac:(unfold o_sec_stats; lia) ltac:(unfold o_sec_mutex; lia))
as (j0 & j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & i1 & i2 & i3 & Hj0 & Hj1 & Hj2 & Hj3 & Hj4 & Hj5 & Hj9 & Hj6 & Hj7 & Hj8 & Hi1 & Hi2 & Hi3).
(* the seed at Allocate's entry (AGjx.SEED_ok over the view), at every block base: the prefix reads it at
   mb := 0, the grant arms at the granted base (AGjr.grant_cont) *)
assert (SEED : forall mb, st_ok tfibsegs (AGjm.E0 ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb) AGid.S_1
(restrict (w_H W) (mkst regs (w64 A_Allocate) mem (seg_rom tfibsegs)))).
{ intros mb.
  exact (AGjx.SEED_ok W ly regs0 mem n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Htp0 Hsp Htrlen
    Hso Hbp Hinst HIO0 NrangeS Hidx Hres Hpres00 PSO0 PLEN0 HcfW regs HUo HU10 HU11 HU12 HU14
    (fun (_ : Z) (_ : word -> option byte) => True) B TS SVr Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3). }
(* The walk, over the virtual register file: the model's tree is the tick, the size check and the kernel's mmap
   ask (ifs_shape), and AGk0E.sec_arms_e runs the machine from Allocate's entry to its ret on both arms. *)
assert (MAIN : amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regs mem md)
(AGk0M.alloc_leaf0_em B ARX AOX lpost TFIB_OOM inst ly S W regs0 mem md n)). (* memnorm *)
{ rewrite (Fsshape n tr S ltac:(lia) FP).
  eapply amreal_pure; [reflexivity|].
  eapply amreal_pure; [unfold mcheck; replace (n <? kMaxAllowedMalloc - kPage) with true
  by (symmetry; apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage in *; lia); reflexivity|].
  assert (Hnlt : n < nmax) by lia.
  (* memnorm *)
  exact (AGk0M.sec_arms_w_em B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF IFSb NMAXW NOBW ROOMW IFA IFG IFR HNOB HROOM TS inst ly S W regs0 mem md n tr
     idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG HTSD Hn Hi11 Htp0 Hgp0 Hra0 Hra40 Hcf Hsp Htrlen Hso Hbp
     Hinst NrangeS (proj2 Nrange) Hnlt Hidx Hres eq_refl eq_refl Hpres00 PBUF0 SVr HARX HRP Htr Hlive regs SEED IFSE). }
(* Every result is the end of a granted path of the whole tree (AGif0n.amreal_apath_gflag), and the leaf over the
   virtual register file is the leaf over the caller's: they agree on x1, x2 and every callee-saved register, and
   AllocG's frame clause reads only those. *)
eapply amreal_mono; [| exact (AGif0n.amreal_apath_gflag tfibsegs _ _ _ _ MAIN)].
intros r W' c' [HL0 HPATH].
apply (AGk0M.alloc_leaf_intro_em B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr r W' c'); [| exact HPATH]. (* memnorm *)
destruct HL0 as (ly' & regs' & mem' & md' & Hc & (HARX' & HLE & HWLE & HRCS & HIO' & HFR & HRAW & HPRS) & HERR & HKEEP & HR10 & HLP & HOOM). (* memnorm: HKEEP *)
exists ly', regs', mem', md'.
split. { rewrite Hc. unfold cfg_at, raZ. rewrite <- R1. reflexivity. }
split.
{ split; [exact HARX'|]. split; [exact HLE|]. split; [exact HWLE|].
  split.
  { intros rr Hrr. rewrite (HUo (Z_to_bv 5 rr)).
    - exact (HRCS rr Hrr).
    - rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32.
      unfold acallee_saved in Hrr. rewrite Z.mod_small by lia. lia.
    - rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32.
      unfold acallee_saved in Hrr. rewrite Z.mod_small by lia. lia.
    - rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32.
      unfold acallee_saved in Hrr. rewrite Z.mod_small by lia. lia. }
  split; [exact HIO'|].
  split.
  { intros a Ra NO NO' NS NE. apply HFR; try assumption.
    intros Hs. apply NS. unfold ascratch, spZ in *. rewrite R2 in Hs. exact Hs. }
  split.
  { (* the raw frame: the same exception sets, the scratch window read off x2, which regs and regs0 share *)
    intros x NO NO' NS NE. apply HRAW; try assumption.
    intros Hs. apply NS. unfold ascratch, spZ in *. rewrite R2 in Hs. exact Hs. }
  intros a Ha. apply HPRS. unfold spZ in *. rewrite R2. exact Ha. }
(* errno on the grant branch: the same raw memories mem / mem' *)
split; [exact HERR|].
(* memnorm: the keep, on the same raw memories *)
split; [exact HKEEP|].
split; [exact HR10|]. split; [exact HLP | exact HOOM].
Qed.
(* The same, in the form AllocGtopM.aalloc_realizes_em_of_prim_sec_em composes with the primary case. *)
Corollary alloc_sec_w_em_realizes :
AllocGtopM.aalloc_sec_realizes_em tfibsegs B U mt ARX AOX rpre nmax lmax lpost A_Allocate TFIB_OOM 8 1 cf.
Proof. exact alloc_sec_w_em. Qed.
End fw.

(* alloc_sec_em, the statement at the cgif model's bound MALLOC_MAX: alloc_sec_w_em at NMAXW := MALLOC_MAX, NOBW :=
   ImgBaseAGS.NOB, ROOMW := 2 ^ 30 (AGif4.AIfaceS_w). *)
Section f.
Variable B : asyms.
(* The trace premise (C5): a predicate on the trace and the state (cgif: In tr (as_universe B)). *)
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variables (nmax lmax : Z).
Variable lpost : astate -> Prop.
Variable dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variables (mtag stag : Z).
Hypothesis IF : AGif0n.AIface B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag.
Hypothesis IFS : AGif4.AIfaceS B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag.
Hypothesis TS : TfibSyms B.
(* Every instantiation keeps Allocate's size-too-big branch off (AllocG.v:20). *)
Hypothesis Hnmax : nmax <= MALLOC_MAX.
(* The call site's can_fill argument: 1 for malloc / realloc, 0 for calloc (AllocG's [cf]). *)
Variable cf : Z.
Hypothesis Hcfv : cf = 0 \/ cf = 1.
(* The errno add-on of AIfaceS (ErrnoGS.v): aes_post_grant is the errno fact at the grant leaf. *)
Hypothesis IFSE : ErrnoGS.AIfaceSE B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag.

Theorem alloc_sec_em : forall inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 cf inst so bp ly S W regs mem md n tr ->
64513 <= n ->
amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regs mem md)
(MemnormT.alloc_leaf_em tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr).
Proof.
exact (alloc_sec_w_em B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF MALLOC_MAX ImgBaseAGS.NOB (2 ^ 30)
  ltac:(unfold MALLOC_MAX; lia) ltac:(unfold MALLOC_MAX, ImgBaseAGS.NOB; lia) ltac:(unfold MALLOC_MAX; vm_compute; discriminate)
  (AGif4.AIfaceS_w _ _ _ _ _ _ _ _ _ _ _ _ IFS) TS Hnmax cf Hcfv IFSE).
Qed.
End f.
End d.
