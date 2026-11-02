(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN1w.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO12.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0y.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN31.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN26.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN30.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1y.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma enframe_eval_junk s g am idx n ctr k :
MT s g = Some (MUsed am) -> 0 <= idx <= am_last am -> ss_hdr (nth_slot am idx) = None ->
let slack := (stride_of am - IB - n) / UNIT in
0 <= slack -> slack <> 0 ->
enframe g idx n ctr k s =
IAsk (KJunk (Z.land ctr 255)) s (fun z => if fold_off slack (z mod 256) <=? slack
then IRet (enframe_pure am g idx n k (z mod 256) s)
else IFail (FAssert 4)).
Proof.
intros Hm Hidx Hh slack Hs0 Hs. unfold enframe.
rewrite (bind_IRet (getm g) _ s am s (getm_eval s g am Hm)).
rewrite (bind_IRet (mcheck _ 12) _ s tt s) by (unfold mcheck; rewrite (proj2 (Z.leb_le 0 idx)), (proj2 (Z.leb_le idx _)) by lia; reflexivity).
cbv zeta. fold slack. replace (slack =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hs). rewrite Hh.
match goal with |- bind _ ?K s = _ => set (KK := K) end.
unfold bind, askz, ret. cbn [ibind]. f_equal. apply functional_extensionality. intros z.
change (KK (z mod 256) s = (if fold_off slack (z mod 256) <=? slack then IRet (enframe_pure am g idx n k (z mod 256) s) else IFail (FAssert 4))).
subst KK. cbv beta.
match goal with |- bind (massert (?o <=? _) _) _ s = _ => change o with (fold_off slack (z mod 256)) end.
unfold massert. destruct (fold_off slack (z mod 256) <=? slack).
- rewrite (bind_IRet (ret tt) _ s tt s) by reflexivity. unfold enframe_pure. cbv zeta. fold slack. reflexivity.
- reflexivity.
Qed.
Lemma fold_off_0' x : 0 <= x < 256 -> fold_off 0 x = 0.
Proof. intros Hx. pose proof (fold_off_ok 0 x ltac:(lia) Hx). lia. Qed.
Lemma enframe_eval0 s g am idx n ctr k :
MT s g = Some (MUsed am) -> 0 <= idx <= am_last am ->
(stride_of am - IB - n) / UNIT = 0 ->
enframe g idx n ctr k s = IRet (enframe_pure am g idx n k 0 s).
Proof.
intros Hm Hidx Hs0. unfold enframe.
rewrite (bind_IRet (getm g) _ s am s (getm_eval s g am Hm)).
rewrite (bind_IRet (mcheck _ 12) _ s tt s) by (unfold mcheck; rewrite (proj2 (Z.leb_le 0 idx)), (proj2 (Z.leb_le idx _)) by lia; reflexivity).
cbv zeta. rewrite Hs0. cbn [Z.eqb].
match goal with |- bind ?m0 _ s = _ => rewrite (bind_IRet m0 _ s 0 s) by reflexivity end.
match goal with |- bind (massert (?o <=? _) _) _ s = _ => change o with (fold_off 0 0) end.
rewrite (fold_off_0' 0) by lia.
rewrite (bind_IRet (massert _ 4) _ s tt s) by reflexivity.
unfold enframe_pure. cbv zeta. rewrite Hs0, (fold_off_0' 0) by lia. reflexivity.
Qed.
Lemma In_ctx_image' A c : In c (ctx_cells A) -> In c (image A).
Proof. intros H. unfold image. apply in_app_iff. left. exact H. Qed.
Lemma In_ctx_ctr' A : In (MCell (LCtx CTX_mmap_counter) 4 (VZ (st_mmap_counter A))) (ctx_cells A).
Proof. unfold ctx_cells. apply in_app_iff. left. cbn. right. right. left. reflexivity. Qed.
Lemma src0_img_range' a : in_img B a -> 0x10000 <= a < 0x51000.
Proof.
intros [_ (sg & Hs & Ha)].
assert (H : forallb (fun sg : word * word => (0x10000 <=? bv_unsigned (fst sg)) && (bv_unsigned (fst sg) + bv_unsigned (snd sg) <=? 0x51000))
(segments_reserved src0segs) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H sg Hs). apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma errno_img' x : errno_addr B <= x < errno_addr B + 4 -> in_img B x.
Proof. intros Hx. apply in_img1_in_img. unfold in_img1. unfold errno_addr in Hx. cbn [ms_tp ms_errno_off src0_msyms] in Hx. unfold src0_tp in Hx. lia. Qed.
Section e.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (n : Z).
Hypothesis PRE : call_pre B (MRx B) L A regs mem md.
Hypothesis Hn : 0 <= n < MMAP_THRESHOLD.
Definition SPv : Z := spZ regs.
Variables (Lc : layout) (Ac : astate) (mc : word -> option byte) (mdc : Model).
Variables (gm : sptr) (am : ameta) (idx sc : Z) (rg : bvmap 5 word).
Hypothesis MID : midrep B Lc Ac mc mdc.
Hypothesis HI : Inv [] (Some (gm, idx)) U0 Ac.
Hypothesis Hu : usedX [] Ac gm am.
Hypothesis Hsc : am_sc am = sc /\ 0 <= sc < 48.
Hypothesis Hfit : n + IB <= stride_of am.
Hypothesis Hidx : 0 <= idx <= am_last am.
Hypothesis Hhd : active_hd Ac sc = Some gm.
Hypothesis HBc : bounded Ac.
Hypothesis HAc : ama_ok Ac.
Hypothesis HRc : rsv_ok Ac.
Hypothesis HSc : span_ok Ac.
Hypothesis LE : layout_le A L Lc.
Hypothesis VM : exists vm, mdc = with_vmmaps vm md.
Hypothesis UB : ub_same A Ac.
Hypothesis R18 : getr rg 18 = Z_to_bv 64 (ptr_addr Lc gm).
Hypothesis R19 : getr rg 19 = Z_to_bv 64 idx.
Hypothesis R8 : getr rg 8 = Z_to_bv 64 n.
Hypothesis R9 : getr rg 9 = Z_to_bv 64 LOCK.
Hypothesis R2 : getr rg 2 = Z_to_bv 64 (SPv - 48).
Hypothesis R4 : getr rg 4 = Z_to_bv 64 TP.
Hypothesis RCS : forall i, In i CSAVED -> getr rg (nat_to_reg i) = getr regs (nat_to_reg i).
Hypothesis FRAME : forall off r, In (off, r) FRAME_SLOTS -> bytes_are mc (SPv - 48 + off) 8 (bv_unsigned (getr regs (nat_to_reg r))).
Hypothesis OUT : forall x, 0 <= x < 2 ^ 64 -> ~ owned B L A x -> ~ owned B Lc Ac x -> ~ in_nonmap_region Lc Ac x -> ~ scratch B regs x ->
mc (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Hypothesis WSCR : forall a, scratch B regs a -> writable_at src0segs mc a.
Hypothesis ZERO : stride_of am < class_size sc ->
forall i, 0 <= i < stride_of am - IB -> mbyte src0segs mc (ptr_addr Lc (slot_start am idx) + i) = Some (Z_to_bv 8 0).
Let rom := seg_rom src0segs.
Definition ctr : Z := st_mmap_counter Ac.
Definition G : Z := ptr_addr Lc gm.
Definition Mb : Z := ptr_addr Lc (am_mem am).
Definition P0 : Z := ptr_addr Lc (slot_start am idx).
Lemma PRE_facts : MRx B L A mem md /\ WF A /\ bounded A /\ YK0s.ret_ok (getr regs 1) /\
SPv mod 16 = 0 /\ alloc_ceiling + 8192 <= SPv /\ SPv < 2 ^ 63 /\
(forall a, SPv - 8192 <= a < SPv -> writable_at src0segs mem a) /\ getr regs 4 = Z_to_bv 64 (ms_tp B) /\
(forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at src0segs mem a) /\
(st_init_done A = false -> auxv_pre B (ly_sec L) SPv mem).
Proof. unfold call_pre, ALLOC_STACK in PRE. exact PRE. Qed.
Lemma Hmdc : m_halted mdc = None /\ m_vm_lazy mdc = [] /\ m_vm_materialized mdc = [].
Proof. exact (mid_md _ _ _ _ _ MID). Qed.
Let Mg : MT Ac gm = Some (MUsed am) := proj1 (usedX_MT _ _ _ _ Hu).
Lemma G_facts :
0 <= am_last am <= 31 /\ length (am_slots am) = Z.to_nat (am_last am + 1) /\ 16 <= stride_of am /\
ss_fr (nth_slot am idx) = None /\ allocated am idx = true /\ 0 <= am_maplen am /\
stride_of am * (am_last am + 1) < 2 ^ 20 /\ 0 <= ctr < 2 ^ 32 /\
(ss_hdr (nth_slot am idx) = None -> am_maplen am = 0) /\
(forall h3 h16, ss_hdr (nth_slot am idx) = Some (h3, h16) -> 0 <= h3 <= 255 /\ 0 <= h16 <= 65535).
Proof.
pose proof (inv_groups HI gm am Hu) as GG. pose proof (stride_pos _ _ _ _ _ GG) as Sp.
pose proof GG as ((Glast & _ & Glen & _) & Gml & Gsl & Gcl & _).
destruct (inv_reserved HI gm idx eq_refl) as (am_ & Hu_ & _ & Hfr_ & Hal_). pose proof (usedX_fun _ _ _ _ _ Hu_ Hu) as ->.
pose proof (Gsl idx Hidx) as (S1 & S2 & _).
pose proof (inv_ctx HI) as (_&_&_&_&_&_&_&_&Rctr&_).
split; [exact Glast|]. split; [exact Glen|]. split; [exact Sp|]. split; [exact Hfr_|]. split; [exact Hal_|]. split; [exact Gml|].
split; [destruct Gcl as [(C & _)|(_ & _ & _ & C)]; [lia | exact C]|]. split; [exact Rctr|]. split; [exact S1 | exact S2].
Qed.
Lemma geo :
exists kr ko GLO ST rgn,
am_mem am = SP kr ko /\ ly_reg Lc kr = GLO /\ stride_of am = ST /\
P0 = GLO + ko + 16 + ST * idx /\ Mb = GLO + ko /\ 0 <= ST * idx /\ ST * idx + ST <= ST * (am_last am + 1) /\
region_of Ac kr = Some rgn /\ rg_kind rgn = RkMap /\ rg_live rgn = true /\ 0 <= ko /\
ko + 16 + ST * (am_last am + 1) <= rg_len rgn /\ 4096 <= GLO /\ GLO + rg_len rgn <= alloc_ceiling /\
(forall x, GLO <= x < GLO + rg_len rgn -> ~ in_img B x) /\
In (LMem (SP kr 0), rg_len rgn) (footprint Ac) /\
4096 <= G /\ G + 40 <= alloc_ceiling /\ G mod 8 = 0 /\ (forall y, G <= y < G + 40 -> ~ in_img B y) /\
(exists a, In a (st_areas Ac) /\ In (LMem a, PGSZ) (footprint Ac) /\ loc_addr Lc (LMem a) <= G /\ G + 40 <= loc_addr Lc (LMem a) + PGSZ /\
(GLO + rg_len rgn <= loc_addr Lc (LMem a) \/ loc_addr Lc (LMem a) + PGSZ <= GLO)).
Proof.
pose proof G_facts as (Glast & Glen & Sp & Hnone & Hal & Gml & Gext & _).
destruct (used_group_region [] (Some (gm, idx)) U0 Ac gm am HI Hu) as (rgn & Hr & Hk & Hl & Ho & Hext & _).
destruct (am_mem am) as [kr ko] eqn:Emem. cbn [prid poff] in *.
destruct (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID) _ _ Hr Hl) as (Ral & R4096 & Rceil & Rimg).
destruct (key_facts [] (Some (gm, idx)) U0 Lc Ac mdc HI (mid_ledger _ _ _ _ _ MID) gm (MUsed am) Mg) as (K1 & K2 & K3 & K4 & (a & Ha & Hfa & Ka1 & Ka2)).
pose proof (footprint_region_In Ac _ _ Hr Hk Hl) as InR.
exists kr, ko, (ly_reg Lc kr), (stride_of am), rgn.
assert (P1 : 0 <= stride_of am * idx) by nia. assert (P2 : stride_of am * idx + stride_of am <= stride_of am * (am_last am + 1)) by nia.
unfold group_extent, UNIT, IB in Hext.
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [unfold P0, ptr_addr, loc_addr, slot_start; rewrite Emem; cbn [padd]; unfold UNIT; lia|].
split; [unfold Mb, ptr_addr, loc_addr; rewrite Emem; cbn; lia|].
split; [lia|]. split; [lia|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [lia|]. split; [exact Rimg|]. split; [exact InR|].
split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|].
exists a. split; [exact Ha|]. split; [exact Hfa|]. split; [exact Ka1|]. split; [exact Ka2|].
pose proof (mid_layout _ _ _ _ _ MID) as (_ & _ & PW & _).
assert (Hne : (LMem (SP kr 0), rg_len rgn) <> (LMem a, PGSZ)).
{ intros E0. injection E0 as E1 E2.
destruct (proj1 (proj2 (inv_areas HI)) a Ha) as (ra & oa & rga & Ea & Hoa & Hoa2 & Hra & Hral & Hoalen & Hrak).
rewrite Ea in E1. injection E1 as <- Eo. rewrite Hr in Hra. injection Hra as <-. rewrite Hk in Hrak. exact Hrak. }
destruct (pairwise_map_In YO0f.ranges_disjoint (crange Lc) (footprint Ac) _ _ PW InR Hfa Hne) as [[D|D]|[D|D]];
cbn [fst snd loc_addr crange] in D; destruct a as [ra' oa']; cbn [loc_addr] in *; clear - D; lia.
Qed.
Definition xv5 (k : nat) : Z :=
if (k <? 32)%nat then bv_unsigned (getr rg (nat_to_reg k))
else match k with
| 33%nat => ctr
| 34%nat => bv_unsigned (getr regs 20) | 35%nat => bv_unsigned (getr regs 19) | 36%nat => bv_unsigned (getr regs 18)
| 37%nat => bv_unsigned (getr regs 9) | 38%nat => bv_unsigned (getr regs 8) | 39%nat => bv_unsigned (getr regs 1)
| _ => 0
end.
Lemma XR5 : forall k, 0 <= xv5 k < 2 ^ 64.
Proof.
intros k. pose proof G_facts as (_ & _ & _ & _ & _ & _ & _ & Rctr & _). unfold xv5. destruct (k <? 32)%nat; [apply u64_range|].
pose proof (u64_range (getr regs 20)). pose proof (u64_range (getr regs 19)). pose proof (u64_range (getr regs 18)).
pose proof (u64_range (getr regs 9)). pose proof (u64_range (getr regs 8)). pose proof (u64_range (getr regs 1)).
do 40 (destruct k as [|k]; [lia|]). lia.
Qed.
Lemma xv5_reg k : (k <= 31)%nat -> xv5 k = bv_unsigned (getr rg (nat_to_reg k)).
Proof. intros Hk. unfold xv5. replace (k <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. Qed.
Lemma T5_st_ok : st_ok src0segs (EV xv5) ss_T5 (mkst rg (Z_to_bv 64 PC) mc rom).
Proof.
pose proof PRE_facts as (_ & _ & _ & _ & Hal & Hceil & Hsp63 & _). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof G_facts as (_ & _ & _ & _ & _ & _ & _ & Rctr & _).
pose proof (mid_statics _ _ _ _ _ MID) as ST. pose proof (mid_mem _ _ _ _ _ MID) as MM. pose proof (mid_ctx _ _ _ _ _ MID) as EC.
assert (XSP : xv5 aSP = SPv - 48).
{ rewrite xv5_reg by (unfold aSP; lia). change (nat_to_reg aSP) with (2%bv : bv 5). rewrite R2. apply lit64_small. lia. }
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts ss_T5 resv_denot].
repeat (split; [reflexivity|]). split; [|split].
- apply regs_ok_lit. intros k Hk.
destruct (Nat.eq_dec k 9) as [->|Hk9]; [cbn; exact R9|]. destruct (Nat.eq_dec k 4) as [->|Hk4]; [cbn; exact R4|].
replace (find (fun p : nat * Z => Nat.eqb (fst p) k) [(9%nat, LOCK); (4%nat, TP)]) with (@None (nat * Z)).
2:{ cbn [find fst]. replace (Nat.eqb 9 k) with false by (symmetry; apply Nat.eqb_neq; lia). replace (Nat.eqb 4 k) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity. }
rewrite xv5_reg by lia. symmetry. apply Z_to_bv_bv_unsigned.
- split; [vm_compute; reflexivity|]. split.
+ unfold t5_mem. repeat apply Forall_cons; [| | | apply Forall_nil].
*   apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_frame]; rewrite (base_val_EV xv5 XR5), XSP; [lia | lia | intros; lia |].
repeat apply Forall_cons; [| | | | | | apply Forall_nil];
(eapply (chunk_ok_val xv5 _ _ _ 8); [apply (U_off0 xv5 XR5) | apply u64_range |]);
[ exact (FRAME 0 20%nat ltac:(cbn; auto 10)) | exact (FRAME 8 19%nat ltac:(cbn; auto 10)) | exact (FRAME 16 18%nat ltac:(cbn; auto 10))
| exact (FRAME 24 9%nat ltac:(cbn; auto 10)) | exact (FRAME 32 8%nat ltac:(cbn; auto 10)) | exact (FRAME 40 1%nat ltac:(cbn; auto 10)) ].
*   apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_lock base_val]; [unfold LOCK, src0_D_malloc_lock; lia | unfold LOCK, src0_D_malloc_lock; lia | intros; lia |].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_lit0. intros k Hk. rewrite Z.add_0_l. apply (st_lock _ _ ST). exact Hk.
*   apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_ctr base_val]; [unfold CTX, src0_D_malloc_context; lia | unfold CTX, src0_D_malloc_context; lia | intros; lia |].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val xv5 _ _ _ 4); [apply (U_off0 xv5 XR5) | change (xv5 aCTR) with ctr; change (8 * Z.of_N 4) with 32; lia |].
intros k Hk. rewrite Z.add_0_l.
pose proof (memrep_cell B Lc Ac mc _ MM (In_ctx_image' Ac _ (In_ctx_ctr' Ac))) as C.
unfold cell_mem in C. cbn [mc_loc mc_w mc_val loc_addr sval_num] in C. rewrite EC in C. cbn [ms_ctx src0_msyms] in C.
unfold CTX. unfold CTX_mmap_counter in C. apply C. exact Hk.
+ cbn [pairwise_disjoint all_disjoint t5_mem]. unfold extent_disjoint. cbn [r_base r_lo r_hi R_frame R_lock R_ctr].
rewrite !(base_val_EV xv5 XR5), XSP. cbn [base_val]. unfold LOCK, CTX, src0_D_malloc_lock, src0_D_malloc_context. repeat split; lia.
- unfold t5_facts. split; [|split; exact I]. cbn [atoms_ok]. split; [|split; [|exact I]].
+ unfold afact_ok. cbn [af_lo af_hi af_al2 F_sp48]. rewrite (ew_EV xv5 XR5), XSP. unfold CEIL. change (2 ^ 4) with 16.
replace (SPv - 48) with (SPv + (-3) * 16) by lia. rewrite Z_mod_plus_full. lia.
+ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (ew_EV xv5 XR5). change (xv5 aCTR) with ctr. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
Qed.
Definition c64 : Z := sx32 ctr.
Record enf_regs (r5 : bvmap 5 word) : Prop := ER5 {
e5_1 : getr r5 1 = getr regs 1;  e5_2 : getr r5 2 = Z_to_bv 64 SPv;  e5_4 : getr r5 4 = Z_to_bv 64 TP;
e5_8 : getr r5 8 = getr regs 8;  e5_9 : getr r5 9 = getr regs 9;
e5_10 : getr r5 10 = Z_to_bv 64 G;  e5_11 : getr r5 11 = Z_to_bv 64 idx;  e5_12 : getr r5 12 = Z_to_bv 64 n;  e5_13 : getr r5 13 = Z_to_bv 64 c64;
e5_18 : getr r5 18 = getr regs 18;  e5_19 : getr r5 19 = getr regs 19;  e5_20 : getr r5 20 = getr regs 20;
e5_cs : forall i, In i CSAVED -> getr r5 (nat_to_reg i) = getr regs (nat_to_reg i) }.
Lemma T5_post ms1 : st_ok src0segs (EV xv5) SST5 ms1 -> frame_of (EV xv5) t5_mem mc (ms_mem ms1) ->
ms1 = mkst (ms_regs ms1) (Z_to_bv 64 ENF) mc rom /\ enf_regs (ms_regs ms1).
Proof.
intros HS1 HF. pose proof SST5_view as V. destruct (cview_regs _ _ _ _ _ _ V) as (Hpc & Hrv & Hmem & _).
pose proof PRE_facts as (_ & _ & _ & _ & Hal & Hceil & Hsp63 & _). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof G_facts as (Glast & _ & _ & _ & _ & _ & _ & Rctr & _). pose proof geo as (kr & ko & GLO & ST & rgn & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K1 & K2 & _).
pose proof (reg_of _ _ _ 1 _ HS1 ltac:(lia) ltac:(reg_eq V 0%nat)) as G1.
pose proof (reg_of _ _ _ 2 _ HS1 ltac:(lia) ltac:(reg_eq V 1%nat)) as G2.
pose proof (reg_of _ _ _ 4 _ HS1 ltac:(lia) ltac:(reg_eq V 2%nat)) as G4.
pose proof (reg_of _ _ _ 8 _ HS1 ltac:(lia) ltac:(reg_eq V 3%nat)) as G8.
pose proof (reg_of _ _ _ 9 _ HS1 ltac:(lia) ltac:(reg_eq V 4%nat)) as G9.
pose proof (reg_of _ _ _ 10 _ HS1 ltac:(lia) ltac:(reg_eq V 5%nat)) as G10.
pose proof (reg_of _ _ _ 11 _ HS1 ltac:(lia) ltac:(reg_eq V 6%nat)) as G11.
pose proof (reg_of _ _ _ 12 _ HS1 ltac:(lia) ltac:(reg_eq V 7%nat)) as G12.
pose proof (reg_of _ _ _ 13 _ HS1 ltac:(lia) ltac:(reg_eq V 8%nat)) as G13.
pose proof (reg_of _ _ _ 18 _ HS1 ltac:(lia) ltac:(reg_eq V 9%nat)) as G18.
pose proof (reg_of _ _ _ 19 _ HS1 ltac:(lia) ltac:(reg_eq V 10%nat)) as G19.
pose proof (reg_of _ _ _ 20 _ HS1 ltac:(lia) ltac:(reg_eq V 11%nat)) as G20.
assert (GS : forall i, In i CSAVED -> getr (ms_regs ms1) (nat_to_reg i) = sv_denot (EV xv5) (SOff i 0)).
{ intros i Hi. pose proof (csaved_cases i Hi) as C.
assert (E : nth i (ss_regs SST5) (SLit 0) = SOff i 0).
{ decompose [or] C; subst i; [reg_eq V 12%nat | reg_eq V 13%nat | reg_eq V 14%nat | reg_eq V 15%nat | reg_eq V 16%nat | reg_eq V 17%nat | reg_eq V 18%nat | reg_eq V 19%nat]. }
exact (reg_of _ _ _ i _ HS1 ltac:(decompose [or] C; subst i; lia) E). }
assert (MM : ms_mem ms1 = mc) by (apply (frame_of_nowin (EV xv5) t5_mem); [repeat constructor | exact HF]).
pose proof (st_ok_mkst src0segs _ _ _ HS1 Hrv) as SHAPE. rewrite Hpc, MM in SHAPE. clear V Hpc Hrv Hmem HS1 HF.
split; [exact SHAPE|]. split.
- change (1%bv : bv 5) with (nat_to_reg 1). rewrite G1, (den_off0 xv5 XR5). apply Z_to_bv_bv_unsigned.
- change (2%bv : bv 5) with (nat_to_reg 2). rewrite G2, (den_off xv5 XR5); rewrite xv5_reg by lia; change (nat_to_reg 2) with (2%bv : bv 5); rewrite R2, lit64_small by lia; [f_equal; lia | lia].
- change (4%bv : bv 5) with (nat_to_reg 4). rewrite G4. reflexivity.
- change (8%bv : bv 5) with (nat_to_reg 8). rewrite G8, (den_off0 xv5 XR5). apply Z_to_bv_bv_unsigned.
- change (9%bv : bv 5) with (nat_to_reg 9). rewrite G9, (den_off0 xv5 XR5). apply Z_to_bv_bv_unsigned.
- change (10%bv : bv 5) with (nat_to_reg 10). rewrite G10, (den_off0 xv5 XR5). rewrite xv5_reg by lia. change (nat_to_reg 18) with (18%bv : bv 5). rewrite R18, lit64_small; [reflexivity | unfold G in *; lia].
- change (11%bv : bv 5) with (nat_to_reg 11). rewrite G11, (den_off0 xv5 XR5). rewrite xv5_reg by lia. change (nat_to_reg 19) with (19%bv : bv 5). rewrite R19, lit64_small; [reflexivity | lia].
- change (12%bv : bv 5) with (nat_to_reg 12). rewrite G12, (den_off0 xv5 XR5). rewrite xv5_reg by lia. change (nat_to_reg 8) with (8%bv : bv 5). rewrite R8, lit64_small; [reflexivity | unfold MMAP_THRESHOLD in Hn; lia].
- change (13%bv : bv 5) with (nat_to_reg 13). rewrite G13, (denot_lit_U (EV xv5)). f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. unfold U.
rewrite (U_sext32 xv5), (U_off0 xv5 XR5). change (xv5 aCTR) with ctr. unfold c64. rewrite (zcanon_id 0), Z.add_0_r by (unfold M64; lia).
apply zcanon_id. unfold M64. apply sx32_range.
- change (18%bv : bv 5) with (nat_to_reg 18). rewrite G18, (den_off0 xv5 XR5). apply Z_to_bv_bv_unsigned.
- change (19%bv : bv 5) with (nat_to_reg 19). rewrite G19, (den_off0 xv5 XR5). apply Z_to_bv_bv_unsigned.
- change (20%bv : bv 5) with (nat_to_reg 20). rewrite G20, (den_off0 xv5 XR5). apply Z_to_bv_bv_unsigned.
- intros i Hi. rewrite (GS i Hi), (den_off0 xv5 XR5). rewrite xv5_reg by (pose proof (csaved_cases i Hi); lia). rewrite (RCS i Hi). apply Z_to_bv_bv_unsigned.
Qed.
Definition last : Z := am_last am.
Definition maplen : Z := am_maplen am.
Definition cls : Z := znth sc size_classes.
Lemma stride_eq : YN04.stride last maplen cls = stride_of am.
Proof.
unfold YN04.stride, YN04.mapped1, stride_of, last, maplen, cls, class_size. rewrite (proj1 Hsc).
destruct (am_maplen am =? 0), (am_last am =? 0); cbn [negb andb]; unfold UNIT; lia.
Qed.
Lemma start_eq : YN04.start Mb idx last maplen cls = P0.
Proof.
unfold YN04.start. rewrite stride_eq. pose proof geo as (kr & ko & GLO & ST & rgn & Emem & EGLO & EST & EP0 & EMb & _). lia.
Qed.
Lemma Z_land_255 x : Z.land x 255 = x mod 256.
Proof. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma c64_low : Z.land c64 255 = Z.land ctr 255.
Proof.
rewrite !Z_land_255. unfold c64.
rewrite <- (Z.mod_mod_divide (sx32 ctr) (2 ^ 32) 256) by (exists (2 ^ 24); reflexivity).
rewrite sx32_mod32. apply Z.mod_mod_divide. exists (2 ^ 24); reflexivity.
Qed.
Let MM : memrep B Lc Ac mc := mid_mem _ _ _ _ _ MID.
Let MMX : memrepX B [] Lc Ac mc := proj2 (memrepX_nil B Lc Ac mc) (mid_mem _ _ _ _ _ MID).
Lemma meta_cell c : In c (meta_slot_cells gm (Some (MUsed am))) -> cell_mem B Lc mc c.
Proof. intros Hc. exact (key_cell [] (Some (gm, idx)) U0 Lc Ac mc HI MMX gm (MUsed am) c Mg Hc). Qed.
Lemma bits_bytes : word_mem src0segs mc (G + 32) (bits_enc last sc maplen).
Proof.
pose proof (meta_cell (MCell (LMem (padd gm META_bits)) 8 (VZ (meta_bits am))) ltac:(cbn; auto 10)) as C.
unfold cell_mem in C. cbn [mc_loc mc_w mc_val sval_num] in C. rewrite loc_addr_padd_ in C. fold G in C.
intros k Hk. unfold META_bits in C. rewrite (meta_bits_enc am), (proj1 Hsc) in C. exact (C k Hk).
Qed.
Lemma mem_bytes : word_mem src0segs mc (G + 16) Mb.
Proof.
pose proof (meta_cell (MCell (LMem (padd gm META_mem)) 8 (VP (am_mem am))) ltac:(cbn; auto 10)) as C.
unfold cell_mem in C. cbn [mc_loc mc_w mc_val sval_num] in C. rewrite loc_addr_padd_ in C. fold G in C. unfold META_mem in C.
intros k Hk. exact (C k Hk).
Qed.
Lemma cls_bytes :
exists clo chi, mbyte src0segs mc (src0_D_size_classes + 2 * sc) = Some clo /\
mbyte src0segs mc (src0_D_size_classes + 2 * sc + 1) = Some chi /\
bv_unsigned clo + 256 * bv_unsigned chi = cls.
Proof.
destruct (so_size_classes _ (mid_syms _ _ _ _ _ MID) (Z.to_nat sc) ltac:(lia)) as (lo & hi & Hlo & Hhi & Hsum). rewrite Z2Nat.id in Hlo, Hhi by lia.
pose proof (st_tables _ _ (mid_statics _ _ _ _ _ MID)) as STB.
exists lo, hi. cbn [ms_segs ms_size_classes src0_msyms] in Hlo, Hhi, STB. unfold table_addr in STB. cbn [ms_debruijn ms_size_classes ms_small_cnt ms_med_cnt src0_msyms] in STB.
split; [|split].
- rewrite STB by (unfold src0_D_size_classes, src0_D_debruijn32, src0_D_small_cnt_tab, src0_D_med_cnt_tab; lia). exact Hlo.
- rewrite STB by (unfold src0_D_size_classes, src0_D_debruijn32, src0_D_small_cnt_tab, src0_D_med_cnt_tab; lia). exact Hhi.
- unfold cls, znth. rewrite <- Hsum. reflexivity.
Qed.
Lemma slot_present x : P0 - 4 <= x < P0 + stride_of am - IB -> present mc x.
Proof.
intros Hx. pose proof geo as (kr & ko & GLO & ST & rgn & Emem & EGLO & EST & EP0 & EMb & P1 & P2 & Hr & Hrk & Hrl & Hko & HfitR & R4096 & Rceil & Rimg & InR & _).
pose proof (proj1 (Forall_forall _ _) (proj2 (proj2 MM)) _ InR) as F. unfold foot_ok in F. cbn [fst snd loc_addr] in F.
apply F. unfold IB in Hx. lia.
Qed.
Lemma slot_chk_byte : mbyte src0segs mc (P0 - 4) = Some (Z_to_bv 8 0).
Proof.
destruct (image_upd_slot Ac gm am idx Mg Hidx) as (l1 & l2 & Eim & Hchk & _).
pose proof (memrep_cell B Lc Ac mc _ MM ltac:(rewrite Eim; apply in_app_iff; left; exact Hchk)) as C.
unfold cell_mem, slot_chk in C. cbn [mc_loc mc_w mc_val sval_num] in C. specialize (C 0%nat ltac:(lia)).
rewrite loc_addr_padd_, Z.add_0_r in C. fold P0 in C. replace (P0 + -4) with (P0 - 4) in C by lia. exact C.
Qed.
Ltac not_eclob :=
unfold YN04.eclob; let HH := fresh in intros HH;
repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end;
match goal with H : _ = _ |- _ => apply (f_equal bv_unsigned) in H; cbn in H; discriminate H end.
Section h.
Variables b3 b2lo b2hi : byte.
Hypothesis Hb3 : mbyte src0segs mc (P0 - 3) = Some b3.
Hypothesis Hb2lo : mbyte src0segs mc (P0 - 2) = Some b2lo.
Hypothesis Hb2hi : mbyte src0segs mc (P0 - 1) = Some b2hi.
Definition memF' : word -> option byte := YN04.memF mc Mb idx n c64 last maplen cls b3 b2lo b2hi.
Definition offM : Z := YN04.off n c64 last maplen cls b3 b2lo b2hi.
Definition off0M : Z := YN04.off0 c64 b3 b2lo b2hi.
Definition qM : Z := YN04.q Mb idx n c64 last maplen cls b3 b2lo b2hi.
Definition enf_final (rF : bvmap 5 word) : Prop :=
getr rF 10 = Z_to_bv 64 qM /\ getr rF 2 = Z_to_bv 64 SPv /\ getr rF 3 = getr regs 3 /\ getr rF 4 = Z_to_bv 64 TP /\
getr rF 8 = getr regs 8 /\ getr rF 9 = getr regs 9 /\ getr rF 18 = getr regs 18 /\ getr rF 19 = getr regs 19 /\ getr rF 20 = getr regs 20 /\
(forall i, In i CSAVED -> getr rF (nat_to_reg i) = getr regs (nat_to_reg i)).
Lemma enframe_hyps :
0 <= last < 32 /\ 0 <= sc < 64 /\ 0 <= maplen < 2 ^ 52 /\ (0 <= G /\ G + 40 <= 2 ^ 64) /\
0 <= c64 < 2 ^ 64 /\ 0 <= idx < 32 /\ (0 <= n /\ n + 4 <= YN04.stride last maplen cls) /\
(16 <= Mb /\ Mb + 16 + YN04.stride last maplen cls * idx + YN04.stride last maplen cls <= 2 ^ 63) /\
YN04.stride last maplen cls * idx + (YN04.stride last maplen cls - 4 - n) < 2 ^ 20 /\
mbyte src0segs mc (YN04.start Mb idx last maplen cls - 4) = Some (Z_to_bv 8 0) /\
mbyte src0segs mc (YN04.start Mb idx last maplen cls - 3) = Some b3 /\
mbyte src0segs mc (YN04.start Mb idx last maplen cls - 2) = Some b2lo /\
mbyte src0segs mc (YN04.start Mb idx last maplen cls - 1) = Some b2hi /\
(forall x, YN04.start Mb idx last maplen cls - 4 <= x < YN04.end_ Mb idx last maplen cls -> writable_at src0segs mc x) /\
(G + 24 <= YN04.start Mb idx last maplen cls - 4 \/ YN04.start Mb idx last maplen cls + YN04.stride last maplen cls <= G + 16).
Proof.
pose proof G_facts as (Glast & Glen & Sp & Hnone & Hal & Gml & Gext & Rctr & _).
pose proof geo as (kr & ko & GLO & ST & rgn & Emem & EGLO & EST & EP0 & EMb & P1 & P2 & Hr & Hrk & Hrl & Hko & HfitR & R4096 & Rceil & Rimg & InR & K1 & K2 & K3 & K4 & (a & Ha & Hfa & Ka1 & Ka2 & Kdisj)).
pose proof alloc_ceiling_lt as HCE. unfold YN04.end_. rewrite !start_eq, !stride_eq.
assert (Hml52 : maplen < 2 ^ 52).
{ unfold maplen. pose proof (inv_groups HI gm am Hu) as (_ & _ & _ & _ & Gmp & _).
destruct (Z_lt_dec 0 (am_maplen am)) as [Hpos|]; [|lia].
destruct (Gmp Hpos) as (r & rg' & Em' & Hr' & _ & Hl' & Hlen' & _).
destruct (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID) _ _ Hr' Hl') as (_ & A1 & A2 & _). unfold PGSZ in Hlen'. lia. }
split; [unfold last; lia|]. split; [lia|]. split; [unfold maplen in *; lia|]. split; [unfold G in *; lia|].
split; [unfold c64; apply sx32_range|]. split; [lia|]. split; [unfold IB in Hfit |- *; lia|].
split; [lia|]. split; [unfold IB; lia|].
split; [apply slot_chk_byte|]. split; [exact Hb3|]. split; [exact Hb2lo|]. split; [exact Hb2hi|].
split; [intros x Hx; apply present_writable; apply slot_present; unfold IB; lia|].
destruct Kdisj as [D|D]; [right | left]; destruct a; cbn [loc_addr] in *; unfold PGSZ in *; lia.
Qed.
Lemma MACH (Phi : config -> Prop) :
(forall rF, enf_final rF -> Phi (mkCfg (mkst rF (getr regs 1) memF' rom) mdc)) ->
SR src0segs (mkCfg (mkst rg (Z_to_bv 64 PC) mc rom) mdc) Phi.
Proof.
intros HPhi. destruct Hmdc as (Hh & Hlz & _). pose proof PRE_facts as (_ & _ & _ & Hret & _).
eapply SR_bind; [exact (T5_run _ _ mdc T5_st_ok Hh Hlz)|].
intros c' (ms1 & -> & HS1 & HF1). destruct (T5_post ms1 HS1 HF1) as [SH E5]. rewrite SH.
pose proof enframe_hyps as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Yc4 & Yb3 & Yb2 & Yb1 & YW & YD).
destruct cls_bytes as (clo & chi & C1 & C2 & C3).
destruct (enframe_steps mc rom G Mb idx n c64 last sc maplen cls clo chi b3 b2lo b2hi
Y1 Y2 Y3 Y4 bits_bytes mem_bytes (fun _ => conj (proj2 (proj2 Hsc)) (conj C1 (conj C2 C3)))
Y5 Y6 Y7 Y8 Y9 Yc4 Yb3 Yb2 Yb1 YW YD
(ms_regs ms1) (e5_10 _ E5) (e5_11 _ E5) (e5_12 _ E5) (e5_13 _ E5)) as (rF & MS & A10 & KEEP).
rewrite (e5_1 _ E5) in MS. unfold YK0s.ret_ok in Hret. rewrite Hret in MS.
eapply SR_msteps; [exact Hh | exact Hlz | exact MS |]. apply SR_ret. apply HPhi.
assert (KP : forall r : reg, ~ YN04.eclob r -> getr rF r = getr (ms_regs ms1) r) by exact KEEP.
unfold enf_final. split; [exact A10|].
split; [rewrite KP by not_eclob; apply (e5_2 _ E5)|].
split; [rewrite KP by not_eclob; apply (e5_cs _ E5 3%nat); cbn; auto|].
split; [rewrite KP by not_eclob; apply (e5_4 _ E5)|].
split; [rewrite KP by not_eclob; apply (e5_8 _ E5)|].
split; [rewrite KP by not_eclob; apply (e5_9 _ E5)|].
split; [rewrite KP by not_eclob; apply (e5_18 _ E5)|].
split; [rewrite KP by not_eclob; apply (e5_19 _ E5)|].
split; [rewrite KP by not_eclob; apply (e5_20 _ E5)|].
intros i Hi. pose proof (csaved_cases i Hi) as C.
rewrite KP by (decompose [or] C; subst i; cbn; not_eclob). apply (e5_cs _ E5 i Hi).
Qed.
Definition slackm : Z := (stride_of am - IB - n) / UNIT.
Lemma enf_model :
YN04.slack n last maplen cls = slackm /\
offM = fold_off slackm off0M /\ 0 <= off0M < 256 /\
0 <= offM <= 255 /\ 16 * offM + n + 4 <= stride_of am /\
qM = P0 + 16 * offM /\
YN04.end_ Mb idx last maplen cls = P0 + stride_of am - 4 /\
YN04.reserved n c64 last maplen cls b3 b2lo b2hi = stride_of am - 4 - 16 * offM - n /\
YN04.code n c64 last maplen cls b3 b2lo b2hi =
(if 5 <=? stride_of am - 4 - 16 * offM - n then 5 else stride_of am - 4 - 16 * offM - n) /\
YN04.hdr16v idx n c64 last maplen cls b3 b2lo b2hi = stride_of am * idx / 16 + offM.
Proof.
pose proof enframe_hyps as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & _).
pose proof (geom_facts Mb idx n c64 last maplen cls b3 b2lo b2hi Y5 Y6 Y7 Y8 Y9) as (Go & Gs & Gq & Ge & Gr & Gqe & Gsl).
pose proof (basic_facts Mb idx n c64 last maplen cls b3 b2lo b2hi Y5 Y6 Y7 Y8) as (_ & _ & _ & _ & _ & _ & Ho0 & _).
rewrite stride_eq, start_eq in *.
assert (SL : YN04.slack n last maplen cls = slackm) by (unfold YN04.slack, slackm; rewrite stride_eq; unfold IB, UNIT; reflexivity).
split; [exact SL|]. split; [unfold offM, YN04.off; rewrite SL; reflexivity|]. split; [exact Ho0|].
split; [exact Go|]. split; [exact Gs|]. split; [exact Gq|]. split; [exact Ge|].
split; [unfold YN04.reserved; rewrite stride_eq; reflexivity|].
split; [unfold YN04.code, YN04.reserved; rewrite stride_eq; reflexivity|].
unfold YN04.hdr16v. rewrite stride_eq. reflexivity.
Qed.
Definition rsvdM : Z := stride_of am - IB - UNIT * offM - n.
Definition rsvM : Z := if 5 <=? rsvdM then 5 else rsvdM.
Definition hdrM : Z * Z := if offM =? 0 then (idx + rsvM * 32, stride_of am * idx / UNIT) else (224, offM).
Definition frM : frame := mkFrame offM n FUser.
Definition am1M : ameta := upd_slot am idx (mkSlot (Some hdrM) (Some frM)).
Definition A1M : astate := upd_meta gm (MUsed am1M) Ac.
Definition pM : sptr := padd (slot_start am idx) (UNIT * offM).
Lemma pure_eq o0 : fold_off slackm o0 = offM -> enframe_pure am gm idx n FUser o0 Ac = (pM, A1M).
Proof.
intros Ho. unfold enframe_pure. cbv zeta. change ((stride_of am - IB - n) / UNIT) with slackm. rewrite Ho.
unfold pM, A1M, am1M, hdrM, frM, rsvM, rsvdM. reflexivity.
Qed.
Lemma ptr_pM : ptr_addr Lc pM = qM.
Proof.
pose proof enf_model as (_ & _ & _ & _ & _ & Gq & _). unfold pM. rewrite ptr_addr_padd_. fold P0. unfold UNIT. lia.
Qed.
Lemma blocks_A1M : malloc_post [] U0 A n (Some pM, A1M) ->
WF A1M /\ exists l1 l2, user_blocks A1M = l1 ++ (pM, n) :: l2 /\ user_blocks A = l1 ++ l2.
Proof.
intros [HI1 MP]. cbn [fst snd] in HI1, MP. destruct MP as (g' & am' & idx' & off' & _ & (l1 & l2 & E1 & E2)).
pose proof PRE_facts as (_ & HW & _).
split; [exact HI1|]. exists (map fst l1), (map fst l2).
rewrite (user_blocks_ublist A1M (proj1 (inv_keys HI1))), (user_blocks_ublist A (proj1 (inv_keys HW))), E1, E2, !map_app. cbn [map fst]. auto.
Qed.
Lemma user_blocks_Ac : user_blocks Ac = user_blocks A.
Proof.
pose proof PRE_facts as (_ & HW & _).
rewrite (user_blocks_ublist Ac (proj1 (inv_keys HI))), (user_blocks_ublist A (proj1 (inv_keys HW))). rewrite (ub_same_ublist _ _ UB). reflexivity.
Qed.
Lemma leaf_ok rF : enf_final rF -> malloc_post [] U0 A n (Some pM, A1M) ->
malloc_leaf B (MRx B) L A regs mem md n (Some pM, A1M) (mkCfg (mkst rF (getr regs 1) memF' rom) mdc).
Proof.
intros (F10 & F2 & F3 & F4 & F8 & F9 & F18 & F19 & F20 & FCS) MP.
destruct (blocks_A1M MP) as (HW1 & ub1 & ub2 & UB1 & UB2).
pose proof PRE_facts as (MX & HW & HB & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herr & _). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof G_facts as (Glast & Glen & Sp & Hnone & Hal' & Gml & Gext & Rctr & _).
pose proof geo as (kr & ko & GLO & ST & rgn & Emem & EGLO & EST & EP0 & EMb & P1 & P2 & Hr & Hrk & Hrl & Hko & HfitR & R4096 & Rceil & Rimg & InR & K1 & K2 & K3 & K4 & _).
pose proof enframe_hyps as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Yc4 & _).
pose proof enf_model as (Esl & Eoff & Ro0 & Ro & Gs & Gq & Ge & Gr & Gc & Gh).
pose proof (upd_slot_fields am idx (mkSlot (Some hdrM) (Some frM))) as (_ & _ & _ & _ & Fst & _). fold am1M in Fst.
pose proof (memF_frame mc Mb idx n c64 last sc maplen cls b3 b2lo b2hi Y1 Y2 Y3 Y5 Y6 Y7 Y8 Y9) as MFR.
pose proof (memF_present mc Mb idx n c64 last sc maplen cls b3 b2lo b2hi Y1 Y2 Y3 Y5 Y6 Y7 Y8 Y9) as MPR.
pose proof (memF_writable mc Mb idx n c64 last sc maplen cls b3 b2lo b2hi Y1 Y2 Y3 Y5 Y6 Y7 Y8 Y9) as MWR.
pose proof (memF_hdr mc Mb idx n c64 last sc maplen cls b3 b2lo b2hi Y1 Y2 Y3 Y5 Y6 Y7 Y8 Y9 Yc4) as MHD.
pose proof (memF_tail mc Mb idx n c64 last sc maplen cls b3 b2lo b2hi Y1 Y2 Y3 Y5 Y6 Y7 Y8 Y9) as MTL.
fold memF' in MFR, MPR, MWR, MHD, MTL. unfold written in MFR.
rewrite ?start_eq, ?Ge in MFR. rewrite ?start_eq, ?Ge in MHD. rewrite ?start_eq, ?Ge in MTL.
fold qM in MFR. fold qM in MHD. fold qM in MTL. fold offM in MHD. rewrite ?Gr, ?Gc, ?Gh in MHD. rewrite ?Gr, ?Gc, ?Gh in MTL.
change (ms_segs B) with src0segs in *.
assert (MX1 : MRx B Lc A1M memF' mdc).
{ apply (MRx_enframe B Lc Ac mc mdc U0 gm am idx offM n hdrM memF' MID HI Hu Hidx HW1).
- unfold UNIT, IB in *. lia.
- unfold YN30.am1, YN30.fr1. fold frM. fold am1M.
unfold hdr_byte3, hdr_off16, rsv_code. cbn [fr_kind fr_off fr_n frM]. rewrite Fst.
unfold hdrM, rsvM, rsvdM. destruct (offM =? 0) eqn:Eo; [|reflexivity].
apply Z.eqb_eq in Eo. rewrite Eo. f_equal; [lia | unfold UNIT; lia].
- intros x Hx Hnw. apply MFR; [exact Hx|]. clear - Hnw Gq.
unfold YN30.Q, YN30.E in Hnw. unfold YN30.P0 in Hnw. unfold P0 in *. unfold UNIT, IB in *. lia.
- exact MPR.
- unfold YN30.Q. unfold YN30.P0. fold P0. replace (P0 + UNIT * offM) with qM by (rewrite Gq; unfold UNIT; lia).
destruct MHD as (H1 & H2 & H3 & H4 & H5 & H6).
unfold YN30.am1, YN30.fr1. fold frM. fold am1M.
assert (E3 : hdr_byte3 am1M idx frM = idx + 32 * (if 5 <=? stride_of am - 4 - 16 * offM - n then 5 else stride_of am - 4 - 16 * offM - n)).
{ unfold hdr_byte3, rsv_code. cbn [fr_kind fr_off fr_n frM]. rewrite Fst. unfold IB, UNIT. reflexivity. }
assert (E16 : hdr_off16 am1M idx frM = stride_of am * idx / 16 + offM).
{ unfold hdr_off16. cbn [fr_off frM]. rewrite Fst. unfold UNIT. reflexivity. }
rewrite E3, E16. change (ms_segs B) with src0segs.
split; [exact H1|]. split; [|split; [|split; [exact H4 | split; [exact H5 | exact H6]]]].
+ rewrite H2. unfold hdrM, rsvM, rsvdM. destruct (offM =? 0); cbn [fst]; [|reflexivity]. unfold IB, UNIT. do 2 f_equal. lia.
+ intros k Hk. rewrite (H3 k Hk). unfold hdrM. destruct (offM =? 0) eqn:Eo; cbn [snd]; [|reflexivity].
apply Z.eqb_eq in Eo. rewrite Eo, Z.add_0_r. unfold UNIT. reflexivity.
- unfold YN30.rsv, YN30.Q, YN30.E. unfold YN30.P0, YN30.am1, YN30.fr1. fold P0. fold frM. fold am1M.
replace (P0 + UNIT * offM) with qM by (rewrite Gq; unfold UNIT; lia).
assert (ER : reserved_of am1M frM = stride_of am - 4 - 16 * offM - n).
{ unfold reserved_of. cbn [fr_off fr_n frM]. rewrite Fst. unfold IB, UNIT. lia. }
rewrite ER. replace (P0 + stride_of am - IB) with (P0 + stride_of am - 4) by (unfold IB; lia). exact MTL.
- exact HBc. - exact HRc. - exact HAc. - exact HSc. - lia. }
pose proof ptr_pM as Hq.
assert (WREG' : forall x, P0 - 4 <= x < P0 + stride_of am - 4 -> GLO <= x < GLO + rg_len rgn).
{ intros x Hx. clear - Hx EP0 P1 P2 Hko HfitR EST. lia. }
assert (WREG : forall x, (P0 - 4 <= x < P0 \/ qM - 4 <= x < qM \/ qM + n <= x < P0 + stride_of am - 4) -> GLO <= x < GLO + rg_len rgn).
{ intros x Hx. apply WREG'. clear - Hx Gq Ro Gs Hn. lia. }
assert (WGUARD : forall x, (alloc_ceiling <= x < 2 ^ 64 \/ in_img B x) ->
~ (P0 - 4 <= x < P0 \/ qM - 4 <= x < qM \/ qM + n <= x < P0 + stride_of am - 4)).
{ intros x Hgx Hw. pose proof (WREG x Hw) as Wx. destruct Hgx as [Hgx|Hgx]; [lia | exact (Rimg x Wx Hgx)]. }
assert (OWN : forall x, owned B Lc Ac x -> ~ owned B Lc A1M x -> qM <= x < qM + n).
{ intros x Ho Hno. destruct Ho as [[Hfp Hnb] | Hs]; [| exfalso; apply Hno; right; exact Hs].
destruct (Z_le_dec qM x) as [L1|L1]; [destruct (Z_lt_dec x (qM + n)) as [L2|L2]; [lia|]|]; exfalso; apply Hno; left; split;
try (unfold in_footprint in *; unfold A1M; rewrite footprint_upd_meta; exact Hfp);
intros (b & Hb & Hxb); apply Hnb; exists b; rewrite UB1 in Hb; rewrite user_blocks_Ac, UB2;
apply in_app_iff in Hb; (destruct Hb as [Hb | [<- | Hb]]; [split; [apply in_app_iff; left; exact Hb | exact Hxb]
| exfalso; cbn [fst snd] in Hxb; change (loc_addr Lc (LMem pM)) with (ptr_addr Lc pM) in Hxb; rewrite Hq in Hxb; lia
| split; [apply in_app_iff; right; exact Hb | exact Hxb]]). }
unfold malloc_leaf. exists Lc, rF, memF', mdc. split; [reflexivity|]. split.
+
unfold call_post. change (ms_segs B) with src0segs.
split; [exact MX1|]. split; [exact HW1|]. split; [unfold A1M; apply (proj2 (bounded_upd_meta _ _ _)); exact HBc|]. split; [exact LE|].
split.
{ intros p k Hin _. destruct (block_region A p k HW Hin) as (kk & o & rg' & -> & Hr' & _). unfold ptr_addr. cbn [loc_addr].
destruct LE as (_ & _ & _ & LR). rewrite (LR kk (region_of_lt A kk rg' Hr')). reflexivity. }
split.
{ intros r Hcr. unfold callee_saved in Hcr.
assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear Hcr. decompose [or] C; subst r;
first [ exact (eq_trans F2 (Z_to_bv_bv_unsigned 64 (getr regs 2%bv)))
| exact F3 | exact (eq_trans F4 (eq_sym Htp)) | exact F8 | exact F9 | exact F18 | exact F19 | exact F20
| exact (FCS 21%nat ltac:(cbn; auto 10)) | exact (FCS 22%nat ltac:(cbn; auto 10)) | exact (FCS 23%nat ltac:(cbn; auto 10))
| exact (FCS 24%nat ltac:(cbn; auto 10)) | exact (FCS 25%nat ltac:(cbn; auto 10)) | exact (FCS 26%nat ltac:(cbn; auto 10)) | exact (FCS 27%nat ltac:(cbn; auto 10)) ]. }
split; [exact VM|].
split.
{ intros a Hg HnA HnA1 Hns _.
assert (Ha64 : 0 <= a < 2 ^ 64) by (destruct Hg as [Hg|Hg]; [lia | pose proof (src0_img_range' a Hg); lia]).
assert (E1 : memF' (Z_to_bv 64 a) = mc (Z_to_bv 64 a)) by (apply MFR; [exact Ha64 | exact (WGUARD a Hg)]).
assert (NOAc : ~ owned B Lc Ac a).
{ intros Ho. pose proof (OWN a Ho HnA1) as Hin. pose proof (WREG' a ltac:(clear - Hin Gq Ro Gs Hn; lia)) as Wa.
destruct Hg as [Hg|Hg]; [clear - Wa Hg Rceil; lia | exact (Rimg a Wa Hg)]. }
assert (NNM : ~ in_nonmap_region Lc Ac a).
{ intros [(r & rg' & Hr' & Hl' & _ & Hx') _]. destruct (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID) r rg' Hr' Hl') as (_ & _ & Rc' & Ri').
destruct Hg as [Hg|Hg]; [clear - Hx' Rc' Hg; lia | exact (Ri' a Hx' Hg)]. }
assert (E2 : mc (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) by (apply OUT; assumption).
unfold mbyte, writable_at, wview. rewrite E1, E2. tauto. }
split.
{ intros p k i Hin Hin1 Hi.
pose proof (mr_blocks _ _ (MRx_laws B) L A mem md p k i MX Hin Hi) as (Pp & Plo & Phi & Pno).
assert (HinC : In (p, k) (user_blocks Ac)) by (rewrite user_blocks_Ac; exact Hin).
assert (EP : ptr_addr Lc p = ptr_addr L p).
{ destruct (block_region A p k HW Hin) as (kk & o & rg' & -> & Hr' & _). unfold ptr_addr. cbn [loc_addr].
destruct LE as (_ & _ & _ & LR). rewrite (LR kk (region_of_lt A kk rg' Hr')). reflexivity. }
assert (NW : ~ (P0 - 4 <= ptr_addr L p + i < P0 \/ qM - 4 <= ptr_addr L p + i < qM \/ qM + n <= ptr_addr L p + i < P0 + stride_of am - 4)).
{ intros Hw.
pose proof (slot_body_no_block [] (Some (gm, idx)) U0 Ac Lc HI (mid_layout _ _ _ _ _ MID) gm am idx (poff (slot_start am idx)) (poff (slot_start am idx) + stride_of am - IB)
Hu Hidx ltac:(intros f Hf; rewrite Hnone in Hf; discriminate Hf) (no_child_at_frameless [] (Some (gm, idx)) U0 Ac gm am idx HI Hu Hidx Hnone)
ltac:(lia) ltac:(lia) (p, k) HinC) as D1.
unfold YO0f.ranges_disjoint, block_range in D1. cbn [fst snd] in D1. change (loc_addr Lc (LMem p)) with (ptr_addr Lc p) in D1. rewrite EP in D1.
rewrite Emem in D1. cbn [prid] in D1. unfold slot_start in D1. rewrite Emem in D1. cbn [padd poff] in D1.
destruct (slot_start_cells A1M gm am1M idx HW1 ltac:(apply (used_metas_usedX A1M gm am1M HW1); unfold A1M; apply usedX_upd; left; pose proof (usedX_MT _ _ _ _ Hu) as [_ NX]; auto)
ltac:(pose proof (upd_slot_fields am idx (mkSlot (Some hdrM) (Some frM))) as (_ & Fl & _); fold am1M in Fl; rewrite Fl; exact Hidx)) as [C4 Chdr].
assert (SL1 : nth_slot am1M idx = mkSlot (Some hdrM) (Some frM)).
{ unfold am1M. rewrite nth_slot_upd_slot by (try lia; rewrite Glen; lia). rewrite Z.eqb_refl. reflexivity. }
rewrite SL1 in Chdr. cbn [ss_hdr] in Chdr. destruct hdrM as [h3 h16] eqn:Eh in Chdr. destruct Chdr as [C3 C16].
assert (HinB1 : In (p, k) (user_blocks A1M)) by (rewrite UB1; rewrite UB2 in Hin; apply in_app_iff in Hin as [Hb|Hb]; apply in_app_iff; [left; exact Hb | right; right; exact Hb]).
pose proof (upd_slot_fields am idx (mkSlot (Some hdrM) (Some frM))) as (_ & _ & _ & _ & _ & _ & Fss). fold am1M in Fss.
pose proof (image_outside_user_blocks A1M Lc _ _ HW1 (proj2 (layout_ok_upd_meta Lc gm _ Ac) (mid_layout _ _ _ _ _ MID)) C4 HinB1) as D4.
pose proof (image_outside_user_blocks A1M Lc _ _ HW1 (proj2 (layout_ok_upd_meta Lc gm _ Ac) (mid_layout _ _ _ _ _ MID)) C3 HinB1) as D3.
pose proof (image_outside_user_blocks A1M Lc _ _ HW1 (proj2 (layout_ok_upd_meta Lc gm _ Ac) (mid_layout _ _ _ _ _ MID)) C16 HinB1) as D16.
unfold YO0f.ranges_disjoint, cell_range, block_range in D4, D3, D16. cbn [fst snd mc_loc mc_w] in D4, D3, D16.
change (loc_addr Lc (LMem p)) with (ptr_addr Lc p) in D4, D3, D16.
rewrite !Fss, !loc_addr_padd_ in D4, D3, D16. fold P0 in D4, D3, D16. rewrite EP in D4, D3, D16.
clear - Hw D1 D4 D3 D16 Hi EP0 EGLO P1 P2 Hko Gq Ro Gs EST Sp Hn. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *.
unfold IB, UNIT in *. lia. }
assert (E1 : memF' (Z_to_bv 64 (ptr_addr L p + i)) = mc (Z_to_bv 64 (ptr_addr L p + i))) by (apply MFR; [lia | exact NW]).
assert (NIMG : ~ in_img B (ptr_addr L p + i)).
{ destruct (block_region A p k HW Hin) as (kk & o & rg' & Ep & Hr' & _ & Hl' & Ho' & Hk' & Hlen' & _).
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ (MRx_MRc _ _ _ _ _ MX)) kk rg' Hr' Hl') as (_ & _ & _ & Himg).
apply Himg. rewrite Ep. unfold ptr_addr. cbn [loc_addr]. lia. }
assert (NOAc : ~ owned B Lc Ac (ptr_addr L p + i)).
{ intros [[_ Hnb] | Hs].
- apply Hnb. exists (p, k). split; [exact HinC|]. cbn [fst snd]. change (loc_addr Lc (LMem p)) with (ptr_addr Lc p). rewrite EP. lia.
- apply NIMG. apply (so_statics_img _ (mid_syms _ _ _ _ _ MID)). exact Hs. }
assert (E2 : mc (Z_to_bv 64 (ptr_addr L p + i)) = mem (Z_to_bv 64 (ptr_addr L p + i))).
{ apply OUT; [lia | exact Pno | exact NOAc | |].
-
intros [_ NM]. apply NM. assert (HinB1 : In (p, k) (user_blocks A1M)) by (rewrite UB1; rewrite UB2 in Hin; apply in_app_iff in Hin as [Hb|Hb]; apply in_app_iff; [left; exact Hb | right; right; exact Hb]).
destruct (block_region A1M p k HW1 HinB1) as (kk & o & rg' & Ep & Hr' & Hk' & Hl' & Ho' & Hn' & Hlen' & _).
exists kk, rg'. split; [unfold A1M in Hr'; unfold region_of in *; cbn in Hr'; exact Hr'|]. split; [exact Hl'|]. split; [exact Hk'|].
rewrite <- EP. rewrite Ep. unfold ptr_addr. cbn [loc_addr]. lia.
- unfold scratch, ALLOC_STACK. fold SPv. intros [Hs|Hs]; [lia|]. apply NIMG. apply errno_img'. exact Hs. }
unfold mbyte. rewrite E1, E2. reflexivity. }
intros a Hs. apply MWR. apply WSCR. exact Hs.
+
cbn [fst snd]. change (ms_segs B) with src0segs. split; [rewrite Hq; exact F10|]. split; [rewrite Hq; lia|]. split; [exists ub1, ub2; auto|].
intros AZ i Hi.
assert (US : stride_of am < class_size sc).
{ unfold allzero_block in AZ.
pose proof (upd_slot_fields am idx (mkSlot (Some hdrM) (Some frM))) as (_ & Fl & Fsc & _ & Fst' & _ & Fss). fold am1M in Fl, Fsc, Fst', Fss.
assert (Hu1 : usedX [] A1M gm am1M) by (unfold A1M; apply usedX_upd; left; pose proof (usedX_MT _ _ _ _ Hu) as [_ NX]; auto).
assert (SL1 : nth_slot am1M idx = mkSlot (Some hdrM) (Some frM)).
{ unfold am1M. rewrite nth_slot_upd_slot by (try lia; rewrite Glen; lia). rewrite Z.eqb_refl. reflexivity. }
pose proof (get_meta_ok A1M gm am1M idx frM HW1 (frames_intro A1M gm am1M idx frM HW1 (proj1 (usedX_MT _ _ _ _ Hu1)) ltac:(rewrite Fl; exact Hidx) ltac:(rewrite SL1; reflexivity))) as GM.
cbn zeta in GM. destruct GM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hff).
assert (Efp : frame_ptr am1M idx frM = pM) by (unfold frame_ptr, pM; rewrite Fss; reflexivity).
rewrite Efp in Hff. rewrite Hff in AZ. change (mlookup (st_metas A1M) gm) with (MT A1M gm) in AZ. unfold A1M in AZ. rewrite MT_upd_same in AZ.
rewrite Fsc, Fst', (proj1 Hsc) in AZ. replace (48 <=? sc) with false in AZ by (symmetry; apply Z.leb_gt; lia). cbn [orb] in AZ.
apply Z.ltb_lt in AZ. exact AZ. }
assert (NW : ~ (P0 - 4 <= qM + i < P0 \/ qM - 4 <= qM + i < qM \/ qM + n <= qM + i < P0 + stride_of am - 4)) by (clear - Hi Gq Ro Gs; lia).
assert (E1 : memF' (Z_to_bv 64 (qM + i)) = mc (Z_to_bv 64 (qM + i))).
{ apply MFR; [| exact NW]. pose proof (WREG (P0 - 4) ltac:(lia)). clear - Hi Gq Ro Gs H Rceil R4096 HfitR EP0 P1 P2 Hko EST. pose proof alloc_ceiling_lt. lia. }
rewrite Hq. unfold mbyte. rewrite E1. fold (mbyte src0segs mc (qM + i)).
rewrite Gq. replace (P0 + 16 * offM + i) with (P0 + (16 * offM + i)) by lia. apply (ZERO US). unfold IB. clear - Hi Ro Gs. lia.
Qed.
End h.
Theorem succ_tail :
mreal src0segs (mkCfg (mkst rg (Z_to_bv 64 PC) mc rom) mdc)
(ibind (enframe gm idx n ctr FUser Ac) (fun ps => IRet (Some (fst ps), snd ps)))
(fun r c' => malloc_post [] U0 A n r -> malloc_leaf B (MRx B) L A regs mem md n r c').
Proof.
pose proof G_facts as (Glast & Glen & Sp & Hnone & Hal & Gml & Gext & Rctr & Shdr0 & Shdr).
pose proof geo as (kr & ko & GLO & ST & rgn & Emem & EGLO & EST & EP0 & _).
destruct (slot_present (P0 - 3) ltac:(unfold IB; lia)) as [b3 Hb3'].
destruct (slot_present (P0 - 2) ltac:(unfold IB; lia)) as [b2lo Hb2lo'].
destruct (slot_present (P0 - 1) ltac:(unfold IB; lia)) as [b2hi Hb2hi'].
assert (Hb3 : mbyte src0segs mc (P0 - 3) = Some b3) by (unfold mbyte; rewrite Hb3'; reflexivity).
assert (Hb2lo : mbyte src0segs mc (P0 - 2) = Some b2lo) by (unfold mbyte; rewrite Hb2lo'; reflexivity).
assert (Hb2hi : mbyte src0segs mc (P0 - 1) = Some b2hi) by (unfold mbyte; rewrite Hb2hi'; reflexivity).
pose proof (enf_model b3 b2lo b2hi Hb3 Hb2lo Hb2hi) as (Esl & Eoff & Ro0 & Ro & Gs & Gq & _).
assert (SL : YN04.slack n last maplen cls = slackm) by exact Esl.
assert (Hsl0 : 0 <= slackm) by (unfold slackm; apply Z.div_pos; unfold IB, UNIT in *; lia).
assert (FIN : forall o0, fold_off slackm o0 = offM b3 b2lo b2hi ->
mreal src0segs (mkCfg (mkst rg (Z_to_bv 64 PC) mc rom) mdc)
(ibind (IRet (enframe_pure am gm idx n FUser o0 Ac)) (fun ps => IRet (Some (fst ps), snd ps)))
(fun r c' => malloc_post [] U0 A n r -> malloc_leaf B (MRx B) L A regs mem md n r c')).
{ intros o0 Ho0. rewrite (pure_eq b3 b2lo b2hi o0 Ho0). cbn [ibind mreal fst snd].
apply (MACH b3 b2lo b2hi Hb3 Hb2lo Hb2hi). intros rF HF MP. exact (leaf_ok b3 b2lo b2hi Hb3 Hb2lo Hb2hi rF HF MP). }
destruct (Z.eq_dec slackm 0) as [Sz | Snz].
-
rewrite (enframe_eval0 Ac gm am idx n ctr FUser Mg Hidx Sz). apply FIN.
rewrite Eoff, Sz, !fold_off_0' by lia. reflexivity.
- destruct (ss_hdr (nth_slot am idx)) as [[h3 h16]|] eqn:Ehdr.
+
destruct (image_upd_slot Ac gm am idx Mg Hidx) as (l1 & l2 & Eim & _).
assert (C3 : In (MCell (LMem (padd (slot_start am idx) (-3))) 1 (VZ h3)) (image Ac)).
{ rewrite Eim. apply in_app_iff. right. apply in_app_iff. left. unfold slot_rest. rewrite Ehdr. apply in_app_iff. left. left. reflexivity. }
assert (C16 : In (MCell (LMem (padd (slot_start am idx) (-2))) 2 (VZ h16)) (image Ac)).
{ rewrite Eim. apply in_app_iff. right. apply in_app_iff. left. unfold slot_rest. rewrite Ehdr. apply in_app_iff. left. right. left. reflexivity. }
pose proof (memrep_cell B Lc Ac mc _ MM C3) as B3. pose proof (memrep_cell B Lc Ac mc _ MM C16) as B16.
unfold cell_mem in B3, B16. cbn [mc_loc mc_w mc_val sval_num] in B3, B16. rewrite loc_addr_padd_ in B3, B16. fold P0 in B3, B16.
change (ms_segs B) with src0segs in B3, B16.
destruct (Shdr h3 h16 eq_refl) as [R3 R16].
assert (E3 : bv_unsigned b3 = h3).
{ specialize (B3 0%nat ltac:(lia)). rewrite Z.add_0_r in B3. replace (P0 + -3) with (P0 - 3) in B3 by lia. rewrite Hb3 in B3. injection B3 as ->.
rewrite le_byte_1_0 by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia. }
assert (E16 : bv_unsigned b2lo + 256 * bv_unsigned b2hi = h16).
{ pose proof (B16 0%nat ltac:(lia)) as X0. pose proof (B16 1%nat ltac:(lia)) as X1.
rewrite Z.add_0_r in X0. replace (P0 + -2) with (P0 - 2) in X0 by lia. rewrite Hb2lo in X0. injection X0 as ->.
replace (P0 + -2 + Z.of_nat 1) with (P0 - 1) in X1 by lia. rewrite Hb2hi in X1. injection X1 as ->.
unfold le_byte. change (2 ^ (8 * Z.of_nat 2)) with 65536. change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8.
rewrite Z.shiftr_0_r, (Z.mod_small h16 65536) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite !(Z.mod_mod _ 256) by lia.
rewrite (Z.mod_small (h16 / 256) 256) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
pose proof (Z.div_mod h16 256 ltac:(lia)). lia. }
unshelve erewrite (enframe_eval Ac gm am idx n ctr FUser h3 h16 Mg Hidx Ehdr _).
{ cbv zeta. apply fold_off_ok; [exact Hsl0|]. fold slackm. replace (slackm =? 0) with false by (symmetry; apply Z.eqb_neq; exact Snz).
change 256 with (2 ^ 8). apply land_range_r; [|lia]. destruct (h3 =? 0); lia. }
apply FIN. fold slackm. replace (slackm =? 0) with false by (symmetry; apply Z.eqb_neq; exact Snz).
rewrite Eoff. f_equal. unfold off0M, YN04.off0, YN04.off0src, YN04.h3, YN04.h16. rewrite E3, E16.
destruct (h3 =? 0); [exact (eq_sym c64_low) | reflexivity].
+
rewrite (enframe_eval_junk Ac gm am idx n ctr FUser Mg Hidx Ehdr Hsl0 Snz). cbn [ibind mreal].
apply (MACH b3 b2lo b2hi Hb3 Hb2lo Hb2hi). intros rF HF. cbn [knode].
exists (off0M b3 b2lo b2hi). split; [exact Ro0|]. fold slackm.
rewrite (Z.mod_small _ 256) by exact Ro0.
replace (fold_off slackm (off0M b3 b2lo b2hi) <=? slackm) with true by (symmetry; apply Z.leb_le; apply fold_off_ok; [exact Hsl0 | exact Ro0]).
rewrite (pure_eq b3 b2lo b2hi (off0M b3 b2lo b2hi) (eq_sym Eoff)). cbn [ibind mreal fst snd].
apply SR_ret. intros MP. exact (leaf_ok b3 b2lo b2hi Hb3 Hb2lo Hb2hi rF HF MP).
Qed.
End e.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
