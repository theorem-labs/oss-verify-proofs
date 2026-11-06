(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 317 of its 339 lines of code are new or changed and 496 lines of the source are left out. *)
(* Helpers of segment S3 of the ASan image-A walk of reac_segconf_declared (fuzz_segconf.asan, interface
   reac_segconf_declared_d.v), part a: the plumbing over readers, the model facts that put the footprint of the
   call of reac_declared_vlan_add inside the walk's own footprint, where that footprint lies, and the shadow of
   the caller's real stack. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI67 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0t.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa SegPaLib PaCall PaDenot PaSB
PaNoChain PaCallRun PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegBase SegObj SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
reac_declared_vlan_split_c reac_declared_vlan_add_c reac_segconf_declared_c reac_segconf_declared_d
reac_segconf_declared_lem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the return point of the call of reac_declared_vlan_add at 0x89a14 *)
Definition DC_RET : Z := AF_reac_segconf_declared + 0x1c4.

(* ======================= plumbing over readers and memories ======================= *)
Lemma dcs3_val_mem : forall segs H mem a (n : nat) v,
(forall k, (k < n)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v n k)) ->
val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. pose proof (Hv k Hk) as Hb. unfold aview in Hb. unfold val_mem.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb;
  cbn [option_map] in Hb; [|discriminate Hb].
injection Hb as Hb. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned, Hb. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
cbv [YO0f.le_byte YG0f.le_byte]. symmetry. apply Z.mod_mod. lia.
Qed.

Lemma dcs3_aview_ext : forall segs H (m m' : word -> option byte), (forall x, m' x = m x) ->
forall a, aview segs H m' a = aview segs H m a.
Proof. intros segs H m m' He a. unfold aview, mbyte, mrestrict. cbv beta. rewrite (He (Z_to_bv 64 a)). reflexivity. Qed.

Lemma dcs3_frame_ro : forall E rs (m m' : word -> option byte),
Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> frame_of E rs m m' -> forall x, m' x = m x.
Proof.
intros E rs m m' Hro H x. apply H. intros (r & Hr & Ha).
pose proof (proj1 (Forall_forall _ _) Hro r Hr) as Hw. cbn beta in Hw. lia.
Qed.

Lemma dcs3_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
getr regs' r = getr regs r.
Proof. intros regs regs' r H Hr. pose proof (H _ Hr) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. Qed.

Lemma dcs3_set_fs_set_fs : forall f f' (S : astate), set_fs f' (set_fs f S) = set_fs f' S.
Proof. intros f f' S. destruct S. reflexivity. Qed.

Lemma dcs3_frame_addr_le : forall n ly ly' cid pos, layout_le n ly ly' -> frame_addr ly' cid pos = frame_addr ly cid pos.
Proof. intros n ly ly' cid pos (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity. Qed.

(* ======================= the model: add's footprint inside the walk's ======================= *)
(* the table the call hands back is no longer than the final table of the run *)
Lemma dcs3_len_final : forall segs i t max added p v,
(i < length segs)%nat -> rs_ignore (nth i segs rseg_d) = false ->
vlan_split (rs_name (nth i segs rseg_d)) = Some (p, v) ->
Z.of_nat (length t) <= max ->
(length (snd (vlan_add t max p v)) <= length (snd (r_decl_go (skipn i segs) t max added)))%nat.
Proof.
intros segs i t max added p v Hi Hg Hs Hlen.
rewrite (dcl_go_split segs i t max added p v Hi Hg Hs).
pose proof (dcl_add_len t max p v Hlen) as [L1 L2].
destruct (fst (vlan_add t max p v) <? 0) eqn:Esign; [cbn [snd]; lia|].
destruct (dcl_go_len (skipn (S i) segs) (snd (vlan_add t max p v)) max
  (added + fst (vlan_add t max p v)) L2) as [G1 G2]. exact G1.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variables RLO RHI GOTW GUARD : Z.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
#[local] Notation PRE := (dc_pre B STK_reac_segconf_declared RLO RHI GOTW GUARD).
#[local] Notation FI := (dc_fi B STK_reac_segconf_declared).
#[local] Notation UN := (dc_un B).
#[local] Notation KA := (INV_KA B STK_reac_segconf_declared).

(* vtab_pre and declared_pre, flattened: the conjunct order the rest of the file destructs *)
Lemma dcs3_vt : forall ly S W mem regs tab max n t,
vtab_pre SEGS B ly S W mem regs tab max n t ->
tab <> 0 /\ tab mod 16 = 0 /\ sa_rtab (rdW W mem) tab t /\
Z.of_nat (length t) <= max /\ max < 2 ^ 31 /\
sa_heap B ly S tab (seg_spec.RVLAN_SIZE * (max + 1)) /\
sa_addr (rdW W mem) tab (seg_spec.RVLAN_SIZE * max) /\
amem_range tab (seg_spec.RVLAN_SIZE * max + 8) /\
n <> 0 /\ n mod 4 = 0 /\ sa_val (rdW W mem) n 4 (Z.of_nat (length t)) /\
sa_dst SEGS B ly S W mem regs n 4 /\ sa_addr (rdW W mem) n 4 /\
sa_disj n 4 tab (seg_spec.RVLAN_SIZE * (max + 1)).
Proof using. intros ly S W mem regs tab max n t H. unfold vtab_pre in H. tauto. Qed.

Lemma dcs3_dp_vt : forall ly S W mem regs cc tab max n rcs t gotw guard,
declared_pre SEGS B ly S W mem regs cc tab max n rcs t gotw guard ->
vtab_pre SEGS B ly S W mem regs tab max n t.
Proof using. intros ly S W mem regs cc tab max n rcs t gotw guard H. unfold declared_pre in H. tauto. Qed.

(* the entry's table and count cell, moved to the state of a cut: the table block is live there, and the count
   cell is in a live block, in a frame of the entry state, or on the caller's real stack above the entry sp *)
Lemma dcs3_where : forall c k ly3 S3 W3 regs3 mem3 md3,
PRE c -> FI c k ly3 S3 W3 regs3 mem3 md3 -> UN c ly3 S3 ->
(exists b m, In (b, m) (ablocks B ly3 S3) /\ 0 <= m /\ b <= x_tab c /\
   x_tab c + seg_spec.RVLAN_SIZE * (x_max c + 1) <= b + m) /\
((exists b m, In (b, m) (ablocks B ly3 S3) /\ 0 <= m /\ b <= x_n c /\ x_n c + 4 <= b + m) \/
 (exists cid pos, In (cid, pos) (frames (x_S c)) /\ 0 <= cid /\
    frame_addr ly3 cid pos <= x_n c /\ x_n c + 4 <= frame_addr ly3 cid pos + fs_frame_bytes cid) \/
 (dc_sp0 c <= x_n c /\ x_n c + 4 <= ly_top ly3 /\
    astack_pres (x_ly c) (w_H (x_W c)) (x_mem c) (dc_sp0 c))).
Proof using LAWS.
intros c k ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN.
pose proof HFI as [HJ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
pose proof (proj1 HJ) as HAR3.
pose proof HUN as [Uperm Uly Ufs].
pose proof (dcs3_vt _ _ _ _ _ _ _ _ _ (dcs3_dp_vt _ _ _ _ _ _ _ _ _ _ _ _ _ (cp_dpre _ _ _ _ _ _ _ HPRE)))
  as (_ & _ & _ & _ & _ & Hheap & _ & _ & _ & _ & _ & Hdst & _ & _).
destruct Hheap as (b0 & m0 & Hin0 & Hb0 & Hb1).
pose proof (cp_afn _ _ _ _ _ _ _ HPRE) as HAFN.
pose proof (proj1 HAFN) as HAR0.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin0) as (_ & _ & _ & _ & _ & _ & Hm0).
assert (Hin0' : In (b0, m0) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Uperm)); exact Hin0).
split; [exists b0, m0; split; [exact Hin0'|]; split; [lia | split; [exact Hb0 | exact Hb1]]|].
destruct Hdst as [[Hfr _] | [[Hhp _] | (Hs1 & Hs2 & _ & Hap)]].
- right. left. destruct Hfr as (cid & pos & Hin & Hcid & Hlo & Hhi).
  exists cid, pos. split; [exact Hin|]. split; [exact Hcid|]. rewrite Uly. split; [exact Hlo | exact Hhi].
- left. destruct Hhp as (b & m & Hin & Hlo & Hhi).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin) as (_ & _ & _ & _ & _ & _ & Hm).
  exists b, m. split; [apply (Permutation_in _ (Permutation_sym Uperm)); exact Hin|].
  split; [lia | split; [exact Hlo | exact Hhi]].
- right. right. rewrite Uly. split; [exact Hs1 | split; [exact Hs2 | exact Hap]].
Qed.

(* add's footprint lies inside the walk's own (QDeclared, 2026-10-30: dc_FP's first range ends at
   tab + 18 |t_final|, and its count-cell range is there exactly when the table grew) *)
Lemma dcs3_fp_sub : forall c i ti added p v,
(i < length (dc_segs c))%nat -> rs_ignore (nth i (dc_segs c) rseg_d) = false ->
vlan_split (rs_name (nth i (dc_segs c) rseg_d)) = Some (p, v) ->
dc_loop c i ti added -> (length (x_tb c) <= length ti)%nat -> Z.of_nat (length ti) <= x_max c ->
forall a, inFP (vtab_W (x_tab c) (x_n c) ti (snd (vlan_add ti (x_max c) p v))) a -> inFP (dc_FP c) a.
Proof using.
intros c i ti added p v Hi Hg Hs HLOOP Hlb Hub a Ha.
destruct HLOOP as [HGO _].
pose proof (dcl_add_len ti (x_max c) p v Hub) as [L1 L2].
assert (HLE : (length (snd (vlan_add ti (x_max c) p v)) <= length (snd (dc_res c)))%nat).
{ unfold dc_res. rewrite <- HGO.
  exact (dcs3_len_final (dc_segs c) i ti (x_max c) added p v Hi Hg Hs Hub). }
unfold dc_FP, declared_W, vtab_W in *. cbn [app] in Ha |- *.
apply inFP_cons in Ha as [Ha | Ha].
- apply inFP_cons. left. unfold seg_spec.RVLAN_SIZE in *. lia.
- destruct (Nat.ltb_spec (length ti) (length (snd (vlan_add ti (x_max c) p v)))) as [Hgrow | Hgrow].
  + apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)].
    apply inFP_cons. right.
    replace (length (x_tb c) <? length (snd (dc_res c)))%nat with true
      by (symmetry; apply Nat.ltb_lt; lia).
    apply inFP_cons. left. exact Ha.
  + exfalso. exact (inFP_nil a Ha).
Qed.

(* every byte of add's footprint is apart from this walk's stack window and from its own frame *)
Lemma dcs3_fp_apart : forall c i ti added p v ly3 S3 W3 regs3 mem3 md3,
PRE c -> KA c i ti added p v ly3 S3 W3 regs3 mem3 md3 ->
forall a, inFP (vtab_W (x_tab c) (x_n c) ti (snd (vlan_add ti (x_max c) p v))) a ->
(a < alloc_ceiling \/ dc_sp0 c <= a) /\ ~ (dc_F c <= a < dc_F c + 128).
Proof using LAWS.
intros c i ti added p v ly3 S3 W3 regs3 mem3 md3 HPRE HKA a Ha.
destruct HKA as (HFI & HUN & HTAB & Hi & HLOOP & HLR & H56 & Hign & Hsp & Hstrz & Hvid & Hs4 & Hs5 & Hs8).
pose proof HFI as [HJ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
pose proof (proj1 HJ) as HAR3.
pose proof HJ as (_ & Hly3 & _ & _ & _ & Hfrs3 & _).
assert (Hin1 : In (1, x_fpos c) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (EF3 : frame_addr ly3 1 (x_fpos c) = dc_F c)
  by (unfold dc_F; exact (dcs3_frame_addr_le _ _ _ 1 (x_fpos c) Hly3)).
assert (FB1 : fs_frame_bytes 1 = 128) by (vm_compute; reflexivity).
destruct (dcs3_where c _ ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN) as ((b0 & m0 & Hin0 & Hm0 & Hb0 & Hb1) & HN).
destruct HTAB as (_ & _ & _ & Hub).
pose proof (dcl_add_len ti (x_max c) p v Hub) as [L1 L2].
pose proof (req_size_pos m0 Hm0) as [Q1 Q2].
pose proof (cp_afn _ _ _ _ _ _ _ HPRE) as HAFN.
pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HS0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTKv : STK_reac_segconf_declared = 12560) by (vm_compute; reflexivity).
unfold dc_sp0 in *.
(* the entries lie in the table's block *)
assert (HBLK : forall x, x_tab c + seg_spec.RVLAN_SIZE * Z.of_nat (length ti) <= x <
                 x_tab c + seg_spec.RVLAN_SIZE * Z.of_nat (length (snd (vlan_add ti (x_max c) p v))) ->
                 b0 <= x < b0 + req_size m0).
{ intros x Hx. unfold seg_spec.RVLAN_SIZE in *. lia. }
assert (HSEPB : forall x, b0 <= x < b0 + req_size m0 -> (x < alloc_ceiling /\ ~ (dc_F c <= x < dc_F c + 128))).
{ intros x Hx. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin0) as (_ & _ & Hc0 & _).
  split; [lia|].
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 b0 m0 1 (x_fpos c) HAR3 Hin0 Hin1) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF3, FB1 in Hd. intros Hbad. lia. }
unfold vtab_W in Ha. cbn [app] in Ha. apply inFP_cons in Ha as [Ha | Ha].
- cbn [fst snd] in Ha. destruct (HSEPB a (HBLK a Ha)) as [X1 X2]. split; [left; exact X1|]. exact X2.
- destruct (length ti <? length (snd (vlan_add ti (x_max c) p v)))%nat; [|exfalso; exact (inFP_nil a Ha)].
  apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)]. cbn [fst snd] in Ha.
  destruct HN as [(b & m & Hin & Hm & Hlo & Hhi) | [(cid & pos & Hin & Hcid & Hlo & Hhi) | (Hs1 & Hs2 & _)]].
  + pose proof (req_size_pos m Hm) as [P1 P2].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (_ & _ & Hc0 & _).
    split; [left; lia|].
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 b m 1 (x_fpos c) HAR3 Hin Hin1) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF3, FB1 in Hd. intros Hbad. lia.
  + assert (Hin3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; right; exact Hin).
    destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 cid pos HAR3 Hin3) as (Hg0 & Hgc & _).
    split; [left; lia|].
    apply in_split in Hin as (l2 & l3 & El).
    assert (Ef : frames S3 = [] ++ (1, x_fpos c) :: l2 ++ (cid, pos) :: l3)
      by (rewrite Hfrs3, El; reflexivity).
    pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 mem3 md3 (1, x_fpos c) (cid, pos) [] l2 l3 HAR3 Ef) as Hd.
    unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite EF3, FB1 in Hd.
    set (fbc := fs_frame_bytes cid) in *. intros Hbad. lia.
  + destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 1 (x_fpos c) HAR3 Hin1) as (HFa & HFb & _).
    rewrite EF3 in HFa, HFb. rewrite FB1 in HFb.
    split.
    { right. lia. }
    { intros Hbad. lia. }
Qed.

(* the byte of add's footprint may be written by this walk *)
Lemma dcs3_awr : forall c i ti added p v ly3 S3 W3 regs3 mem3 md3,
PRE c -> KA c i ti added p v ly3 S3 W3 regs3 mem3 md3 ->
forall a, inFP (vtab_W (x_tab c) (x_n c) ti (snd (vlan_add ti (x_max c) p v))) a ->
awr_byte SEGS B STK_reac_segconf_declared (dc_sp0 c) (dc_FP c) (ablocks B (x_ly c) (x_S c)) (ablocks B ly3 S3)
  (frames (x_S c)) ly3 [(1, x_fpos c)] a.
Proof using LAWS.
intros c i ti added p v ly3 S3 W3 regs3 mem3 md3 HPRE HKA a Ha.
pose proof HKA as HKA0.
destruct HKA as (HFI & HUN & HTAB & Hi & HLOOP & HLR & H56 & Hign & Hsp & Hstrz & Hvid & Hs4 & Hs5 & Hs8).
pose proof HFI as [HJ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
pose proof (proj1 HJ) as HAR3.
pose proof HUN as [Uperm Uly Ufs].
destruct HTAB as (_ & _ & Hlb & Hub).
assert (HFPa : inFP (dc_FP c) a)
  by exact (dcs3_fp_sub c i ti added p v Hi Hign Hsp HLOOP Hlb Hub a Ha).
destruct (dcs3_where c _ ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN) as ((b0 & m0 & Hin0 & Hm0 & Hb0 & Hb1) & HN).
pose proof (dcl_add_len ti (x_max c) p v Hub) as [L1 L2].
pose proof (req_size_pos m0 Hm0) as [Q1 Q2].
unfold vtab_W in Ha. cbn [app] in Ha. apply inFP_cons in Ha as [Ha | Ha].
- cbn [fst snd] in Ha. right. left. split; [exact HFPa|].
  exists b0, m0. split; [exact Hin0|]. unfold seg_spec.RVLAN_SIZE in *. lia.
- destruct (length ti <? length (snd (vlan_add ti (x_max c) p v)))%nat; [|exfalso; exact (inFP_nil a Ha)].
  apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)]. cbn [fst snd] in Ha.
  destruct HN as [(b & m & Hin & Hm & Hlo & Hhi) | [(cid & pos & Hin & Hcid & Hlo & Hhi) | (Hs1 & Hs2 & _)]].
  + pose proof (req_size_pos m Hm) as [P1 P2].
    right. left. split; [exact HFPa|]. exists b, m. split; [exact Hin | lia].
  + right. right. right. right. right. right. split; [exact HFPa|].
    exists cid, pos. split; [exact Hin|]. left. unfold in_zr. cbn [fst snd].
    set (fbc := fs_frame_bytes cid) in *. lia.
  + right. right. right. right. right. left. split; [exact HFPa | lia].
Qed.

(* no byte of the walk's footprint is an image byte *)
Lemma dcs3_fp_noimg : forall c k ly3 S3 W3 regs3 mem3 md3,
PRE c -> FI c k ly3 S3 W3 regs3 mem3 md3 -> UN c ly3 S3 ->
forall a, inFP (dc_FP c) a -> ~ in_img SEGS a.
Proof using LAWS.
intros c k ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN a Ha.
pose proof HFI as [HJ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
pose proof (proj1 HJ) as HAR3.
pose proof HJ as (_ & Hly3 & _ & _ & _ & Hfrs3 & _).
pose proof (dcs3_vt _ _ _ _ _ _ _ _ _ (dcs3_dp_vt _ _ _ _ _ _ _ _ _ _ _ _ _ (cp_dpre _ _ _ _ _ _ _ HPRE)))
  as (_ & _ & _ & Hlt & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
destruct (dcs3_where c _ ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN) as ((b0 & m0 & Hin0 & Hm0 & Hb0 & Hb1) & HN).
pose proof (req_size_pos m0 Hm0) as [Q1 Q2].
assert (HTF : Z.of_nat (length (snd (dc_res c))) <= x_max c).
{ unfold dc_res, r_declared.
  destruct (dcl_go_len (rc_seg (x_rc c)) (x_tb c) (x_max c) 0 Hlt) as [_ G2]. exact G2. }
pose proof asan_consts as (C1 & _).
pose proof (cp_afn _ _ _ _ _ _ _ HPRE) as HAFN.
pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HS0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTKv : STK_reac_segconf_declared = 12560) by (vm_compute; reflexivity).
unfold dc_sp0 in *.
unfold dc_FP, declared_W, vtab_W in Ha. cbn [app] in Ha. apply inFP_cons in Ha as [Ha | Ha].
- cbn [fst snd] in Ha.
  apply (blk_img SEGS B LAWS ly3 S3 W3 mem3 md3 b0 m0 a HAR3 Hin0).
  unfold seg_spec.RVLAN_SIZE in *. lia.
- destruct (length (x_tb c) <? length (snd (dc_res c)))%nat; [|exfalso; exact (inFP_nil a Ha)].
  apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)]. cbn [fst snd] in Ha.
  destruct HN as [(b & m & Hin & Hm & Hlo & Hhi) | [(cid & pos & Hin & Hcid & Hlo & Hhi) | (Hs1 & Hs2 & _)]].
  + pose proof (req_size_pos m Hm) as [P1 P2].
    apply (blk_img SEGS B LAWS ly3 S3 W3 mem3 md3 b m a HAR3 Hin). lia.
  + assert (Hin3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; right; exact Hin).
    set (fbc := fs_frame_bytes cid) in *.
    assert (Hr1 : frame_addr ly3 cid pos <= a < frame_addr ly3 cid pos + fbc) by lia.
    intros Himg.
    destruct (al_client_img _ _ LAWS ly3 S3 W3 mem3 md3 a HAR3
      (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin3 Hr1)))))) as [_ Hni].
    exact (Hni Himg).
  + intros Himg. pose proof (pa_segs_low a Himg) as Hlow. unfold kLowMemEnd in Hlow. lia.
Qed.

(* the caller's real stack is at zero shadow: what a real-stack count cell needs *)
Lemma dcs3_stk_shadow : forall ly S W mem md q n,
AR SEGS B ly S W mem md -> ly_stk_lo ly <= q -> q + n <= ly_stk_hi ly -> 0 <= n ->
range_addressable (rdW W mem) SHADOW_OFF q n /\ (0 < n -> shadow_hull_vis (rdW W mem) q n).
Proof using LAWS.
intros ly S W mem md q n HAR Hlo Hhi Hn.
pose proof HAR as (M & _).
pose proof (am_layout _ _ _ _ M) as LO.
pose proof (lo_top _ LO) as LT.
assert (Halo : page_aligned (ly_stk_lo ly)) by tauto.
assert (Hahi : page_aligned (ly_stk_hi ly)) by tauto.
assert (Hhm : kHighMemBeg <= ly_stk_lo ly) by tauto.
unfold page_aligned in Halo, Hahi.
assert (Hlo64 : ly_stk_lo ly mod 64 = 0) by (Z.div_mod_to_equations; lia).
assert (Hhi64 : ly_stk_hi ly mod 64 = 0) by (Z.div_mod_to_equations; lia).
assert (Hlo8 : ly_stk_lo ly mod 8 = 0) by (Z.div_mod_to_equations; lia).
assert (Hhi8 : ly_stk_hi ly mod 8 = 0) by (Z.div_mod_to_equations; lia).
assert (Hlo0 : 0 <= ly_stk_lo ly) by (unfold kHighMemBeg in Hhm; lia).
pose proof (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
  ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZ.
cbn [fst snd] in HZ. unfold zero_shadow, shadow_of_addr in HZ.
assert (HG : forall g, ly_stk_lo ly <= g < ly_stk_hi ly -> rdW W mem (SHADOW_OFF + g / 8) = Some 0).
{ intros g Hg. specialize (HZ (g / 8 - ly_stk_lo ly / 8)).
  replace (SHADOW_OFF + ly_stk_lo ly / 8 + (g / 8 - ly_stk_lo ly / 8)) with (SHADOW_OFF + g / 8) in HZ by lia.
  apply HZ. Z.div_mod_to_equations. lia. }
split.
- intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr. apply HG. lia.
- intros Hpos s Hs.
  destruct (hull_inside (ly_stk_lo ly) (ly_stk_hi ly) q n s Hlo64 Hhi64 Hlo0 Hlo ltac:(lia) ltac:(lia) Hs)
    as (g & Hg8 & Hgr & ->).
  unfold shadow_addr. rewrite (HG g Hgr). discriminate.
Qed.

(* the table and the count cell after the call, from add's post *)
Lemma dcs3_tab_call : forall c (ti ti' : list (list Z * Z)) (W4 : world SEGS) mem4,
sa_rtab (rdW W4 mem4) (x_tab c) ti' -> sa_val (rdW W4 mem4) (x_n c) 4 (Z.of_nat (length ti')) ->
(length (x_tb c) <= length ti)%nat -> (length ti <= length ti')%nat -> Z.of_nat (length ti') <= x_max c ->
dc_tab c ti' W4 mem4.
Proof using.
intros c ti ti' W4 mem4 H1 H2 H3 H4 H5. split; [exact H1|]. split; [exact H2|]. split; [lia | exact H5].
Qed.

(* the table at a state that reads as another one does *)
Lemma dcs3_tab_ext : forall c (ti : list (list Z * Z)) (W4 : world SEGS) mem4 (mem5 : word -> option byte),
dc_tab c ti W4 mem4 -> (forall a, rdW W4 mem5 a = rdW W4 mem4 a) -> dc_tab c ti W4 mem5.
Proof using.
intros c ti W4 mem4 mem5 (H1 & H2 & H3 & H4) He. split; [|split; [|split; [exact H3 | exact H4]]].
- destruct H1 as (bs & Hb & He2). exists bs. split; [|exact He2]. intros j Hj. rewrite He. exact (Hb j Hj).
- intros k Hk. rewrite He. exact (H2 k Hk).
Qed.

(* the kept part of the cut carried over the call of add (its post gives sa_noalloc) *)
Lemma dcs3_un_call : forall c ly3 S3 ly4 S4,
UN c ly3 S3 -> sa_noalloc B ly3 S3 ly4 S4 -> UN c ly4 S4.
Proof using.
intros c ly3 S3 ly4 S4 [U1 U2 U3] (N1 & N2 & f' & N3). subst ly4. constructor.
- exact (Permutation_trans N1 U1).
- exact U2.
- destruct U3 as (f & Hf). exists f'. rewrite N3, Hf. apply dcs3_set_fs_set_fs.
Qed.

End e.
End f.
End d.
