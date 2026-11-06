(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Corelib.Init.Logic"; "eq"; "and"; "iff"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "modulo"; "pow"; "mul"; "of_nat"; "sub"; "div"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "pair"; "andb"; "prod"; "false"; "negb"; "length"; "option"; "Some"; "cons"; "fst"; "snd"; "app"; "nil"; "orb"; "@Stdlib.Lists.List"; "In"; "filter"; "NoDup"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "eval"; "SLit"; "reg_sv"; "rm"; "valuation"; "sobj"; "ss_next"; "ss_objs"; "obj_range"; "ranges_disjoint"; "ss_pc"; "agree_below"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MadviseA"; "cntZ"; "ivs_pos"; "tp_dontneed"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "page_size"; "page_outside_range"; "m_vm_lazy"; "Model"; "page_in_ranges"; "page_base"; "page_mem"; "event"; "m_vm_materialized"; "region_free"; "vm_backing_used"; "vm_noaccess"; "VmMaps"; "m_vmmaps"; "map_contains"; "maps_subtract"; "vm_maps"; "vm_reserved"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise"; "madvise_dontneed_next"; "madvise_dontneed_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_base"; "shadow_addr"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "MI"; "mat_equiv"; "tp_in_maps"; "unpaid"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "sys_input"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "wstep"; "etriple"; "triple1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA2"; "splice"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapNodesA"; "rereserve_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "smatchA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_gpr"; "ms_mem"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "A_after"; "ok_pframeA"; "only_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MadviseA.D.Node"; "madvise_post"; "madvise_pre"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_n"; "mmap_nZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys_mem"; "unmap_range"; "zero_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MadviseA.D"; "madvise_post"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall"; "int32"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi"; "MADV_DONTNEED"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundL SymSoundM SymSoundR SymComplete SymCall SymExit Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA LedgerA SysCallA MmapA MmapFixedA MmapFixedA2 MmapNodesA MadviseSpecA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Definition cntZ (f : word -> bool) (l : list word) : Z := Z.of_nat (length (List.filter f l)).

Lemma cntZ_cons : ltac2:(tb__ "0|1|
S1Q40A1M0S12F_;G0S13G0A1S3S7S34R3S1dG0R2R1A3A2S9S12S7L_;R3R2A1Z1Z0X12x2S34R3R1A2A2A3Fl;Fx;Ff;").
Proof. intros f x l. unfold cntZ. cbn [List.filter]. destruct (f x); cbn [length]; lia. Qed.

Lemma cntZ_nil : ltac2:(tb__ "0|1|
S1Q40A1M0S12F_;S3S7S34R1S21G0A1A2Z0A3Ff;").
Proof. reflexivity. Qed.

Lemma cntZ_nonneg : ltac2:(tb__ "0|1|
S1Q40A1M0S12F_;S13G0A1SaZ0S34R2R1A2A2Fl;Ff;").
Proof. intros. unfold cntZ. lia. Qed.

Lemma filter_filter_and {T} : ltac2:(tb__ "0|2|
VT;S12F_;M0G0S13VT;A1M1S3G1S24VT;R3S24VT;R2R1A3A3S24VT;VT;S16R3R1A1R4R1A1A2Lx;R1A3A3Fl;Fg;Ff;").
Proof.
  intros f g l. induction l as [|x l IH]; [reflexivity|]. cbn [List.filter].
  destruct (g x); cbn [List.filter andb]; [destruct (f x)|]; rewrite IH; reflexivity.
Qed.

Lemma filter_all_true {T} : ltac2:(tb__ "0|1|
VT;S12F_;S13VT;A1M0VT;S23VT;R1R2A3S3S12R4R2A1S14A3F_;Fx;S3G0S24VT;R3R2A3R2A3F_;Fl;Ff;").
Proof.
  intros f l H. induction l as [|x l IH]; [reflexivity|]. cbn [List.filter].
  rewrite (H x (or_introl eq_refl)). rewrite IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma page_mem_filter : ltac2:(tb__ "0|1|
S1Q40A1M0S12F_;G0S13G0A1S3S12S3dR2S24G0R3R1A3A2S16S3dR2R1A2R3R2A1A2A3Fl;Fp;Ff;").
Proof.
  intros f p l. destruct (page_mem p l) eqn:E.
  - apply page_mem_In in E. destruct (f p) eqn:F; cbn [andb].
    + apply page_mem_In. apply filter_In. split; assumption.
    + apply page_mem_false. intros Hin. apply filter_In in Hin as [_ Hin]. congruence.
  - cbn [andb]. apply page_mem_false. apply page_mem_false in E. intros Hin. apply filter_In in Hin as [Hin _]. exact (E Hin).
Qed.

Lemma length_filter_mat : ltac2:(tb__ "0|3|
S13S1Q40A1M0A1M1G1G0S12F_;S25G0R3A2M2G2G0S23G0R1R5A3S23G0R2R7A3F_;Fp;S3S7SfS1aG0S24G0R4R5A3A2A1S34G0S16S3dR1R6A2R5R1A1A2Lp;R6A2A3F_;F_;F_;Fg;Fmat;Ftp;").
Proof.
  intros tp mat g HT HM Hsub. unfold cntZ. f_equal.
  apply NoDup_same_length; [apply List.NoDup_filter; exact HM | apply List.NoDup_filter; exact HT|].
  intros x. rewrite !filter_In. split.
  - intros [Hx Hg]. split; [exact (Hsub x Hx)|]. rewrite Hg, andb_true_r. apply page_mem_In. exact Hx.
  - intros [Hx Hb]. apply andb_prop in Hb as [Hm Hg]. split; [apply page_mem_In; exact Hm | exact Hg].
Qed.

Lemma length_mat : ltac2:(tb__ "0|3|
S13S1Q40A1M0A1M1G1S25G0R2A2M2G2G0S23G0R1R4A3S23G0R2R6A3F_;Fp;S3S7SfS1aG0R4A2A1S34G0S3dR1R5A2Lp;R5A2A3F_;F_;F_;Fmat;Ftp;").
Proof.
  intros tp mat HT HM Hsub. pose proof (length_filter_mat tp mat (fun _ => true) HT HM Hsub) as X.
  rewrite (filter_all_true (fun _ : word => true) mat) in X by reflexivity. rewrite X. unfold cntZ. f_equal. f_equal.
  apply filter_ext_in. intros p _. apply andb_true_r.
Qed.

Definition tp_dontneed (lo hi : Z) (kp : word -> bool) (tp : list word) : list word := ltac2:(tb__ "0|1|
S24S1Q40A1M0G0S22S38Vlo;Vhi;R1A3Vkp;R1A1A2Lp;Vtp;A3").

Lemma tp_dontneed_forget : ltac2:(tb__ "0|2|
S7S7S13S1Q40A1M0A1M1S3G1S36R3R2G0S18L_;R1A4S5dR3R2R1A3A3Ftp;Fhi;Flo;").
Proof. intros. unfold tp_dontneed, tp_forget. apply filter_ext_in. intros p _. apply orb_false_r. Qed.

Lemma tp_dontneed_keep : ltac2:(tb__ "0|2|
S7S7S13S1Q40A1M0A1M1S3G1S36R3R2G0S14L_;R1A4R1A3Ftp;Fhi;Flo;").
Proof. intros. unfold tp_dontneed. apply filter_all_true. intros p _. apply orb_true_r. Qed.

Lemma tp_dontneed_NoDup : ltac2:(tb__ "0|1|
S7S7S1Q40A1M0S12F_;S13G0A1S25G0R1A2S25G0S36R5R4R3R2A4A2F_;Ftp;Fkp;Fhi;Flo;").
Proof. intros. unfold tp_dontneed. apply List.NoDup_filter. assumption. Qed.

Lemma tp_dontneed_sub : ltac2:(tb__ "0|1|
S7S7S1Q40A1M0S12F_;S13G0A1G0S23G0R1S36R5R4R3R2A4A3S23G0R2R3A3F_;Fp;Ftp;Fkp;Fhi;Flo;").
Proof. intros lo hi kp tp p H. unfold tp_dontneed in H. apply filter_In in H as [H _]. exact H. Qed.

Lemma tp_dontneed_out : ltac2:(tb__ "0|1|
S7S7S1Q40A1M0S12F_;S13G0A1G0S23G0R1R2A3S3S12S38R6R5R2A3S14A3S23G0R3S36R7R6R5R4A4A3F_;F_;Fp;Ftp;Fkp;Fhi;Flo;").
Proof. intros lo hi kp tp p H Ho. unfold tp_dontneed. apply filter_In. split; [exact H|]. rewrite Ho. reflexivity. Qed.

Definition ivs_pos (l : list (word * word)) : Prop := ltac2:(tb__ "0|2|
S1Q40M0A1M1G1S23S17G1G1A2S15G1G1R2R1A4Vl;A3SbZ0S0G0R2A2A2F_;Fs;Fb;").

Lemma ivs_pos_nil : ivs_pos [].
Proof. intros b s []. Qed.

Lemma ivs_pos_cons : ltac2:(tb__ "0|3|
S1Q40M0A1M1G1S13S17G1G1A2M2A1SbZ0S0G0R2A2A2S35R2A1S35S1dG2S15G1G1R5R4A4R3A3A1F_;F_;Fl;Fs;Fb;").
Proof. intros b s l Hs Hl b' s' [E|Hin]; [injection E as <- <-; exact Hs | exact (Hl b' s' Hin)]. Qed.

Lemma ivs_pos_app : ltac2:(tb__ "0|4|
S13S17S1Q40A1M0G0A2M1A1M2G2S35R2A1M3G3S35S20G1R4R3A3A1F_;F_;Fl2;Fl1;").
Proof. intros l1 l2 H1 H2 b s Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (H1 b s Hin) | exact (H2 b s Hin)]. Qed.

Lemma ivs_pos_filter : ltac2:(tb__ "0|2|
S17S1Q40A1M0G0A2M1S12F_;S13G1A1S35R1A1S35S24G1R3R2A3A1F_;Fl;Ff;").
Proof. intros f l H b s Hin. apply filter_In in Hin as [Hin _]. exact (H b s Hin). Qed.

Lemma ivs_pos_subtract : ltac2:(tb__ "0|1|
S13S17S1Q40A1M0G0A2A1S7S7S35R3A1S35S46R4R3R2A3A1F_;Fhi;Flo;Fl;").
Proof.
  intros l lo hi H. induction l as [|[a sz] l IH]; [exact ivs_pos_nil|]. cbn [maps_subtract].
  apply ivs_pos_app; [|apply IH; intros b s Hin; apply (H b s); right; exact Hin].
  pose proof (H a sz (or_introl eq_refl)) as Hsz. pose proof (urange a) as Ra. pose proof (urange sz) as Rs.
  unfold iv_subtract. intros b s Hin. apply in_app_or in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [Hin|[]]. injection Hin as <- <-.
    rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [Hin|[]]. injection Hin as <- <-.
    rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.

Lemma region_free_of_uncovered : ltac2:(tb__ "0|3|
S13S17S1Q40M0A1M1G1A2A1G1G1S35R3A1SbZ0S0G0R2A2A2S7S4SaS0G0R5A2M2R1A2SbR1S9G2S0G0R4A2A2A2A2S3S12S77R7R2A2S18A3F_;Fz;S3S12S40R6R5R4A3S14A3F_;F_;F_;Fn;Fa;Fl;").
Proof.
  intros l a n Hpos Hn Hun. induction l as [|[b s] l IH]; [reflexivity|]. cbn [region_free].
  rewrite IH; [rewrite andb_true_r | intros b' s' Hin; apply (Hpos b' s'); right; exact Hin
               | intros z Hz; pose proof (Hun z Hz) as X; cbn [covered existsb] in X; apply orb_false_iff in X as [_ X]; exact X].
  apply negb_true_iff. unfold iv_overlap. apply andb_false_iff.
  pose proof (Hpos b s (or_introl eq_refl)) as Hs.
  destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned b + bv_unsigned s)) as [L1|L1]; [|left; apply Z.ltb_ge; exact L1].
  destruct (Z_lt_le_dec (bv_unsigned b) (bv_unsigned a + bv_unsigned n)) as [L2|L2]; [|right; apply Z.ltb_ge; exact L2].
  exfalso. pose proof (Hun (Z.max (bv_unsigned a) (bv_unsigned b)) ltac:(lia)) as X. cbn [covered existsb] in X.
  apply orb_false_iff in X as [X _]. unfold in_iv, in_rng, ivB, ivS in X. cbn [fst snd] in X.
  apply andb_false_iff in X as [X|X]; [apply Z.leb_gt in X | apply Z.ltb_ge in X]; lia.
Qed.

Lemma map_contains_intro : ltac2:(tb__ "0|5|
S13S17S1Q40M0A1M1G1A2M2A1G1G1G1G1S23G2S15G1G1R2R1A4R5A3SaS0G0R3A2M3S0G0R5A2M4A2SaS9S0G0R6A2G4A2S9S0G0R4A2G3A2A2S3S12S45R8R7R6A3S14A3F_;F_;F_;Fs;Fb;Fn;Fa;Fl;").
Proof.
  intros l a n b s Hin H1 H2. unfold map_contains. apply existsb_exists. exists (b, s). split; [exact Hin|]. cbn [fst snd].
  apply andb_true_intro. split; apply Z.leb_le; assumption.
Qed.

Lemma madvise_dontneed_ok_intro : ltac2:(tb__ "0|5|
S43S1Q40M0A1M1G1G1G1S3S12S40S48R5A1R4R3A3S14A3S23S17G1G1A2S15G1G1R3R2A4S47R6A1A3SaS0G0R4A2M2S0G0R6A2M3A2SaS9S0G0R7A2G3A2S9S0G0R5A2G2A2A2S35S42R9A1A1SbZ0S0G0R8A2A2S7S4SaS0G0RbA2M4R1A2SbR1S9G4S0G0RaA2A2A2A2S3S12S77S42RdA1R2A2S18A3F_;Fz;S3S12S4aRcRbRaA3S14A3F_;F_;F_;F_;F_;F_;F_;Fs;Fb;Fn;Fa;Fh;").
Proof.
  intros h a n b s Hres Hin H1 H2 Hpos Hn Hun. unfold madvise_dontneed_ok.
  rewrite Hres, (map_contains_intro _ a n b s Hin H1 H2), (region_free_of_uncovered _ a n Hpos Hn Hun). reflexivity.
Qed.

Section D.
Variable segs : list Segment.

Section Laws.
Variables (md : Model) (a k : word).
Local Notation lo := (bv_unsigned a).
Local Notation hi := (bv_unsigned a + bv_unsigned k).
Local Notation md' := (madvise_dontneed_next md a k).

Lemma used_dontneed : ltac2:(tb__ "0|4|
S3S7S41S49Vmd;Va;Vk;A3A1S9S10S41Vmd;A1SeS37SfS1aS1Q40M0A1M1S3fVmd;A1M2A2A1A2A2SeS37SfS1aG1S24G1S38S0G0Va;A2M3S9G3S0G0Vk;A2A2A2G2A3A2A1A2A2A3").
Proof using . rewrite dontneed_next_eq. apply vm_backing_used_with_mat. Qed.

Lemma unpaid_dontneed : ltac2:(tb__ "0|4|
S13S1Q40M0A1M1A1M2S3G2S55S49Vmd;Va;Vk;A3R1A2S24G1G1S16S3bR1S39Vmd;A1A2S19S16S3dR1S3fVmd;A1A2S38S0G0Va;A2M3S9G3S0G0Vk;A2A2R1A3A2A1A2Lp;R1A3A3Ftp;").
Proof using .
  intros tp. unfold unpaid. rewrite m_vm_lazy_dontneed_next, m_vm_materialized_dontneed_next.
  apply filter_ext_in. intros p _. rewrite page_mem_filter. reflexivity.
Qed.

Lemma paid_dontneed_le : ltac2:(tb__ "0|2|
S13S1Q40A1M0A1M1G1S25G0R1A2G0S23G0R1R3A3S23G0R2R5A3F_;Fp;SaS51S49Vmd;Va;Vk;A3R3A2S51Vmd;R4A2A2F_;F_;Ftp';Ftp;").
Proof using .
  intros tp tp' HT' Hsub. unfold paid. rewrite used_dontneed.
  set (O := page_outside_range lo hi).
  set (matIn := List.filter (fun p => negb (O p)) (m_vm_materialized md)).
  assert (Hsplit : (length (List.filter O (m_vm_materialized md)) + length matIn = length (m_vm_materialized md))%nat).
  { unfold matIn. pose proof (filter_length_split (fun _ : word => true) O (m_vm_materialized md)) as X.
    cbn [andb] in X. rewrite (filter_all_true (fun _ : word => true)) in X by reflexivity. exact X. }
  assert (INCL : forall p, In p (unpaid md' tp') -> In p (unpaid md tp ++ matIn)).
  { intros p Hp. rewrite unpaid_dontneed in Hp. apply filter_In in Hp as [Htp Hb]. apply andb_prop in Hb as [Hl Hn].
    apply negb_true_iff in Hn. apply in_or_app. destruct (page_mem p (m_vm_materialized md)) eqn:Em.
    - right. unfold matIn. apply filter_In. split; [apply page_mem_In; exact Em|]. cbn [andb] in Hn. fold O in Hn. rewrite Hn. reflexivity.
    - left. unfold unpaid. apply filter_In. split; [exact (Hsub p Htp)|]. rewrite Hl, Em. reflexivity. }
  assert (ND : List.NoDup (unpaid md' tp')) by (unfold unpaid; apply List.NoDup_filter; exact HT').
  pose proof (List.NoDup_incl_length ND INCL) as LEN. rewrite length_app in LEN.
  pose proof page_size_pos. nia.
Qed.

Lemma cnt_keep_id : ltac2:(tb__ "0|5|
S1Q40A1M0S12F_;M1G1G1S13G0A1G0S23G0R1R2A3S3S12R4R2A1S18A3S3S12R7R3A1S14A3F_;F_;Fp;S3S7S9S34G0S16R6R1A1M2S19S16R5R1A1M3R4R1A1A2M4A1A2Lp;R2A2S34G0G4Lp;R2A2A2S9S34G0S16G2S19G3A1A2Lp;R2A2S34G0G3Lp;R2A2A2A3F_;Fl;FO;FM;FL;").
Proof using .
  clear. intros L M O l H.
  induction l as [|x l IH]; [reflexivity|]. rewrite !cntZ_cons.
  specialize (IH (fun p Hp => H p (or_intror Hp))). pose proof (H x (or_introl eq_refl)) as Hx.
  destruct (O x); [destruct (L x), (M x); cbn [andb negb]; lia|].
  rewrite (Hx eq_refl). destruct (M x); cbn [andb negb]; lia.
Qed.

Lemma cnt_forget_id : ltac2:(tb__ "0|6|
S1Q40A1M0S12F_;M1G1G1S13G0A1G0S23G0R1R2A3S3S12R4R2A1S18A3S3S12R7R3A1S14A3F_;F_;Fp;S3S7S9S9S34G0S16R5R1A1M2R4R1A1M3A2M4Lp;R2A2S34G0S16G3S16R6R1A1M5S19G4A1A2A2Lx;R2A2A2S34G0S19G3A1Lp;R2A2A2S9S34G0S16G5S19G2A1A2Lp;R2A2S34G0G2Lp;R2A2A2A3F_;Fl;FO;FM;FL;").
Proof using .
  clear. intros L M O l H.
  induction l as [|x l IH]; [reflexivity|]. rewrite !cntZ_cons.
  specialize (IH (fun p Hp => H p (or_intror Hp))). pose proof (H x (or_introl eq_refl)) as Hx.
  destruct (O x); [destruct (L x), (M x); cbn [andb negb]; lia|].
  rewrite (Hx eq_refl). destruct (M x); cbn [andb negb]; lia.
Qed.

Section Exact.
Variable tp : list word.
Hypothesis HT : List.NoDup tp.
Hypothesis HM : List.NoDup (m_vm_materialized md).
Hypothesis Hsub : ltac2:(tb__ "0|1|
S1Q40A1M0S23G0R1S3fVmd;A1A3S23G0R2Vtp;A3F_;Fp;").

Hypothesis Hlz : ltac2:(tb__ "0|3|
S1Q40M0A1M1S23G1R1Vtp;A3S3S12S38S0G0Va;A2M2S9G2S0G0Vk;A2A2R2A3S18A3S3S12S3bR3S39Vmd;A1A2S14A3F_;F_;Fp;").

Lemma paid_dontneed_keep : ltac2:(tb__ "0|0|
S3S7S51S49Vmd;Va;Vk;A3Vtp;A2S51Vmd;Vtp;A2A3").
Proof using HM HT Hlz Hsub.
  unfold paid. rewrite used_dontneed, unpaid_dontneed.
  rewrite (length_mat tp _ HT HM Hsub), (length_filter_mat tp _ (page_outside_range lo hi) HT HM Hsub).
  pose proof (cnt_keep_id (fun p => page_in_ranges p (m_vm_lazy md)) (fun p => page_mem p (m_vm_materialized md))
                (page_outside_range lo hi) tp Hlz) as K. cbv beta in K.
  unfold cntZ, unpaid in *. unfold page_size. lia.
Qed.

Lemma paid_dontneed_forget : ltac2:(tb__ "0|3|
S3S7S9S51S49Vmd;Va;Vk;A3S5dS0Q40M0Va;A2M1S9G1S0G0Vk;A2A2M2Vtp;A3A2SeS37S34S1G0A1S19S38G1G2R1A3A1Lp;Vtp;A2A2A2S51Vmd;Vtp;A2A3").
Proof using HM HT Hlz Hsub.
  unfold paid. rewrite used_dontneed, unpaid_dontneed. unfold tp_forget. rewrite filter_filter_and.
  rewrite (length_mat tp _ HT HM Hsub), (length_filter_mat tp _ (page_outside_range lo hi) HT HM Hsub).
  pose proof (cnt_forget_id (fun p => page_in_ranges p (m_vm_lazy md)) (fun p => page_mem p (m_vm_materialized md))
                (page_outside_range lo hi) tp Hlz) as K. cbv beta in K.
  unfold cntZ, unpaid in *. unfold page_size. lia.
Qed.
End Exact.
End Laws.

Lemma page_base_self : ltac2:(tb__ "0|2|
S1Q40M0A1M1S3S7ScS0G0R1A2S37A2Z0A3S3G1S3cR2A1R2A3F_;Fp;").
Proof using .
  intros p Hal. apply bv_eq. rewrite page_base_val. pose proof page_size_pos as Pps.
  pose proof (Z.div_mod (bv_unsigned p) page_size ltac:(lia)) as Dp. rewrite Hal in Dp. lia.
Qed.

Lemma page_outside_range_false : ltac2:(tb__ "0|2|
S7S7S1Q40M0A1S5S3S12S38R3R2R1A3S18A3S4SaR3S0G0R1A2M1A2SbG1R2A2A2A2Fp;Fhi;Flo;").
Proof using .
  intros lo hi p. unfold page_outside_range. rewrite negb_false_iff, andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Lemma page_outside_range_true : ltac2:(tb__ "0|2|
S7S7S1Q40M0A1S5S3S12S38R3R2R1A3S14A3S6S4SaR3S0G0R1A2M1A2SbG1R2A2A2A1A2Fp;Fhi;Flo;").
Proof using .
  intros lo hi p. rewrite <- page_outside_range_false. destruct (page_outside_range lo hi p); split; congruence.
Qed.

Lemma tp_inside_lazy : ltac2:(tb__ "0|5|
S3aS13S1Q40M0A1M1A1G1G1S54R4R3A2G1S4SaS0G0R4A2M2S0G0R1A2M3A2SbG3S9G2S0G0R3A2A2A2A2S3S12S3bS3cR2A1S39R7A1A2S14A3F_;Fx;G1S23G1R1R6A3S3S12S38S0G0R6A2M4S9G4S0G0R5A2A2R2A3S18A3S3S12S3bR3S39R9A1A2S14A3F_;F_;Fp;F_;F_;Fk;Fa;Ftp;Fmd;").
Proof using .
  intros md tp a k Htm Hlz p Hp Ho. apply page_outside_range_false in Ho.
  rewrite <- (page_base_self p (proj1 (Htm p Hp))). apply Hlz. exact Ho.
Qed.

Lemma range_in_lazy_pages : ltac2:(tb__ "0|7|
S3aS1Q40M0A1M1G1G1G1S23S17G1G1A2S15G1G1R2R1A4S39R5A1A3SaS0G0R3A2M2S0G0R5A2M3A2SaS9S0G0R6A2G3A2S9S0G0R4A2G2A2A2S3S7ScS0G0R7A2S37A2Z0A3M4G4G1S4SaS0G0RaA2M5S0G0R1A2M6A2SbG6S9G5S0G0R9A2A2A2A2S3S12S3bS3cR2A1S39RcA1A2S14A3F_;Fx;F_;F_;F_;F_;F_;Fs;Fl;Fk;Fa;Fmd;").
Proof using .
  intros md a k l s Hin H1 H2 Hal Hkl x Hx. destruct (page_in_aligned_range a k x Hal Hkl Hx) as [P1 P2].
  apply page_in_ranges_spec. exists (l, s). split; [exact Hin|]. apply page_in_range_spec. cbn [fst snd]. lia.
Qed.

Lemma MI_dontneed : ltac2:(tb__ "0|4|
S3aS13S1Q40M0A1M1A1M2G2G1G1S52Vsegs;R5R4A3S25G1R4A2G1S23G1R1R6A3S23G1R2R8A3F_;Fp;G1S23G1R1R8A3S3S12S38S0G0R7A2M3S9G3S0G0R6A2A2R2A3S14A3S23G1R3R9A3F_;F_;Fp;S52Vsegs;S49R9R6R5A3R7A3F_;F_;F_;F_;Fk;Fa;Ftp';Ftp;Fmd;").
Proof using .
  intros md tp tp' a k (HW & HT & Hmat & Hsub & Hpaid & Hlc & Hivs & Hlm & Htm) HT' Hs Ho.
  apply (MI_intro segs).
  - exact HW.
  - exact HT'.
  - rewrite m_vm_materialized_dontneed_next. apply List.NoDup_filter. exact Hmat.
  - rewrite m_vm_materialized_dontneed_next. intros p Hp. apply filter_In in Hp as [Hp Hout]. exact (Ho p (Hsub p Hp) Hout).
  - rewrite m_vmmaps_dontneed_next. pose proof (paid_dontneed_le md a k tp tp' HT' Hs). lia.
  - rewrite m_vm_lazy_dontneed_next. exact Hlc.
  - exact Hivs.
  - exact Hlm.
  - intros p Hp. exact (Htm p (Hs p Hp)).
Qed.

Lemma mat_equiv_dontneed : ltac2:(tb__ "0|4|
S3aS13S1Q40M0A1M1A1G1G1S52Vsegs;R4R3A3G1S4SaS0G0R4A2M2S0G0R1A2M3A2SbG3S9G2S0G0R3A2A2A2A2S3S12S3bS3cR2A1S39R7A1A2S14A3F_;Fx;S53Vsegs;R5R6S49R6R4R3A3A4F_;F_;Fk;Fa;Ftp;Fmd;").
Proof using .
  intros md tp a k HMI Hlz. pose proof HMI as (HW & HT & Hmat & Hsub & Hpaid & Hlc & Hivs & Hlm & Htm).
  split; [|split].
  - eexists. apply dontneed_next_eq.
  - apply paid_dontneed_keep; [exact HT | exact Hmat | exact Hsub | exact (tp_inside_lazy md tp a k Htm Hlz)].
  - intros _. apply (MI_dontneed md tp tp a k HMI HT); intros p Hp; try intros _; exact Hp.
Qed.

Lemma smatchA_after_dontneed : ltac2:(tb__ "0|e|
S2bS2bS13S1Q40M0A1M1A1M2G2S4cS13S3eA1M3S66S3aG3G1G1G1S26S8S6bVsegs;ReRcRaS15G3S56R9S57R8R7A2A4A5S3S7ScS0G0R6A2S37A2Z0A3M4G4SaS9S0G0R8A2S0G0R7A2A2SdZ2Z40A2A2G1S4SaS0G0RaA2M5S0G0R1A2M6A2SbG6S9G5S0G0R9A2A2A2A2S3S12S3bS3cR2A1S39RdA1A2S14A3F_;Fx;S25G1R10A2G1S23G1R1R12A3S23G1R2R14A3F_;Fp;G1S23G1R1R14A3S3S12S38S0G0ReA2M7S9G7S0G0RdA2A2R2A3S14A3S23G1R3R15A3F_;F_;Fp;S2cS23S2cR1S2eS4bR13A1A1A3S30S2fR18R2A2S15S7S7S0G0RfA2M8S9G8G7A2A4A2F_;Fo;S17S26S26A2M9S7S23G9R2S4dR15A1A3S4SaS0G0S27R1aS1eS26S26R3A3A2A2MaR2A2SbR2S9GaS0G0S27R1aS1fS26S26R3A3A2A2A2A2A2S6S4SaS0G0R12A2MbS0G0S4fS0G0S27R1bS4eR17A1A2A2R3A2A2McA2SbGcS9GbS0G0R11A2A2A2A2A1F_;F_;Fy;Frr;S32S2dS4bR14A1A1S5eR18S5fS2aR18A1S60R15A1RfReA4A2R17A3S7cS2dS4bR15A1A1RcA2S3S12S33RdReA2S14A3S3G1S27R1aRfA2R10A3S65Vsegs;R1bR19S50R18S7bS4bR18A1MdR10S2eGdA1RfA4A2S15G3S56R14S57S73R16R11S75S68R16A1R13R12A3A3S49R15R13R12A3A2A4A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnx;Fe;Fr;Fn;Fa;Ftr';Fmd;Fms;Ftr;FA;Ftp';Ftp;Frho';Frho;").
Proof using .
  intros rho rho' tp tp' A tr ms md tr' a n r e nx Hsp Hal Hnl Hend Hlz HT' Hs Ho Hdisj Hxs Hag' Hnx He Hev.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  pose proof HMI as (HW & HT & Hmat & Hsub & Hpaid & Hlc & Hivs & Hlm & Htm).
  pose proof Hsp as (Hspv & _ & Hwf & Hsh & Hhz). rewrite virt_unfold in Hspv.
  pose proof (urange a) as Ra. pose proof (urange n) as Rn. pose proof page_size_pos as Pps.
  set (lo := bv_unsigned a) in *. set (hi := lo + bv_unsigned n) in *.
  set (md' := madvise_dontneed_next md a n). set (new := rereserve_bytes tp') in *.
  assert (Hnro : forall x : word, lo <= bv_unsigned x < hi -> ro_addr segs x = false).
  { intros x Hx. unfold ro_addr. pose proof (Hlz x Hx) as Hp.
    apply page_in_ranges_spec in Hp as ([l s] & Hin & Hr). apply page_in_range_spec in Hr. cbn [fst snd] in Hr.
    pose proof (page_base_range x) as PB. rewrite (Hlc l s (bv_unsigned x) Hin ltac:(lia)). reflexivity. }
  assert (TPout : forall x : word, ~ (lo <= bv_unsigned x < hi) -> page_mem (page_base x) tp' = page_mem (page_base x) tp).
  { intros x Hx.
    assert (Hpo : page_outside_range lo hi (page_base x) = true).
    { apply page_outside_range_true. destruct (page_out_of_aligned_range a n x Hal Hnl Hx) as [P|P]; fold lo in P; fold hi in P; lia. }
    destruct (page_mem (page_base x) tp) eqn:E.
    - apply page_mem_In. apply page_mem_In in E. exact (Ho _ E Hpo).
    - apply page_mem_false. apply page_mem_false in E. intros Hin. exact (E (Hs _ Hin)). }
  assert (HIN : forall x : word, lo <= bv_unsigned x < hi -> hid md' tp' x = negb (page_mem (page_base x) tp')).
  { intros x Hx. unfold hid, md'. rewrite m_vm_lazy_dontneed_next, (Hlz x Hx). reflexivity. }
  assert (HOUT : forall x : word, ~ (lo <= bv_unsigned x < hi) -> hid md' tp' x = hid md tp x).
  { intros x Hx. unfold hid, md'. rewrite m_vm_lazy_dontneed_next, (TPout x Hx). reflexivity. }
  assert (Hh' : m_halted md' = m_halted md) by reflexivity.

  assert (Ev : vms md' tp' (after_sys_mem ms r (zero_range (ms_mem ms) a n))
               = after_sys_mem (vms md tp ms) r (splice (ms_mem (vms md tp ms)) new a n)).
  { unfold vms, restrict, after_sys_mem. cbn [ms_regs ms_fregs ms_pc ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
    f_equal. apply functional_extensionality. intros x. unfold mrestrict, splice. rewrite zero_range_at.
    destruct (in_range a n x) eqn:Ein.
    - apply in_range_spec in Ein. rewrite (HIN x Ein). unfold new, rereserve_bytes. destruct (page_mem (page_base x) tp'); reflexivity.
    - assert (Hn : ~ (lo <= bv_unsigned x < hi)) by (intros H; apply (proj2 (in_range_spec a n x)) in H; congruence).
      rewrite (HOUT x Hn). reflexivity. }
  split; [|split; [|split; [|split]]].
  - unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS]. fold md'. rewrite Ev.
    pose proof (smatch_pending_reframe segs rho (ax_S A) tr (vms md tp ms) (vmd md) a n new Hspv Hend Hdisj
                  ltac:(intros x Hx Hro; rewrite (Hnro x Hx) in Hro; discriminate)) as Hsp1.
    pose proof (smatch_pending_agree segs _ rho' (ax_S A) tr _ (vmd md) Hag' Hsp1) as Hsp2.
    rewrite after_sys_mem_with_mem. unfold after_sys.
    eapply smatch_after_sys; [exact Hsp2 | | exact Hnx | exact He | exact Hev | | |].
    + apply (proj2 (model_idle_vmd md')). rewrite Hh'. exact Hh.
    + apply forallb_forall. intros o Ho'. eapply obj_wf_mono; [exact Hnx|]. exact (proj1 (forallb_forall _ _) (swf_objs _ (smatch_pendingA_swf segs _ _ _ _ Hsp)) o Ho').
    + apply mem_match_after_sys_same. exact (smatch_pending_mem segs _ _ _ _ _ Hsp2).
    + exact (smatch_pending_ro_clear segs _ _ _ _ _ Hsp2).
  -   cbn [cfg_model cfg_ms snd fst]. exact (MI_dontneed md tp tp' a n HMI HT' Hs Ho).
  -   unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  -
    set (rho1 := set_rm rho (splice (rm rho) new a n)) in *.
    assert (Hsh1 : shadow_ok rho1 A).
    { eapply (shadow_ok_transport rho rho1 A A); [reflexivity | apply eval_set_rm | intros; unfold rho1; rewrite !eval_set_rm; split; reflexivity | | exact Hsh].
      intros x Hxw Hout Hdef. split; [apply outside_all_set_rm; exact Hout|].
      unfold rho1. cbn [set_rm rm]. unfold splice.
      destruct (in_range a n _) eqn:E; [|reflexivity]. exfalso. apply in_range_spec in E.
      exact (xword_avoid_aligned rho A _ _ x (mod8_of_page _ Hal) (mod8_of_pages _ _ Hal Hnl) Hxs Hxw E). }
    exact (shadow_ok_stable A (ax_setS A (S_after (ax_S A) e (ss_objs (ax_S A)) nx)) rho1 rho' Hag' Hwf (smatch_pendingA_swf segs _ _ _ _ Hsp) eq_refl eq_refl eq_refl Hsh1).
  -
    cbn [cfg_model cfg_ms snd]. fold md'. intros x Hx. rewrite after_sys_memq, zero_range_at.
    destruct (in_range a n x) eqn:E; [left; reflexivity|].
    assert (Hn : ~ (lo <= bv_unsigned x < hi)) by (intros H; apply (proj2 (in_range_spec a n x)) in H; congruence).
    rewrite (HOUT x Hn) in Hx. exact (Hhz x Hx).
Qed.

Lemma madv_len_sym : ltac2:(tb__ "0|6|
S2bS13S1Q40M0A1M1A1S4cS13S3eA1M2S66S3aS26S7S6bVsegs;R8R7R6S15G2S56R5S57R4R3A2A4A5S3S26S29S4bR7A1ZbA2R3A3S3S7S0G0S27RaR4A2A2R3A3S3S7ScR4Z1000A2Z0M3A3S4SbG3R5A2SbR5SdZ2Z3eA2A2A2S4S6S3G1S67R9U1A2M4S2G0G3A2A3A1S4S3S7S72G4A1R6A3S4S3G1S71G4A1S2G0R6A2M5A3S3S7S0G0G5A2R6A3A2A2A2F_;F_;F_;F_;F_;Fnlit;Felen;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md elen nlit Hsp H11 Helen Hmod Hn.
  destruct (pending_argsA segs rho tp A tr ms md Hsp) as (_ & G1 & _). rewrite H11 in G1.
  assert (Hlenv : bv_unsigned (ms_gpr ms 1) = nlit) by (rewrite G1; exact Helen).
  assert (HnZ : mmap_nZ (ms_gpr ms 1) = nlit).
  { unfold mmap_nZ, page_round_up_Z, page_size. rewrite Hlenv.
    pose proof Hmod as Hmod'. apply Z.mod_divide in Hmod'; [|lia]. destruct Hmod' as [q Hq]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia.
    rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  split; [|split; [exact HnZ | split; [unfold mmap_n; rewrite HnZ; reflexivity|]]].
  - intros E. rewrite E in Hlenv. rewrite Z_to_bv_unsigned in Hlenv. change (bv_wrap 64 0) with 0 in Hlenv. lia.
  - rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

Lemma int32_lit4 : ltac2:(tb__ "0|1|
S3S7S0Q40M0S79S2G0Z4A2A1A2S7aA3").
Proof using . reflexivity. Qed.

Section Node.
Variables (J Jo : jpredA) (A : axst) (rho : valuation) (tp : list word) (kp : word -> bool) (ea elen : sv) (nlit : Z).
Hypothesis H17 : ltac2:(tb__ "0|0|
S3S26S29S4bVA;A1Z11A2S28Ze9A1A3").
Hypothesis H10 : ltac2:(tb__ "0|0|
S3S26S29S4bVA;A1ZaA2Vea;A3").
Hypothesis H11 : ltac2:(tb__ "0|0|
S3S26S29S4bVA;A1ZbA2Velen;A3").
Hypothesis Helen : ltac2:(tb__ "0|0|
S3S7S0Q40S27Vrho;Velen;A2A2Vnlit;A3").
Hypothesis Hmod : nlit mod 4096 = 0.
Hypothesis Hn : 0 < nlit < 2 ^ 62.
Hypothesis H12 : ltac2:(tb__ "0|0|
S3S26S29S4bVA;A1ZcA2S28Z4A1A3").

Definition madvise_pre : Prop := ltac2:(tb__ "0|c|
S13S3eA1M0S66S3aS6bVsegs;Vrho;Vtp;VA;S15G0S56R3S57R2R1A2A4A5VJ;Vrho;Vtp;R4R2A4S67R4U0A2S1Q40M1A1M2S2G1Vnlit;A2G2S36S0G1R2A2M3S9G3Vnlit;A2Vkp;Vtp;A4S13G2A1S4S3S7ScS0G1R3A2M4S37A2Z0A3S4SbS9G4Vnlit;A2SdZ2Z40A2A2S4S3S12S4aS44R6A1R3R2A3S14A3S4G2S4SaS0G1R4A2M5S0G1R1A2M6A2SbG6S9G5Vnlit;A2A2A2S3S12S3bS3cR2A1S39R8A1A2S14A3F_;Fx;S4S2cS23S2cR1S2eS4bVA;A1A1A3S30S2fVrho;R2A2S15S7S7S0G1R5A2M7S9G7Vnlit;A2A4A2F_;Fo;S4S17S26S26A2M8S7S23G8R2S4dVA;A1A3S4SaS0G1S27Vrho;S1eS26S26R3A3A2A2M9R2A2SbR2S9G9S0G1S27Vrho;S1fS26S26R3A3A2A2A2A2A2S6S4SaS0G1R7A2MaS0G1S4fS0G1S27Vrho;S4eVA;A1A2A2R3A2A2MbA2SbGbS9GaVnlit;A2A2A2A1F_;F_;Fy;Frr;VJo;S5eVrho;S5fS2aVrho;A1S60R1A1R3R2A4A2R1R8S49R6R3R2A3A4A2A2A2A2A2A2Ttp';Tn;Ta;F_;F_;Fmd;Fms;Ftr;").

Definition madvise_post : assn := ltac2:(tb__ "0|3|
S27Vrho;Vea;A2S1Q40M0A1M1S2G0Vnlit;A2G1S36S0G0R2A2M2S9G2Vnlit;A2Vkp;Vtp;A4S13G1A1S59S61Vsegs;VJo;S6cVA;S28Z0A1A2S5eVrho;S5fS2aVrho;A1S60R2A1R4R3A4A2R2R1A6Lw;Ttp';Tn;Ta;").

Lemma madvise_coreA : ltac2:(tb__ "0|4|
S70S13S3eA1M0S66S3aS6bVsegs;Vrho;Vtp;VA;S15G0S56R3S57R2R1A2A4A5VJ;Vrho;Vtp;R4R2A4S15G0S56R5S57S73R4S2Q40M1Z0A2S75S68R4A1S67R4U0A2M2S71S67R4U1A2A1M3A3A3S49R3G2G3A3A2A4S17G0S56A2S4S6eS58Vsegs;R5S2G1Ze9A2A3R4A2S4S59S5aVsegs;S15G0S56R7S57R6R5A2A4R1A3S3S59R2R3A3F_;Fw';S4S5aVsegs;S15G0S56R6S57R5R4A2A4R1A3S6fR1A1A2A2A2TW;F_;F_;Fmd;Fms;Ftr;F_;").
Proof using H10 H11 H12 H17 Helen Hmod Hn.
  intros HJ tr ms md Hsp Hk W.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  destruct (madv_len_sym rho tp A tr ms md elen nlit Hsp H11 Helen Hmod Hn) as (Hlen & HnZ & HnE & Un).
  destruct (pending_argsA segs rho tp A tr ms md Hsp) as (G0 & _ & G2 & _). rewrite H10 in G0. rewrite H12 in G2. cbn [eval] in G2.
  destruct (HJ tr ms md Hsp Hk) as (Hal & Hwrap & Hgate & Hlz & Hdisj & Hxs & HJo).
  assert (H233 : bv_unsigned (Z_to_bv 64 233) = 233%Z) by reflexivity.
  assert (Hadv : bv_unsigned (int32 (ms_gpr ms 2)) = MADV_DONTNEED) by (rewrite G2; exact int32_lit4).
  assert (Hwrap' : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) < two_pow_64) by (rewrite HnZ; exact Hwrap).
  rewrite <- HnE in Hgate.
  split; [exact (madvise_only_okA segs ms md _ H233 Hadv Hal Hlen Hwrap' Hgate)|].
  split; [intros w' Hw; exact (wstep_madvise_invA segs ms md _ Hh H233 Hadv Hal Hlen Hwrap' Hgate tr w' Hp Hw)|].
  split; [exact (wstep_madvise_introA segs ms md _ Hh H233 Hadv Hal Hlen Hwrap' Hgate tr Hp)|].
  unfold W, madvise_post. cbv zeta. rewrite HnE. rewrite <- G0. split.
  - unfold A_after.
    apply (smatchA_after_dontneed rho _ tp _ A tr ms md tr (ms_gpr ms 0) (Z_to_bv 64 nlit) (Z_to_bv 64 0) (SLit 0) (ss_next (ax_S A)) Hsp).
    + exact Hal.
    + rewrite Un. unfold page_size. exact Hmod.
    + rewrite Un. lia.
    + rewrite Un. exact Hlz.
    + apply tp_dontneed_NoDup. exact (MI_nodupT segs _ _ HMI).
    + intros p. apply tp_dontneed_sub.
    + rewrite Un. intros p. apply tp_dontneed_out.
    + rewrite Un. exact Hdisj.
    + rewrite Un. exact Hxs.
    + apply agree_below_refl.
    + apply Pos.le_refl.
    + reflexivity.
    + reflexivity.
  - cbn [w_tr w_cfg fst snd cfg_model]. exact HJo.
Qed.

Theorem triple1_madvise_dontneedA : ltac2:(tb__ "0|1|
S59OF_;S64Vsegs;R1VJ;A3S6dVsegs;R2VJ;A3S63Vsegs;S2dS4bVA;A1M0A1VJ;A3S3S1bS69A1S76Vsegs;S31G0A1A2S1cS69S6aA2A3S70S5cVsegs;R6S61Vsegs;VJ;VA;Vrho;Vtp;A5S6fA4F_;F_;F_;F_;F_;Fok;").
Proof using H10 H11 H12 H17 Helen Hmod Hn.
  intros ok Hokf Hokp Hst Hi HJ.
  apply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
  intros tr ms md Hsp Hk. destruct (madvise_coreA HJ tr ms md Hsp Hk) as (Hoo & Hinv & _ & Hpost).
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  split.
  - eapply Hokp; [exact Hk | exact Hp | exact Hoo].
  - intros w' Hw. rewrite (Hinv w' Hw). exact Hpost.
Qed.

Theorem etriple_madvise_dontneedA : ltac2:(tb__ "0|1|
S63Vsegs;S2dS4bVA;A1M0A1VJ;A3S3S1bS69A1S76Vsegs;S31G0A1A2S1cS69S6aA2A3S70S5bVsegs;S61Vsegs;VJ;VA;Vrho;Vtp;A5S6fA3F_;F_;F_;").
Proof using H10 H11 H12 H17 Helen Hmod Hn.
  intros Hst Hi HJ.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md Hsp Hk. destruct (madvise_coreA HJ tr ms md Hsp Hk) as (_ & _ & Hstep & Hpost).
  eexists. split; [exact Hstep | exact Hpost].
Qed.
End Node.

Lemma splice_forget_unmap : ltac2:(tb__ "0|5|
S1Q40M0A1M1S1bS1Q8A1A1F_;M2S13G1A1G1G1S3S7ScS0G0R2A2S37A2Z0A3M3G3S3G2S5fR6S60S5dS0G0R4A2M4S9G4S0G0R3A2A2R5A3A1R4R3A4S74R6R4R3A3A3F_;F_;Fn;Fa;Ftp;Fm;").
Proof using .
  intros m tp a n Hal Hnl. apply functional_extensionality. intros x. unfold splice. rewrite unmap_range_at.
  destruct (in_range a n x) eqn:E; [|reflexivity]. apply in_range_spec in E.
  destruct (page_in_aligned_range a n x Hal Hnl E) as [P1 P2]. pose proof page_size_pos as Pps.
  unfold rereserve_bytes. replace (page_mem (page_base x) (tp_forget (bv_unsigned a) (bv_unsigned a + bv_unsigned n) tp)) with false; [reflexivity|].
  symmetry. apply page_mem_false. intros Hin. unfold tp_forget in Hin. apply filter_In in Hin as [_ Ho].
  apply page_outside_range_true in Ho. lia.
Qed.

Lemma madvise_post_keep : ltac2:(tb__ "0|2|
S62S4cS2bS13S1Q40M0A1M1A1S26S7S59S5S78R7R6R5R4G1S14L_;R3R2R1A8S61Vsegs;R7S6cR6S28Z0A1A2S5eR5S5fS2aR5A1S60R4A1S27R5R3A2S2G0R2A2A4A2R4R1A6A2Fw;Fnlit;Fea;Ftp;Frho;FA;FJo;").
Proof using . intros. unfold madvise_post. cbv zeta. rewrite tp_dontneed_keep. tauto. Qed.

Lemma madvise_post_forget : ltac2:(tb__ "0|5|
S62S4cS2bS13S1Q40M0A1M1A1S26S7S59S3S7ScS0G0S27R5R3A2A2S37A2Z0M2A3S3S7ScR3Z1000A2G2A3S4SbG2R4A2SbR4SdZ2Z3eA2A2A2S5S78RaR9R8R7G1S18L_;R6R5R4A8S61Vsegs;RaS6cR9S28G2A1A2S5eR8S74S2aR8A1S27R8R6A2M3S2G0R5A2A3A2S5dS0G0G3A2M4S9G4R5A2R7A3R4A6A2F_;F_;F_;Fw;Fnlit;Fea;Ftp;Frho;FA;FJo;").
Proof using .
  intros Jo A rho tp ea nlit w Hal Hmod Hn. unfold madvise_post. cbv zeta. rewrite tp_dontneed_forget.
  assert (Un : bv_unsigned (Z_to_bv 64 nlit) = nlit) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia).
  pose proof (splice_forget_unmap (rm rho) tp (eval rho ea) (Z_to_bv 64 nlit) Hal ltac:(rewrite Un; unfold page_size; exact Hmod)) as E.
  rewrite Un in E. rewrite E. tauto.
Qed.

Lemma tp_inside_count : ltac2:(tb__ "0|7|
S13S1Q40M0A1M1A1G1G1S25G1R3A2G1S23G1R1R5A3S3S7ScS0G0R2A2M2S37A2Z0M3A3F_;Fp;S3S7ScS0G0R4A2S37A2G3A3M4G4SaS9S0G0R6A2S0G0R5A2A2SdZ2Z40A2A2G1S3S7ScS0G0R1A2S37A2G3A3S4SaS0G0R9A2M5G2A2SbG2S9G5S0G0R8A2A2M6A2A2S23G1R3RbA3F_;F_;Fp;S3S7S34G1S19S38G5G6R1A3A1Lp;R9A2S11S0G0R7A2S37A2A3F_;F_;F_;F_;F_;F_;Fk;Fa;Ftp;").
Proof using .
  intros tp a k HT Htal Hal Hkl Hend Hall. pose proof page_size_pos as Pps. pose proof (urange a) as Ra. pose proof (urange k) as Rk.
  set (lo := bv_unsigned a) in *. set (hi := lo + bv_unsigned k) in *.
  set (q := bv_unsigned k / page_size).
  assert (Hq : bv_unsigned k = page_size * q).
  { unfold q. pose proof (Z.div_mod (bv_unsigned k) page_size ltac:(lia)) as D. rewrite Hkl in D. lia. }
  assert (Hq0 : 0 <= q) by (unfold q; apply Z.div_pos; lia).
  set (pg := fun i : nat => Z_to_bv 64 (lo + page_size * Z.of_nat i) : word).
  set (pages := List.map pg (List.seq 0 (Z.to_nat q))).
  assert (Hpgv : forall i, (i < Z.to_nat q)%nat -> bv_unsigned (pg i) = lo + page_size * Z.of_nat i).
  { intros i Hi. unfold pg. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). nia. }
  assert (NDp : List.NoDup pages).
  { unfold pages. apply Finite.Injective_map_NoDup_in; [|apply List.seq_NoDup].
    intros i j Hi Hj E. apply in_seq in Hi. apply in_seq in Hj. apply (f_equal bv_unsigned) in E.
    rewrite (Hpgv i), (Hpgv j) in E by lia. nia. }
  unfold cntZ. rewrite (NoDup_same_length _ pages (List.NoDup_filter _ HT) NDp).
  - unfold pages. rewrite length_map, length_seq. lia.
  - intros p. rewrite filter_In. unfold pages. rewrite in_map_iff. split.
    + intros [Hp Hb]. apply negb_true_iff in Hb. apply page_outside_range_false in Hb.
      pose proof (Htal p Hp) as Hpal. pose proof (Z.div_mod (bv_unsigned a) page_size ltac:(lia)) as Da. fold lo in Da. fold lo in Hal. rewrite Hal in Da.
      pose proof (Z.div_mod (bv_unsigned p) page_size ltac:(lia)) as Dp. rewrite Hpal in Dp.
      set (i := bv_unsigned p / page_size - lo / page_size).
      assert (Hi : 0 <= i < q) by (unfold i; nia).
      exists (Z.to_nat i). split.
      * apply bv_eq. rewrite Hpgv by lia. rewrite Z2Nat.id by lia. unfold i. lia.
      * apply in_seq. lia.
    + intros (i & <- & Hi). apply in_seq in Hi. pose proof (Hpgv i ltac:(lia)) as V.
      assert (Hpal : bv_unsigned (pg i) mod page_size = 0).
      { rewrite V. rewrite Z.add_mod, Hal by lia. rewrite (Z.mul_comm page_size), Z_mod_mult. reflexivity. }
      assert (Hrng : lo <= bv_unsigned (pg i) < hi) by (rewrite V; unfold hi; nia).
      split; [exact (Hall _ Hpal Hrng)|]. apply negb_true_iff. apply page_outside_range_false. exact Hrng.
Qed.

Lemma paid_dontneed_forgetA : ltac2:(tb__ "0|6|
S3aS13S1Q40M0A1M1A1G1G1S52Vsegs;R4R3A3G1S4SaS0G0R4A2M2S0G0R1A2M3A2SbG3S9G2S0G0R3A2A2M4A2A2S3S12S3bS3cR2A1S39R7A1A2S14A3F_;Fx;S3S7S9S51S49R6R4R3A3S5dG2G4R5A3A2SeS37S34G1S19S38S0G0R5A2M5S9G5G2A2R1A3A1Lp;R5A2A2A2S51R6R5A2A3F_;F_;Fk;Fa;Ftp;Fmd;").
Proof using .
  intros md tp a k (HW & HT & Hmat & Hsub & Hpaid & Hlc & Hivs & Hlm & Htm) Hlz.
  apply paid_dontneed_forget; [exact HT | exact Hmat | exact Hsub | exact (tp_inside_lazy md tp a k Htm Hlz)].
Qed.

Lemma paid_dontneed_forget_all : ltac2:(tb__ "0|9|
S3aS13S1Q40M0A1M1A1G1G1S52Vsegs;R4R3A3S3S7ScS0G0R3A2S37A2Z0M2A3M3G3SaS9S0G0R5A2S0G0R4A2A2SdZ2Z40A2A2G1S4SaS0G0R7A2M4S0G0R1A2M5A2SbG5S9G4S0G0R6A2A2A2A2S3S12S3bS3cR2A1S39RaA1A2S14A3F_;Fx;G1S3S7ScG5S37A2G2A3S4SaS0G0R9A2M6S0G0R2A2M7A2SbG7S9G6S0G0R8A2M8A2A2A2S23G1R3RbA3F_;F_;Fp;S3S7S51S49RaR8R7A3S5dG8S9G8G4A2R9A3A2S10S51RaR9A2G4A2A3F_;F_;F_;F_;F_;F_;Fk;Fa;Ftp;Fmd;").
Proof using .
  intros md tp a k HMI Hal Hkl Hend Hlz Hall. pose proof (paid_dontneed_forgetA md tp a k HMI Hlz) as E.
  pose proof HMI as (HW & HT & Hmat & Hsub & Hpaid & Hlc & Hivs & Hlm & Htm).
  rewrite (tp_inside_count tp a k HT (fun p Hp => proj1 (Htm p Hp)) Hal Hkl Hend Hall) in E.
  pose proof page_size_pos as Pps. pose proof (Z.div_mod (bv_unsigned k) page_size ltac:(lia)) as D. rewrite Hkl in D. lia.
Qed.

End D.
