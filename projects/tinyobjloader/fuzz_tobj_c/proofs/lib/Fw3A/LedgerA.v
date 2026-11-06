(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "lt"; "leb"; "modulo"; "sub"; "ge"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "prod"; "bool"; "pair"; "fst"; "snd"; "true"; "cons"; "false"; "app"; "None"; "andb"; "length"; "negb"; "nil"; "option"; "orb"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "vm_maps"; "m_vmmaps"; "vm_backing_used"; "m_vm_lazy"; "vm_noaccess"; "vm_forget_range"; "with_vmmaps"; "VmMaps"; "maps_subtract"; "page_size"; "lazy_interior"; "page_in_ranges"; "vm_add_lazy"; "m_vm_materialized"; "page_base"; "vm_limit"; "region_free"; "iv_subtract"; "page_mem"; "page_outside_range"; "@Stdlib.Lists.List"; "In"; "NoDup"; "existsb"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "ivs_wf"; "model_ivs_wf"; "iv_wf"; "iv_count"; "overlap_sum"; "covered"; "ivS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "hid"; "lazy_in_maps"; "unpaid"; "MI"; "lazy_clear"; "paid"; "tp_in_maps"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.LedgerA"; "tp_clear_of"; "page_in_range"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "find_segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Restrict"; "wx_segs_nowrap"; "@Corelib.Init.Peano"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymSoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Lemma iv_count_le_size : ltac2:(tb__ "0|1|
SfS12F_;S11S1Q40A1M0G0A2S2S3dR2R1A2S40R1A1A2Fp;FP;").
Proof.
  intros P p. unfold iv_count. pose proof (zcount_le_len P (ivB p) (Z.to_nat (ivS p))).
  pose proof (S_range p). rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma iv_count_covered_zero : ltac2:(tb__ "0|2|
S10S11S1Q40A1M0G0A2M1A1G1S36G1R1R2A3SaSfS3dSfS1dS3fR4R1A2A1Lx;R2A2Z0A3F_;Fp;FC;").
Proof.
  intros C p Hin. unfold iv_count. apply zcount_false. intros x Hx.
  pose proof (S_range p). rewrite Z2Nat.id in Hx by lia.
  apply negb_false_iff. unfold covered. apply existsb_exists. exists p. split; [exact Hin|].
  unfold in_iv, in_rng. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma used_maps_cons_le : ltac2:(tb__ "0|4|
S21S29S1Q40M0A1M1G1S3bR4A1S3cS13G1G1R3R2A4A1SaS10S11G1G1A2M2A1M3S22R5A1S17G2S13G1G1R4R3A4S22S23R6A1A1A3A3SaG3S26R6A1S26S23R7A1A1A3S2S24S28R7R8A2A1S3S24R8A1S0G0R5A2A2A2F_;F_;F_;F_;Fn;Fa;Fh';Fm;").
Proof.
  intros m h' a n Hwf Hiv Hmaps Hna. pose proof Hwf as (Wm & Wn & Wl).
  assert (Hwf' : model_ivs_wf (with_vmmaps h' m)).
  { unfold model_ivs_wf. model_proj. rewrite Hmaps, Hna. split; [apply ivs_wf_cons; assumption | split; assumption]. }
  rewrite (vm_backing_used_sem _ Hwf'), (vm_backing_used_sem _ Hwf). model_proj. rewrite Hmaps, Hna.
  cbn [sum_count]. pose proof (iv_count_le_size (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (a, n)).
  unfold ivS in H. cbn [snd] in H. lia.
Qed.

Lemma used_none_cons_le : ltac2:(tb__ "0|3|
S21S29S1Q40A1M0G0S3bR4A1S3cS13G0G0R3R2A4A1SaS10S11G0G0A2M1A1M2S22R5A1S17G1S13G0G0R4R3A4S22S23R6A1A1A3A3SaG2S26R6A1S17G1S13G0G0R5R4A4S26S23R7A1A1A3A3S2S24S28R7R8A2A1S24R8A1A2F_;F_;F_;F_;Fn;Fa;Fh';Fm;").
Proof.
  intros m h' a n Hwf Hiv Hmaps Hna. pose proof Hwf as (Wm & Wn & Wl).
  assert (Hwf' : model_ivs_wf (with_vmmaps h' m)).
  { unfold model_ivs_wf. model_proj. rewrite Hmaps, Hna. split; [apply ivs_wf_cons; assumption | split; [apply ivs_wf_cons; assumption | assumption]]. }
  rewrite (vm_backing_used_sem _ Hwf'), (vm_backing_used_sem _ Hwf). model_proj. rewrite Hmaps, Hna.
  cbn [sum_count app]. rewrite (iv_count_covered_zero ((a, n) :: vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) (a, n)) by (left; reflexivity).
  pose proof (sum_count_mono (fun x => negb (covered ((a, n) :: vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x))
                              (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (vm_maps (m_vmmaps m))) as M.
  lapply M; [intros; lia|]. intros x Hx. cbn [covered existsb app] in Hx |- *.
  apply negb_true_iff in Hx. apply orb_false_iff in Hx as [_ Hx]. apply negb_true_iff. exact Hx.
Qed.

Lemma used_add_lazy_le : ltac2:(tb__ "0|2|
S21S1Q40M0A1M1G1S3bR3A1S2S3S0G0R3A2S0G0R2A2A2S4Z2Z40A2A2S2S24S2eR4R3R5A3A1S24R5A1A2F_;F_;Fn;Fa;Fm;").
Proof.
  intros m a n Hwf Hend. pose proof Hwf as (Wm & Wn & Wl).
  pose proof (model_ivs_wf_vm_add_lazy a n m Hend Hwf) as Hwf'.
  rewrite (vm_backing_used_sem _ Hwf'), (vm_backing_used_sem _ Hwf). model_proj.
  apply Z.add_le_mono_r. apply sum_count_mono. intros x Hx.
  rewrite covered_app in Hx. rewrite covered_app. apply negb_true_iff in Hx. apply negb_true_iff.
  apply orb_false_iff in Hx as [H1 H2]. rewrite covered_app in H2. apply orb_false_iff in H2 as [_ H2]. rewrite H1, H2. reflexivity.
Qed.

Lemma used_rw_noreserve_le : ltac2:(tb__ "0|6|
S21S29S1Q40M0A1M1G1S3bR4A1SaSfS7S0G0R3A2S2bA2Z0M2A3M3G3S5G2S0G0R4A2A2S2S3S0G0R6A2S0G0R5A2A2S4Z2Z40A2A2SaS10S11G1G1A2M4A1M5S22R8A1S17G4S13G1G1R7R6A4S22S23R9A1A1A3A3SaG5S26R9A1S26S23RaA1A1A3S2S24S2eR9R8S28RaRbA2A3A1S24RbA1A2F_;F_;F_;F_;F_;F_;F_;Fn;Fa;Fh';Fm;").
Proof.
  intros m h' a n Hwf Hal Hnl Hpos Hend Hmaps Hna. pose proof Hwf as (Wm & Wn & Wl).
  pose proof (lazy_interior_aligned a n Hal Hnl Hpos Hend) as Hli.
  assert (Hwf1 : model_ivs_wf (with_vmmaps h' m)).
  { unfold model_ivs_wf. model_proj. rewrite Hmaps, Hna. split; [apply ivs_wf_cons; [exact Hend|assumption] | split; assumption]. }
  pose proof (model_ivs_wf_vm_add_lazy a n _ Hend Hwf1) as Hwf'.
  rewrite (vm_backing_used_sem _ Hwf'), (vm_backing_used_sem _ Hwf). model_proj. rewrite Hmaps, Hna, Hli.
  cbn [sum_count app].
  assert (Z0 : iv_count (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ (a, n) :: m_vm_lazy m) x)) (a, n) = 0).
  { apply iv_count_covered_zero. apply in_or_app. right. left. reflexivity. }
  rewrite Z0.
  pose proof (sum_count_mono (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ (a, n) :: m_vm_lazy m) x))
                              (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (vm_maps (m_vmmaps m))) as M.
  lapply M; [intros; lia|]. intros x Hx. rewrite !covered_app in Hx |- *. cbn [covered existsb] in Hx |- *.
  apply negb_true_iff in Hx. apply negb_true_iff. apply orb_false_iff in Hx as [H1 H2]. apply orb_false_iff in H2 as [_ H2].
  rewrite H1. exact H2.
Qed.

Lemma unpaid_ext : ltac2:(tb__ "0|2|
S21S21S10S1Q40A1M0A1M1SaS10S11G0G0A2A1S25R2A1S25R3A1A3SaG1S2fR3A1S2fR4A1A3SaG1S43R4R3A2S43R5R3A2A3F_;F_;Ftp;Fmd';Fmd;").
Proof. intros md md' tp Hl Hm. unfold unpaid. rewrite Hl, Hm. reflexivity. Qed.

Lemma hid_ext : ltac2:(tb__ "0|1|
S21S21S10S1Q40A1M0A1SaS10S11G0G0A2A1S25R2A1S25R3A1A3SaG0S12Fa;S41R3R2A2S41R4R2A2A3F_;Ftp;Fmd';Fmd;").
Proof. intros md md' tp Hl. unfold hid. rewrite Hl. reflexivity. Qed.

Lemma paid_with_vmmaps : ltac2:(tb__ "0|1|
S29S21S10S1Q40A1A1SaSfS46S28R3R2A2M0R1A2S3S46R2R1A2S8S24G0A1S24R2A1A2A2A3Ftp;Fm;Fh';").
Proof. intros h' m tp. unfold paid. rewrite (unpaid_ext m (with_vmmaps h' m) tp) by reflexivity. lia. Qed.

Lemma page_in_ranges_app : ltac2:(tb__ "0|3|
S1Q40A1M0S10S11G0G0A2M1A1M2G2SaS12S2dR3S19G1R2R1A3A2S20S2dR3R2A2S2dR3R1A2A2A3Fl2;Fl1;Fp;").
Proof. intros. unfold page_in_ranges. apply existsb_app. Qed.

Definition page_in_range (p : word) (r : word * word) : bool := ltac2:(tb__ "0|4|
S1bS6S0Q40M0S14S1G0A1M1G1Vr;A3A2M2S0G0Vp;A2M3A2S6S3G3S2bA2S3G2S0G0S15G1G1Vr;A3A2A2A2A2").

Lemma page_in_ranges_eq : ltac2:(tb__ "0|2|
S1Q40A1M0S10S11G0G0A2M1A1SaS12S2dR2R1A2S38G1S4aR2A1R1A3A3Fl;Fp;").
Proof. intros. reflexivity. Qed.

Definition tp_clear_of (tp : list word) (L : list (word * word)) : Prop := ltac2:(tb__ "0|1|
S1Q40A1M0S36G0R1Vtp;A3SaS12S2dR2VL;A2S18A3F_;Fp;").

Lemma unpaid_add_lazy : ltac2:(tb__ "0|2|
S21S1Q40A1M0G0S10G0A1M1S49R1S2cR3R2A2A2SaG1S43S2eR4R3R5A3R2A2S43R5R2A2A3F_;Ftp;Fn;Fa;Fm;").
Proof.
  intros m a n tp Hclr. unfold unpaid. model_proj. apply filter_ext_in. intros p Hp.
  rewrite page_in_ranges_app, (Hclr p Hp). reflexivity.
Qed.

Lemma paid_add_lazy : ltac2:(tb__ "0|2|
S21S1Q40A1M0G0S10G0A1S49R1S2cR3R2A2A2SaSfS46S2eR4R3R5A3M1R2A2S3S46R5R2A2S8S24G1A1S24R5A1A2A2A3F_;Ftp;Fn;Fa;Fm;").
Proof. intros m a n tp H. unfold paid. rewrite (unpaid_add_lazy m a n tp H). lia. Qed.

Lemma hid_add_lazy : ltac2:(tb__ "0|2|
S21S1Q40A1M0G0S10G0A1G0SaS12S41S2eR4R3R5A3R2R1A3S20S41R5R2R1A3S1bS2dS30R1A1M1S2cR4R3A2A2S1dS34G1R2A2A1A2A2A3Fx;Ftp;Fn;Fa;Fm;").
Proof.
  intros m a n tp x. unfold hid. model_proj. rewrite page_in_ranges_app.
  destruct (page_in_ranges (page_base x) (lazy_interior a n)), (page_in_ranges (page_base x) (m_vm_lazy m)), (page_mem (page_base x) tp); reflexivity.
Qed.

Lemma tp_clear_of_interior : ltac2:(tb__ "0|5|
S10S1Q40M0A1M1A1G1G1G1S36G1R1R4A3SdS2S3S0G0R2A2M2S2bA2S0G0R4A2M3A2S2S3G3S0G0R3A2M4A2G2A2A2F_;Fp;S2S3G4G2A2S4Z2Z40A2A2S49R5S2cR4R3A2A2F_;F_;Fn;Fa;Ftp;").
Proof.
  intros tp a n H Hend p Hp. pose proof (H p Hp) as D. unfold lazy_interior. cbv zeta.
  pose proof (urange a) as Ra. pose proof (urange n) as Rn. pose proof (urange p) as Rp. pose proof page_size_pos as Pps.
  destruct (_ <? _) eqn:E; [|reflexivity]. apply Z.ltb_lt in E.
  rewrite page_in_ranges_eq. cbn [existsb]. rewrite orb_false_r.
  set (lo' := (bv_unsigned a + page_size - 1) / page_size * page_size) in *.
  set (hi' := (bv_unsigned a + bv_unsigned n) / page_size * page_size) in *.
  assert (Hlo : bv_unsigned a <= lo').
  { unfold lo'. pose proof (Z.div_mod (bv_unsigned a + page_size - 1) page_size ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned a + page_size - 1) page_size ltac:(lia)). lia. }
  assert (Hhi : hi' <= bv_unsigned a + bv_unsigned n).
  { unfold hi'. pose proof (Z.div_mod (bv_unsigned a + bv_unsigned n) page_size ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned a + bv_unsigned n) page_size ltac:(lia)). lia. }
  assert (Hlo0 : 0 <= lo') by (unfold lo'; apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia|lia]).
  unfold page_in_range. cbn [fst snd]. rewrite !fg_lit by lia.
  apply andb_false_iff. destruct D as [D|D]; [left; apply Z.leb_gt | right; apply Z.leb_gt]; lia.
Qed.

Lemma page_in_range_spec : ltac2:(tb__ "0|4|
S1Q40M0A1M1S11G1G1A2SeSaS12S4aR2R1A2S16A3SbS2S0G0S14G1G1R1A3A2M2S0G0R2A2M3A2S2S3G3S2bA2S3G2S0G0S15G1G1R1A3A2A2A2A2A2Fr;Fp;").
Proof.
  intros p [lo sz]. unfold page_in_range. cbn [fst snd]. rewrite andb_true_iff, !Z.leb_le. tauto.
Qed.

Lemma page_in_ranges_spec : ltac2:(tb__ "0|2|
S1Q40A1M0S10S11G0G0A2M1A1SeSaS12S2dR2R1A2S16A3ScG1G1SbS36G1R1R2A3SaS12S4aR3R1A2S16A3A2Lr;A2A2Fl;Fp;").
Proof. intros p l. rewrite page_in_ranges_eq. rewrite existsb_exists. tauto. Qed.

Lemma in_iv_subtract : ltac2:(tb__ "0|6|
S11S1Q40M0A1M1G1A2M2G1G1SfSfS36G2R5S33R4R3R2R1A4A3S3cS13G1G1R5R4A4A1SbS2S0G0R6A2M3S0G0S14G1G1R7A3A2M4A2SbS2S3G4S0G0S15G1G1R7A3A2A2M5S3G3S0G0R5A2A2A2SdS2G5R4A2S2R3G4A2A2A2A2F_;F_;Fhi;Flo;Fsz;Fa;Fq;").
Proof.
  intros q a sz lo hi Hin Hwf. unfold iv_wf, ivB, ivS in Hwf. cbn [fst snd] in Hwf.
  pose proof (urange a) as Ra. pose proof (urange sz) as Rs.
  unfold iv_subtract in Hin. cbv zeta in Hin. apply in_app_or in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite fg_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite !fg_lit by lia. lia.
Qed.

Lemma in_maps_subtract : ltac2:(tb__ "0|6|
S11S1Q40M0A1M1G1A2M2S10G2A1SfSfS36G2R4S2aR3R2R1A3A3S3aR4A1ScG2G2SbS36G2R1R6A3SbS2S0G0S14G1G1R1A3A2M3S0G0S14G1G1R7A3A2M4A2SbS2S3G4S0G0S15G1G1R7A3A2A2M5S3G3S0G0S15G1G1R1A3A2A2A2SdS2G5R5A2S2R4G4A2A2A2A2A2Lr;A2F_;F_;Fhi;Flo;Fl;Fq;").
Proof.
  intros q l lo hi. induction l as [|[a sz] l IH]; intros Hin Hwf; [destruct Hin|].
  cbn [maps_subtract] in Hin. apply ivs_wf_cons_inv in Hwf as [Ha Hl]. apply in_app_or in Hin as [Hin|Hin].
  - exists (a, sz). split; [left; reflexivity|]. cbn [fst snd]. exact (in_iv_subtract q a sz lo hi Hin Ha).
  - destruct (IH Hin Hl) as (r & Hr & X). exists r. split; [right; exact Hr | exact X].
Qed.

Lemma unpaid_forget_incl : ltac2:(tb__ "0|1|
S21SfSfS10S1Q40A1M0A1G0S3aS25R5A1A1S36G0R2S43S27R5R4R6A3R3A2A3S36G0R3S43R7R4A2A3F_;F_;Fp;Ftp;Fhi;Flo;Fm;").
Proof.
  intros m lo hi tp p Hwf Hp. unfold unpaid in Hp |- *. model_proj. rewrite filter_In in Hp |- *.
  destruct Hp as [Htp Hb]. split; [exact Htp|]. apply andb_prop in Hb as [Hl Hm].
  apply page_in_ranges_spec in Hl as (q & Hq & Hpq).
  destruct (in_maps_subtract q _ lo hi Hq Hwf) as (r & Hr & H1 & H2 & H3).
  apply page_in_range_spec in Hpq as [P1 P2].
  apply andb_true_intro. split.
  - apply page_in_ranges_spec. exists r. split; [exact Hr|]. apply page_in_range_spec. lia.
  - apply negb_true_iff in Hm. apply negb_true_iff. rewrite page_mem_false in Hm |- *. intros Hin. apply Hm.
    apply filter_In. split; [exact Hin|]. unfold page_outside_range.
    pose proof page_size_pos. apply negb_true_iff. apply andb_false_iff.
    destruct H3 as [H3|H3]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
Qed.

Lemma unpaid_forget_le : ltac2:(tb__ "0|1|
S21SfSfS10S1Q40A1M0A1S3aS25R4A1A1S37G0R2A2S4eS1cG0S43S27R5R4R6A3R3A2A2S1cG0S43R6R3A2A2A2F_;F_;Ftp;Fhi;Flo;Fm;").
Proof.
  intros m lo hi tp Hwf Hnd. apply List.NoDup_incl_length.
  - unfold unpaid. apply List.NoDup_filter. exact Hnd.
  - intros p Hp. exact (unpaid_forget_incl m lo hi tp p Hwf Hp).
Qed.

Lemma hid_forget_false : ltac2:(tb__ "0|1|
S21SfSfS10S1Q40A1M0A1G0S3aS25R5A1A1SaS12S41R6R3R2A3S18A3SaS12S41S27R6R5R7A3R4R3A3S18A3F_;F_;Fx;Ftp;Fhi;Flo;Fm;").
Proof.
  intros m lo hi tp x Hwf H. unfold hid in H |- *. model_proj.
  destruct (page_mem (page_base x) tp); [rewrite andb_false_r; reflexivity|]. rewrite andb_true_r in H |- *.
  destruct (page_in_ranges (page_base x) (maps_subtract (m_vm_lazy m) lo hi)) eqn:E; [|reflexivity]. exfalso.
  apply page_in_ranges_spec in E as (q & Hq & Hpq).
  destruct (in_maps_subtract q _ lo hi Hq Hwf) as (r & Hr & H1 & H2 & _).
  apply page_in_range_spec in Hpq as [P1 P2].
  assert (X : page_in_ranges (page_base x) (m_vm_lazy m) = true); [|congruence].
  apply page_in_ranges_spec. exists r. split; [exact Hr|]. apply page_in_range_spec. lia.
Qed.

Lemma hid_forget_true : ltac2:(tb__ "0|3|
S21SfSfS10S1Q40M0A1M1A1G1S3aS25R5A1A1SaS12S41S27R5R4R6A3R3R2A3S16A3SbSaS12S41R7R4R3A3S16A3SdS2S3S0G0S30R3A1A2M2S2bA2R6A2S2R5G2A2A2A2F_;F_;Fx;Ftp;Fhi;Flo;Fm;").
Proof.
  intros m lo hi tp x Hwf H. unfold hid in H |- *. revert H. model_proj. intros H.
  apply andb_prop in H as [Hl Hm]. rewrite Hm, andb_true_r.
  apply page_in_ranges_spec in Hl as (q & Hq & Hpq).
  destruct (in_maps_subtract q _ lo hi Hq Hwf) as (r & Hr & H1 & H2 & H3).
  apply page_in_range_spec in Hpq as [P1 P2]. split.
  - apply page_in_ranges_spec. exists r. split; [exact Hr|]. apply page_in_range_spec. lia.
  - pose proof page_size_pos. lia.
Qed.

Lemma iv_subtract_keeps : ltac2:(tb__ "0|5|
S1Q40M0A1M1G1SfSfSfSfS3cS13G1G1R6R5A4A1S2R5R4A2S2S0G0R8A2M2R4A2S2R4S3S0G0R9A2G2A2A2S5R6R5A2SdS2R6R9A2S2R8R7A2A2ScS11G1G1A2M3G3SbS36G3R1S33RdRcRbRaA4A3SbS2S0G0S14G1G1R1A3A2M4R9A2S2R8S3G4S0G0S15G1G1R1A3A2A2A2A2A2Lr;A2F_;F_;F_;F_;F_;F_;Fq;Fp;Fhi;Flo;Fsz;Fa;").
Proof.
  intros a sz lo hi p q Hwf Hlh H1 H2 H3 H4. unfold iv_wf, ivB, ivS in Hwf. cbn [fst snd] in Hwf.
  pose proof (urange a) as Ra. pose proof (urange sz) as Rs.
  unfold iv_subtract. cbv zeta. destruct H4 as [H4|H4].
  - destruct (bv_unsigned a <? lo) eqn:El; [|apply Z.ltb_ge in El; lia].
    exists (a, Z_to_bv 64 (Z.min (bv_unsigned sz) (lo - bv_unsigned a))). split; [apply in_or_app; left; left; reflexivity|].
    cbn [fst snd]. rewrite fg_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Er; [|apply Z.ltb_ge in Er; lia].
    eexists. split; [apply in_or_app; right; left; reflexivity|]. cbn [fst snd]. rewrite !fg_lit by lia. lia.
Qed.

Lemma maps_subtract_keeps : ltac2:(tb__ "0|4|
S10S11S1Q40M0A1M1G1A2M2A1SfSfG2SfSfS3aR6A1S2R6R5A2S36G2R5R8A3S2S0G0S14G1G1R6A3A2R5A2S2R5S3S0G0S14G1G1R7A3A2S0G0S15G1G1R7A3A2A2A2S5R7R6A2SdS2R7RbA2S2RaR8A2A2ScG2G2SbS36G2R1S2aReRdRcA3A3SbS2S0G0S14G1G1R1A3A2M3RaA2S2R9S3G3S0G0S15G1G1R1A3A2A2A2A2A2Lr';A2F_;F_;F_;F_;F_;F_;F_;Fq;Fp;Fr;Fhi;Flo;Fl;").
Proof.
  intros l lo hi r p q Hwf Hlh Hin H1 H2 H3 H4. induction l as [|[a sz] l IH]; [destruct Hin|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract].
  destruct Hin as [<-|Hin].
  - cbn [fst snd] in H1, H2. destruct (iv_subtract_keeps a sz lo hi p q Ha Hlh H1 H2 H3 H4) as (r' & Hr' & X).
    exists r'. split; [apply in_or_app; left; exact Hr' | exact X].
  - destruct (IH Hl Hin) as (r' & Hr' & X). exists r'. split; [apply in_or_app; right; exact Hr' | exact X].
Qed.

Lemma hid_forget_in_range : ltac2:(tb__ "0|2|
S21SfSfS10S1Q40M0A1M1A1G1S3aS25R5A1A1S2R5S0G0S30R2A1A2A2S2S3S0G0S30R3A1A2S2bA2R5A2SaS12S41S27R7R6R8A3R5R4A3S18A3F_;F_;F_;Fx;Ftp;Fhi;Flo;Fm;").
Proof.
  intros m lo hi tp x Hwf H1 H2. unfold hid. model_proj.
  destruct (page_in_ranges (page_base x) (maps_subtract (m_vm_lazy m) lo hi)) eqn:E; [|reflexivity]. exfalso.
  apply page_in_ranges_spec in E as (q & Hq & Hpq).
  destruct (in_maps_subtract q _ lo hi Hq Hwf) as (r & Hr & Q1 & Q2 & Q3).
  apply page_in_range_spec in Hpq as [P1 P2]. pose proof page_size_pos. lia.
Qed.

Lemma hid_forget_outside : ltac2:(tb__ "0|3|
S21SfSfS10S1Q40M0A1M1A1G1S3aS25R5A1A1S2R5R4A2SdS2S3S0G0S30R3A1A2M2S2bA2R6A2S2R5G2A2A2SaS12S41S27R7R6R8A3R5R4A3S41R8R5R4A3A3F_;F_;F_;Fx;Ftp;Fhi;Flo;Fm;").
Proof.
  intros m lo hi tp x Hwf Hlh Hout. destruct (hid m tp x) eqn:E; [|apply hid_forget_false; assumption].
  unfold hid in E |- *. model_proj. apply andb_prop in E as [Hl Hm]. rewrite Hm, andb_true_r.
  apply page_in_ranges_spec in Hl as (r & Hr & Hpr). apply page_in_range_spec in Hpr as [P1 P2].
  pose proof page_size_pos.
  destruct (maps_subtract_keeps (m_vm_lazy m) lo hi r (bv_unsigned (page_base x)) (bv_unsigned (page_base x) + page_size) Hwf Hlh Hr P1 P2 ltac:(lia) Hout)
    as (r' & Hr' & X1 & X2).
  apply page_in_ranges_spec. exists r'. split; [exact Hr'|]. apply page_in_range_spec. lia.
Qed.

Lemma overlap_sum_split_le : ltac2:(tb__ "0|6|
S10S11S1Q40M0A1M1G1A2M2A1M3G2G3G1G1SaS12S32S19G2R5R3A3R2R1A3S16A3S2S3eS19G2R6S17G2R5R4A3A3S0G0R3A2M4S3G4S0G0R2A2M5A2A3G5A2F_;Fn;Fa;Fl2;Fr;Fl1;").
Proof.
  intros l1 r l2 a n Hfree. pose proof (urange n).
  rewrite overlap_sum_app, overlap_sum_cons.
  pose proof (overlap_sum_region_free (l1 ++ l2) a n Hfree) as Z0. rewrite overlap_sum_app in Z0.
  pose proof (iv_count_in_rng_le r (bv_unsigned a) (bv_unsigned a + bv_unsigned n) ltac:(lia)).
  pose proof (sum_count_nonneg (in_rng (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) l1).
  pose proof (sum_count_nonneg (in_rng (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) l2).
  unfold overlap_sum in *. lia.
Qed.

Lemma used_commit_le : ltac2:(tb__ "0|6|
S21S29S1Q40M0A1M1G1S3bR4A1SaS10S11G1G1A2A1M2S22R4A1S22S23R5A1A1A3SaG2S26R5A1S2aS26S23R6A1A1S0G0R4A2M3S3G3S0G0R3A2A2A3A3S2S24S27S0G0R5A2M4S3G4G3A2M5S28R6R7A2A3A1S3S24R7A1S3eS22S23R7A1A1G4G5A3A2A2F_;F_;F_;Fn;Fa;Fh';Fm;").
Proof.
  intros m h' a n Hwf Hmaps Hna. pose proof (urange n).
  apply backing_forget_commit_le; [exact Hwf | lia | exact Hmaps | exact Hna].
Qed.

Lemma used_destroy_le : ltac2:(tb__ "0|2|
S21S29SfSfS3bR4A1S2R3R2A2SaS10S11S1Q40A1M0G0A2A1M1S22R5A1S2aS22S23R6A1A1R4R3A3A3SaG1S26R6A1S2aS26S23R7A1A1R5R4A3A3S2S24S27R6R5S28R7R8A2A3A1S24R8A1A2F_;F_;F_;F_;Fhi;Flo;Fh';Fm;").
Proof.
  intros m h' lo hi Hwf Hlh Hmaps Hna. pose proof Hwf as (Wm & Wn & Wl).
  destruct (maps_subtract_sem _ lo hi Wm Hlh) as (Wm' & Sm & _).
  destruct (maps_subtract_sem _ lo hi Wn Hlh) as (Wn' & _ & Cn).
  destruct (maps_subtract_sem _ lo hi Wl Hlh) as (Wl' & _ & Cl).
  assert (Hwf' : model_ivs_wf (vm_forget_range lo hi (with_vmmaps h' m))).
  { unfold model_ivs_wf. model_proj. rewrite Hmaps, Hna. split; [exact Wm' | split; [exact Wn' | exact Wl']]. }
  rewrite (vm_backing_used_sem _ Hwf'), (vm_backing_used_sem _ Hwf). model_proj. rewrite Hmaps, Hna.
  pose proof (filter_length_le (page_outside_range lo hi) (m_vm_materialized m)). pose proof page_size_pos.
  apply Z.add_le_mono; [|nia].
  rewrite Sm. apply sum_count_mono. intros x Hx. apply andb_prop in Hx as [Hx Hr].
  rewrite covered_app in Hx. rewrite Cn, Cl, Hr in Hx. rewrite covered_app.
  rewrite !andb_true_r in Hx. exact Hx.
Qed.

Lemma lazy_in_maps_destroy : ltac2:(tb__ "0|1|
SfSfS21S29S3bR2A1S2R5R4A2S42R4A1SaS10S11S1Q40A1M0G0A2A1S22R4A1S2aS22S23R5A1A1R7R6A3A3S42S27R8R7S28R5R6A2A3A1F_;F_;F_;F_;Fh';Fm;Fhi;Flo;").
Proof.
  intros lo hi m h' (Wm & _ & Wl) Hlh H Hmaps lz sz Hin Hsz. unfold lazy_in_maps in H. model_proj.
  rewrite m_vm_lazy_vm_forget_range, m_vm_lazy_with_vmmaps in Hin. rewrite Hmaps.
  destruct (in_maps_subtract (lz, sz) _ lo hi Hin Wl) as ([b s] & Hr & H1 & H2 & H3). cbn [fst snd] in H1, H2, H3.
  pose proof (urange lz).
  destruct (H b s Hr ltac:(lia)) as (b' & s' & Hbs & X1 & X2).
  destruct (maps_subtract_keeps (vm_maps (m_vmmaps m)) lo hi (b', s') (bv_unsigned lz) (bv_unsigned lz + bv_unsigned sz) Wm Hlh Hbs ltac:(cbn [fst snd]; lia) ltac:(cbn [fst snd]; lia) ltac:(lia) H3)
    as ([b2 s2] & Hr2 & Y1 & Y2). cbn [fst snd] in Y1, Y2.
  exists b2, s2. split; [exact Hr2 | lia].
Qed.

Lemma tp_in_maps_destroy : ltac2:(tb__ "0|6|
S1Q40M0A1M1G1S21S29S10G1A1S3bR3A1S47R4R2A2SaSfS7S0G0R7A2S2bA2Z0A3M2G2SaS10S11G1G1A2A1S22R6A1S2aS22S23R7A1A1S0G0R9A2M3S3G3S0G0R8A2A2A3A3S47S27S0G0RaA2M4S3G4G3A2M5S28R7R8A2A3S39G1S35G4G5A2R6A3A2F_;F_;F_;F_;F_;Ftp;Fh';Fm;Fn;Fa;").
Proof.
  intros a n m h' tp (Wm & _ & _) Htm Hal Hnl Hmaps p Hp. model_proj. rewrite Hmaps.
  apply filter_In in Hp as [Hp Hout]. destruct (Htm p Hp) as (Hpal & b & s & Hbs & B1 & B2). split; [exact Hpal|].
  pose proof page_size_pos. pose proof (urange n). pose proof (urange a). pose proof (urange p).
  unfold page_outside_range in Hout. apply negb_true_iff in Hout. apply andb_false_iff in Hout.
  assert (Hclear : bv_unsigned p + page_size <= bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned p).
  { pose proof (Z.div_mod (bv_unsigned a) page_size ltac:(lia)) as Da. rewrite Hal in Da.
    pose proof (Z.div_mod (bv_unsigned n) page_size ltac:(lia)) as Dn. rewrite Hnl in Dn.
    pose proof (Z.div_mod (bv_unsigned p) page_size ltac:(lia)) as Dp. rewrite Hpal in Dp.
    destruct Hout as [Hout|Hout]; [apply Z.leb_gt in Hout; left | apply Z.ltb_ge in Hout; right; exact Hout].
    assert (bv_unsigned p / page_size < bv_unsigned a / page_size) by nia. nia. }
  destruct (maps_subtract_keeps (vm_maps (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (b, s)
              (bv_unsigned p) (bv_unsigned p + page_size) Wm ltac:(lia) Hbs B1 B2 ltac:(lia) Hclear) as ([b2 s2] & Hr2 & Y1 & Y2).
  cbn [fst snd] in Y1, Y2. exists b2, s2. split; [exact Hr2 | lia].
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma lazy_clear_app : ltac2:(tb__ "0|4|
S10S11S1Q40A1M0G0A2M1A1M2G2S45Vsegs;R2A2M3G3S45Vsegs;S19G1R4R3A3A2F_;F_;Fl2;Fl1;").
Proof. intros l1 l2 H1 H2 lo sz z Hin Hz. apply in_app_or in Hin as [Hin|Hin]; [eapply H1 | eapply H2]; eauto. Qed.

Lemma lazy_clear_interior : ltac2:(tb__ "0|4|
S1Q40M0A1M1G1SfSbS2S0G0R3A2M2R1A2S5R1S3G2S0G0R2A2A2M3A2A2SaS1fS4bA1S4cVsegs;R2Z1A3S1aS4bA1A3F_;Fz;S2G3S4Z2Z40A2A2S45Vsegs;S2cR4R3A2A2F_;F_;Fn;Fa;").
Proof.
  intros a n H Hend lo sz z Hin Hz. unfold lazy_interior in Hin. cbv zeta in Hin.
  pose proof (urange a) as Ra. pose proof (urange n) as Rn. pose proof page_size_pos as Pps.
  destruct (_ <? _) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [Heq|[]].
  injection Heq as <- <-.
  set (lo' := (bv_unsigned a + page_size - 1) / page_size * page_size) in *.
  set (hi' := (bv_unsigned a + bv_unsigned n) / page_size * page_size) in *.
  assert (Hlo : bv_unsigned a <= lo').
  { unfold lo'. pose proof (Z.div_mod (bv_unsigned a + page_size - 1) page_size ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned a + page_size - 1) page_size ltac:(lia)). lia. }
  assert (Hhi : hi' <= bv_unsigned a + bv_unsigned n).
  { unfold hi'. pose proof (Z.div_mod (bv_unsigned a + bv_unsigned n) page_size ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned a + bv_unsigned n) page_size ltac:(lia)). lia. }
  assert (Hlo0 : 0 <= lo') by (unfold lo'; apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia|lia]).
  rewrite !fg_lit in Hz by lia. apply H. lia.
Qed.

Lemma lazy_clear_pieces : ltac2:(tb__ "0|1|
S10S11S1Q40A1M0G0A2A1SfSfS3aR3A1S45Vsegs;R4A2S45Vsegs;S2aR5R4R3A3A2F_;F_;Fhi;Flo;Fl;").
Proof.
  intros l lo hi Hwf H lo0 sz z Hin Hz.
  destruct (in_maps_subtract (lo0, sz) l lo hi Hin Hwf) as ([b s] & Hr & H1 & H2 & _). cbn [fst snd] in H1, H2.
  eapply H; [exact Hr|]. lia.
Qed.

Lemma lazy_in_maps_with_vmmaps_grow : ltac2:(tb__ "0|2|
S29S21S42R1A1S11S1Q40A1M0G0A2M1S36G1R1S22S23R3A1A1A3S36G1R2S22R5A1A3F_;Fr;S42S28R4R3A2A1F_;F_;Fm;Fh';").
Proof.
  intros h' m H Hsub lo sz Hin Hsz. unfold lazy_in_maps in H. cbn in Hin |- *.
  destruct (H lo sz Hin Hsz) as (b & s & Hbs & X). exists b, s. split; [apply Hsub; exact Hbs | exact X].
Qed.

Lemma lazy_in_maps_add_lazy : ltac2:(tb__ "0|4|
S1Q40M0A1M1G1S21S42R1A1S2S3S0G0R4A2S0G0R3A2A2S4Z2Z40A2A2ScG1G1ScG1G1SbS36S11G1G1A2S13G1G1R2R1A4S22S23R5A1A1A3SbS2S0G0R2A2M2S0G0R7A2M3A2S2S3G3S0G0R6A2A2S3G2S0G0R1A2A2A2A2A2Ls;A2Lb;A2S42S2eR6R5R4A3A1F_;F_;F_;Fm;Fn;Fa;").
Proof.
  intros a n m H Hend (b & s & Hbs & Hb1 & Hb2) lo sz Hin Hsz. unfold lazy_in_maps in H.
  rewrite m_vm_lazy_vm_add_lazy in Hin. rewrite m_vmmaps_vm_add_lazy.
  apply in_app_or in Hin as [Hin|Hin]; [|exact (H lo sz Hin Hsz)].
  exists b, s. split; [exact Hbs|].
  unfold lazy_interior in Hin. cbv zeta in Hin.
  pose proof (urange a) as Ra. pose proof (urange n) as Rn. pose proof page_size_pos as Pps.
  destruct (_ <? _) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [Heq|[]]. injection Heq as <- <-.
  set (lo' := (bv_unsigned a + page_size - 1) / page_size * page_size) in *.
  set (hi' := (bv_unsigned a + bv_unsigned n) / page_size * page_size) in *.
  assert (Hlo : bv_unsigned a <= lo').
  { unfold lo'. pose proof (Z.div_mod (bv_unsigned a + page_size - 1) page_size ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned a + page_size - 1) page_size ltac:(lia)). lia. }
  assert (Hhi : hi' <= bv_unsigned a + bv_unsigned n).
  { unfold hi'. pose proof (Z.div_mod (bv_unsigned a + bv_unsigned n) page_size ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned a + bv_unsigned n) page_size ltac:(lia)). lia. }
  assert (Hlo0 : 0 <= lo') by (unfold lo'; apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia|lia]).
  rewrite !fg_lit by lia. lia.
Qed.

Lemma lazy_in_maps_forget : ltac2:(tb__ "0|0|
SfSfS21S3aS25R1A1A1S42R2A1S42S27R5R4R3A3A1F_;F_;Fm;Fhi;Flo;").
Proof.
  intros lo hi m Hwf H lo0 sz Hin Hsz. unfold lazy_in_maps in H. model_proj. rewrite m_vm_lazy_vm_forget_range in Hin.
  destruct (in_maps_subtract (lo0, sz) _ lo hi Hin Hwf) as ([b s] & Hr & H1 & H2 & _). cbn [fst snd] in H1, H2.
  pose proof (urange lo0).
  destruct (H b s Hr ltac:(lia)) as (b' & s' & Hbs & X1 & X2). exists b', s'. split; [exact Hbs|]. lia.
Qed.

Lemma hid_false_of_region_free : ltac2:(tb__ "0|4|
S21S10S1Q40M0A1M1A1G1G1G1S42R5A1S3bR6A1SaS12S32S22S23R7A1A1R5R4A3S16A3SbS2S0G0R6A2M2S0G0R4A2M3A2S5G3S3G2S0G0R5A2A2A2A2SaS12S41R9R8R5A3S18A3F_;F_;F_;F_;Fx;Fn;Fa;Ftp;Fmd;").
Proof.
  intros md tp a n x Hlm (Wm & _ & Wl) Hfree Hx. unfold hid.
  destruct (page_in_ranges (page_base x) (m_vm_lazy md)) eqn:E; [|reflexivity]. exfalso.
  apply page_in_ranges_spec in E as ([lo sz] & Hin & Hp). apply page_in_range_spec in Hp as [P1 P2]. cbn [fst snd] in P1, P2.
  pose proof page_size_pos. pose proof (urange (page_base x)).
  destruct (Hlm lo sz Hin ltac:(lia)) as (b & s & Hbs & B1 & B2).
  pose proof (page_base_range x) as [X1 X2].

  clear Hin. induction (vm_maps (m_vmmaps md)) as [|[b0 s0] l IH]; [destruct Hbs|].
  cbn [region_free] in Hfree. apply andb_true_iff in Hfree as [H1 H2].
  destruct Hbs as [Heq|Hbs]; [|apply IH; [intros q Hq; apply Wm; right; exact Hq | exact H2 | exact Hbs]].
  injection Heq as -> ->. apply negb_true_iff in H1. unfold iv_overlap in H1. cbn [fst snd] in H1.
  apply andb_false_iff in H1 as [H1|H1]; apply Z.ltb_ge in H1; lia.
Qed.

Lemma MI_with_vmmaps : ltac2:(tb__ "0|2|
S21S29S10S1Q40A1M0A1SfS44Vsegs;R4R2A3SaSfS31R4A1S31S23R5A1A1A3S3aS22R5A1A1S3aS26R6A1A1S11G0G0A2M1S36G1R1S22S23R9A1A1A3S36G1R2S22R9A1A3F_;Fr;S2S24S28R8R9A2A1S3S24R9A1R6A2A2S9S48RaR8A2R7A2S44Vsegs;S28RaRbA2R9A3F_;F_;F_;F_;F_;F_;F_;Fk;Ftp;Fh';Fmd;").
Proof.
  intros md h' tp k (HW & HT & Hmat & Hsub & Hpaid & Hlc & Hivs & Hlm & Htm) Hlim Hwm Hwn Hgrow Hused Hroom.
  unfold MI. model_proj. split; [exact HW|]. split; [exact HT|]. split; [exact Hmat|]. split; [exact Hsub|].
  split; [|split; [exact Hlc | split; [apply model_ivs_wf_with_vmmaps; assumption | split; [apply lazy_in_maps_with_vmmaps_grow; assumption|]]]].
  - rewrite paid_with_vmmaps, Hlim. unfold headroom in Hroom. lia.
  - intros p Hp. destruct (Htm p Hp) as (Hal & b & s & Hbs & X). split; [exact Hal|]. exists b, s. split; [apply Hgrow; exact Hbs | exact X].
Qed.

Lemma MI_add_lazy : ltac2:(tb__ "0|5|
S21S1Q40M0A1M1G1S10G1A1S44Vsegs;R4R1A3S2S3S0G0R4A2S0G0R3A2A2S4Z2Z40A2A2S49R3S2cR5R4A2A2SfSbS2S0G0R7A2M2R1A2S5R1S3G2S0G0R6A2A2A2A2SaS1fS4bA1S4cVsegs;R2Z1A3S1aS4bA1A3F_;Fz;ScG1G1ScG1G1SbS36S11G1G1A2S13G1G1R2R1A4S22S23RaA1A1A3SbS2S0G0R2A2M3S0G0R9A2M4A2S2S3G4S0G0R8A2A2S3G3S0G0R1A2A2A2A2A2Ls;A2Lb;A2S44Vsegs;S2eR8R7R9A3R6A3F_;F_;F_;F_;F_;Ftp;Fn;Fa;Fmd;").
Proof.
  intros md a n tp HMI Hend Hclr Hseg Hin. pose proof HMI as (HW & HT & Hmat & Hsub & Hpaid & Hlc & Hivs & Hlm & Htm).
  unfold MI. rewrite m_vmmaps_vm_add_lazy, m_vm_materialized_vm_add_lazy, m_vm_lazy_vm_add_lazy.
  split; [exact HW|]. split; [exact HT|]. split; [exact Hmat|]. split; [exact Hsub|]. split.
  { rewrite (paid_add_lazy md a n tp Hclr). pose proof (used_add_lazy_le md a n Hivs Hend). lia. }
  split; [apply lazy_clear_app; [apply lazy_clear_interior; assumption | exact Hlc]|].
  split; [apply model_ivs_wf_vm_add_lazy; assumption | split; [apply lazy_in_maps_add_lazy; assumption | exact Htm]].
Qed.

Lemma MI_intro : ltac2:(tb__ "0|1|
S21S10S1Q40A1M0A1S4dVsegs;A1S37G0R2A2S37G0S2fR4A1A2G0S36G0R1S2fR6A1A3S36G0R2R6A3F_;Fp;S2S46R6R5A2S31S23R6A1A1A2S45Vsegs;S25R7A1A2S3bR8A1S42R9A1S47RaR9A2S44Vsegs;RbRaA3F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp;Fmd;").
Proof.
  intros. unfold MI. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Lemma MI_intro_nolazy : ltac2:(tb__ "0|3|
S21S4dVsegs;A1SaS10S11S1Q40A1M0G0A2M1A1S25R2A1S1eG1A1A3SaS10G0A1S2fR3A1S1eG0A1M2A3S2S24R4A1S31S23R4A1A1A2S3aS22S23R5A1A1A1S3aS26S23R6A1A1A1S44Vsegs;R7G2A3F_;F_;F_;F_;F_;F_;Fmd;").
Proof.
  intros md HW Hl Hm Hu Hwm Hwn. apply MI_intro.
  - exact HW.
  - constructor.
  - rewrite Hm. constructor.
  - rewrite Hm. intros p [].
  - unfold paid, unpaid. cbn. lia.
  - rewrite Hl. intros lo sz z [].
  - apply model_ivs_wf_intro; [exact Hwm | exact Hwn | rewrite Hl; apply ivs_wf_nil].
  - intros lo sz Hin. rewrite Hl in Hin. destruct Hin.
  - intros p [].
Qed.

Lemma tp_clear_of_region_free : ltac2:(tb__ "0|2|
S21S10S1Q40M0A1M1A1G1G1S47R4R3A2S3aS22S23R5A1A1A1SaS12S32S22S23R6A1A1R4R3A3S16A3S2S3S0G0R5A2S0G0R4A2A2S4Z2Z40A2A2S49R7S2cR6R5A2A2F_;F_;F_;F_;Fn;Fa;Ftp;Fmd;").
Proof.
  intros md tp a n Htm Hwf Hfree Hend. apply tp_clear_of_interior; [|exact Hend].
  intros p Hp. destruct (Htm p Hp) as (_ & b & s & Hbs & B1 & B2). pose proof page_size_pos.
  clear Htm Hp. induction (vm_maps (m_vmmaps md)) as [|[b0 s0] l IH]; [destruct Hbs|].
  cbn [region_free] in Hfree. apply andb_true_iff in Hfree as [H1 H2].
  destruct Hbs as [Heq|Hbs]; [|apply IH; [intros q Hq; apply Hwf; right; exact Hq | exact H2 | exact Hbs]].
  injection Heq as -> ->. apply negb_true_iff in H1. unfold iv_overlap in H1. cbn [fst snd] in H1.
  apply andb_false_iff in H1 as [H1|H1]; apply Z.ltb_ge in H1; lia.
Qed.

End WithSegs.
