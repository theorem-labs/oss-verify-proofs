(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase State Monad Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require MmapSim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require BackingAlgebra AsanNodesMmLib.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanNodesLibE.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefNodes.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics MemImageType StackLayout Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesFs__Lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module AsanBootMm3.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require MmapSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require BackingAlgebra AsanNodesMmLib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition ivs_pos (l : list (word * word)) : Prop := forall q, In q l -> 0 < bv_unsigned (snd q).

(* [comment removed for export] *)
Definition ivs_within (l : list (word * word)) (W : list (Z * Z)) : Prop :=
  forall q, In q l -> exists w, In w W /\ fst w <= bv_unsigned (fst q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= snd w.

Lemma ivs_pos_nil : ivs_pos []. Proof. intros q []. Qed.
Lemma ivs_pos_cons : forall p l, 0 < bv_unsigned (snd p) -> ivs_pos l -> ivs_pos (p :: l).
Proof. intros p l Hp Hl q [<-|Hq]; auto. Qed.
Lemma ivs_within_nil : forall W, ivs_within [] W. Proof. intros W q []. Qed.
Lemma ivs_within_cons : forall p l W,
  (exists w, In w W /\ fst w <= bv_unsigned (fst p) /\ bv_unsigned (fst p) + bv_unsigned (snd p) <= snd w) ->
  ivs_within l W -> ivs_within (p :: l) W.
Proof. intros p l W Hp Hl q [<-|Hq]; auto. Qed.
Lemma ivs_within_mono : forall l W W', (forall w, In w W -> In w W') -> ivs_within l W -> ivs_within l W'.
Proof. intros l W W' HW Hl q Hq. destruct (Hl q Hq) as (w & Hw & H). exists w. split; [apply HW; exact Hw | exact H]. Qed.

Lemma iv_subtract_pos : forall (a sz : word) lo hi q,
  iv_wf (a, sz) -> 0 < bv_unsigned sz -> In q (iv_subtract a sz lo hi) -> 0 < bv_unsigned (snd q).
Proof.
  intros a sz lo hi q Hwf Hsz Hin. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:El; [|destruct Hin]. apply Z.ltb_lt in El.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite u64_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite !u64_lit by lia. lia.
Qed.

Lemma maps_subtract_pos : forall l lo hi, ivs_wf l -> ivs_pos l -> ivs_pos (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hwf Hp q Hin; [destruct Hin|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract] in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - exact (iv_subtract_pos a sz lo hi q Ha (Hp (a, sz) (or_introl eq_refl)) Hin).
  - apply (IH lo hi Hl); [intros r Hr; apply Hp; right; exact Hr | exact Hin].
Qed.

Lemma maps_subtract_within : forall l lo hi W, ivs_wf l -> ivs_within l W -> ivs_within (maps_subtract l lo hi) W.
Proof.
  intros l lo hi W Hwf Hl q Hin. destruct (maps_subtract_pieces l lo hi q Hwf Hin) as (r & Hr & H1 & H2 & _).
  destruct (Hl r Hr) as (w & Hw & G1 & G2). exists w. split; [exact Hw | lia].
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_id : forall l lo hi, lo < hi -> ivs_pos l ->
  (forall r, In r l -> bv_unsigned (fst r) + bv_unsigned (snd r) <= lo \/ hi <= bv_unsigned (fst r)) ->
  maps_subtract l lo hi = l.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hlh Hp Hd; [reflexivity|].
  cbn [maps_subtract]. rewrite (iv_subtract_disjoint a sz lo hi Hlh (Hp (a, sz) (or_introl eq_refl)) (Hd (a, sz) (or_introl eq_refl))).
  cbn [app]. f_equal. apply IH; [exact Hlh | intros r Hr; apply Hp; right; exact Hr | intros r Hr; apply Hd; right; exact Hr].
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_id_within : forall l lo hi W, lo < hi -> ivs_pos l -> ivs_within l W ->
  (forall w, In w W -> snd w <= lo \/ hi <= fst w) ->
  maps_subtract l lo hi = l.
Proof.
  intros l lo hi W Hlh Hp Hw HW. apply maps_subtract_id; [exact Hlh | exact Hp |].
  intros r Hr. destruct (Hw r Hr) as (w & Hin & G1 & G2). destruct (HW w Hin); [left | right]; lia.
Qed.
End AsanBootMm3.

(* [comment removed for export] *)
Module AsanLedger.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require BackingAlgebra AsanNodesMmLib AsanNodesLibE. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pages_sub_maps_subtract : forall l lo hi (p : word),
  ivs_wf l -> lo <= hi ->
  page_in_ranges p (maps_subtract l lo hi) = true -> page_in_ranges p l = true.
Proof.
  intros l lo hi p Hwf Hlh Hp. apply page_in_ranges_true in Hp as (q & Hin & H1 & H2).
  destruct (maps_subtract_pieces l lo hi q Hwf Hin) as (r & Hr & R1 & R2 & _).
  apply (proj2 (page_in_ranges_true p l)). exists r. split; [exact Hr | lia].
Qed.

Lemma page_outside_aligned : forall lo hi (p : word),
  lo mod page_size = 0 -> hi mod page_size = 0 -> bv_unsigned p mod page_size = 0 ->
  page_outside_range lo hi p = true ->
  bv_unsigned p + page_size <= lo \/ hi <= bv_unsigned p.
Proof.
  intros lo hi p Hlo Hhi Hp Hout. unfold page_outside_range in Hout. apply negb_true_iff in Hout.
  apply andb_false_iff in Hout as [Hout|Hout]; [apply Z.leb_gt in Hout | apply Z.ltb_ge in Hout; right; exact Hout].
  left. unfold page_size in *.
  pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.div_mod (bv_unsigned p) 4096 ltac:(lia)). nia.
Qed.

(* [comment removed for export] *)
Lemma forget_filter_lazy : forall (lz : list (word * word)) (mat : list word) lo hi p,
  ivs_wf lz -> lo <= hi -> lo mod page_size = 0 -> hi mod page_size = 0 ->
  (forall q, In q mat -> bv_unsigned q mod page_size = 0) ->
  (forall q, In q mat -> page_in_ranges q lz = true) ->
  In p (List.filter (page_outside_range lo hi) mat) ->
  page_in_ranges p (maps_subtract lz lo hi) = true.
Proof.
  intros lz mat lo hi p Hwf Hlh Hlo Hhi Hal Hlz Hin. apply filter_In in Hin as [Hin Hout].
  rewrite (page_in_ranges_subtract_out p lz lo hi Hwf Hlh).
  - exact (Hlz p Hin).
  - apply page_outside_aligned; [exact Hlo | exact Hhi | exact (Hal p Hin) | exact Hout].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Fixedin.
  Variable A : list (Z * Z).
  Variables (flags addr n : word) (m : Model).
  Let lo := bv_unsigned addr.
  Let hi := bv_unsigned addr + bv_unsigned n.
  Hypothesis Hwf : model_ivs_wf m.
  Hypothesis Hal : bv_unsigned addr mod page_size = 0.
  Hypothesis Hnl : bv_unsigned n mod page_size = 0.
  Hypothesis Hpos : 0 < bv_unsigned n.
  Hypothesis Hend : bv_unsigned addr + bv_unsigned n <= 2 ^ 64.

  Let Wm := proj1 Hwf.
  Let Wn := proj1 (proj2 Hwf).
  Let Wl := proj1 (proj2 (proj2 Hwf)).
  Let Wsp := proj2 (proj2 (proj2 Hwf)).

  #[using="Hpos"] Lemma lo_le_hi : lo <= hi. Proof. unfold lo, hi. lia. Qed.
  #[using="lo Hal Hnl"] Lemma hi_aligned : hi mod page_size = 0.
  Proof. unfold hi, page_size in *. rewrite Z.add_mod, Hal, Hnl by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Section Eager.
    Hypothesis Hnr : mmap_noreserve_b flags = false.
    Let m' := fixedin_ok_model 3 flags addr n m.

    #[using="Hnr"] Lemma fixedin_eager_unfold :
      m' = vm_forget_range lo hi (with_vmmaps (mmap_fixed_rw_next (m_vmmaps m) addr n) m).
    Proof.
      unfold m', fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. cbn [Z.eqb].
      rewrite Hnr. reflexivity.
    Qed.

    #[using="lo hi Hnr"] Lemma fixedin_eager_maps : vm_maps (m_vmmaps m') = vm_maps (m_vmmaps m).
    Proof. rewrite fixedin_eager_unfold. reflexivity. Qed.
    #[using="lo hi Hnr"] Lemma fixedin_eager_reserved : vm_reserved (m_vmmaps m') = vm_reserved (m_vmmaps m).
    Proof. rewrite fixedin_eager_unfold. reflexivity. Qed.
    #[using="Hnr"] Lemma fixedin_eager_noaccess : vm_noaccess (m_vmmaps m') = maps_subtract (vm_noaccess (m_vmmaps m)) lo hi.
    Proof. rewrite fixedin_eager_unfold. reflexivity. Qed.
    #[using="Hnr"] Lemma fixedin_eager_lazy : m_vm_lazy m' = maps_subtract (m_vm_lazy m) lo hi.
    Proof. rewrite fixedin_eager_unfold. reflexivity. Qed.
    #[using="Hnr"] Lemma fixedin_eager_mat : m_vm_materialized m' = List.filter (page_outside_range lo hi) (m_vm_materialized m).
    Proof. rewrite fixedin_eager_unfold. reflexivity. Qed.
    #[using="lo hi Hnr"] Lemma fixedin_eager_limit : vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
    Proof. rewrite fixedin_eager_unfold. reflexivity. Qed.
    #[using="lo hi Hnr"] Lemma fixedin_eager_init_sp : vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m).
    Proof. rewrite fixedin_eager_unfold. reflexivity. Qed.
    #[using="lo hi Hnr"] Lemma fixedin_eager_halted : m_halted m' = m_halted m.
    Proof. rewrite fixedin_eager_unfold. reflexivity. Qed.
    #[using="lo hi Hnr"] Lemma fixedin_eager_fds : m_fds m' = m_fds m.
    Proof. rewrite fixedin_eager_unfold. reflexivity. Qed.
    #[using="lo hi Hnr"] Lemma fixedin_eager_fs : m_fs m' = m_fs m.
    Proof. rewrite fixedin_eager_unfold. reflexivity. Qed.
    #[using="lo hi Hnr"] Lemma fixedin_eager_tid : m_tid m' = m_tid m.
    Proof. rewrite fixedin_eager_unfold. reflexivity. Qed.

    #[using="lo hi Hwf Hpos Wm Wn Hnr"] Lemma model_ivs_wf_fixedin_eager : model_ivs_wf m'.
    Proof.
      rewrite fixedin_eager_unfold. apply model_ivs_wf_vm_forget_range; [apply lo_le_hi|].
      apply model_ivs_wf_with_vmmaps; [exact Hwf | exact Wm | | reflexivity].
      unfold mmap_fixed_rw_next. cbn. apply maps_subtract_wf; [exact Wn | apply lo_le_hi].
    Qed.

    #[using="Hwf Hpos Wm Wn Wl Hnr"] Lemma eager_used_fixedin_eager_le :
      eager_used m' <= eager_used m + overlap_sum (vm_maps (m_vmmaps m)) lo hi.
    Proof.
      rewrite (eager_used_sem m' model_ivs_wf_fixedin_eager), (eager_used_sem m Hwf).
      rewrite fixedin_eager_maps, fixedin_eager_noaccess, fixedin_eager_lazy.
      destruct (maps_subtract_sem _ lo hi Wn lo_le_hi) as (_ & _ & Cn).
      destruct (maps_subtract_sem _ lo hi Wl lo_le_hi) as (_ & _ & Cl).
      unfold overlap_sum. eapply Z.le_trans.
      { apply (sum_count_mono _ (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x) || in_rng lo hi x)).
        intros x. rewrite !covered_app, Cn, Cl.
        destruct (covered (vm_noaccess (m_vmmaps m)) x), (covered (m_vm_lazy m) x), (in_rng lo hi x); cbn; congruence. }
      apply sum_count_or_le.
    Qed.

    #[using="Hwf Hal Hnl Hpos Wm Wn Wl Hnr"] Lemma MInv_fixedin_eager :
      MInv A m -> eager_used m + overlap_sum (vm_maps (m_vmmaps m)) lo hi + A_bytes A <= vm_limit (m_vmmaps m) ->
      MInv A m'.
    Proof.
      intros [Hnd Halg Hallow Hlz Hb] Hbud. constructor.
      - rewrite fixedin_eager_mat. apply NoDup_filter. exact Hnd.
      - rewrite fixedin_eager_mat. intros p Hp. apply filter_In in Hp as [Hp _]. exact (Halg p Hp).
      - rewrite fixedin_eager_mat. intros p Hp. apply filter_In in Hp as [Hp _]. exact (Hallow p Hp).
      - rewrite fixedin_eager_mat, fixedin_eager_lazy. intros p Hp.
        eapply forget_filter_lazy; [exact Wl | apply lo_le_hi | exact Hal | apply hi_aligned | exact Halg | exact Hlz | exact Hp].
      - rewrite fixedin_eager_limit. pose proof eager_used_fixedin_eager_le. lia.
    Qed.

    #[using="lo hi Hwf Hpos Wl Hnr"] Lemma lazy_pages_fixedin_eager : forall p,
      page_in_ranges p (m_vm_lazy m') = true -> page_in_ranges p (m_vm_lazy m) = true.
    Proof. intros p. rewrite fixedin_eager_lazy. apply pages_sub_maps_subtract; [exact Wl | apply lo_le_hi]. Qed.

    #[using="lo hi Hwf Hpos Wl Hnr"] Lemma lazy_cover_fixedin_eager : forall H, lazy_cover H (m_vm_lazy m) A -> lazy_cover H (m_vm_lazy m') A.
    Proof. intros H HL w Hp Hw. apply HL; [apply lazy_pages_fixedin_eager; exact Hp | exact Hw]. Qed.
  End Eager.

  (* [comment removed for export] *)
  Section Lazy.
    Hypothesis Hnr : mmap_noreserve_b flags = true.
    Let m' := fixedin_ok_model 3 flags addr n m.

    #[using="Hnr"] Lemma fixedin_lazy_unfold :
      m' = vm_add_lazy addr n (vm_forget_range lo hi (with_vmmaps (mmap_fixed_rw_next (m_vmmaps m) addr n) m)).
    Proof.
      unfold m', fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. cbn [Z.eqb].
      rewrite Hnr. reflexivity.
    Qed.

    #[using="lo hi Hnr"] Lemma fixedin_lazy_maps : vm_maps (m_vmmaps m') = vm_maps (m_vmmaps m).
    Proof. rewrite fixedin_lazy_unfold. reflexivity. Qed.
    #[using="lo hi Hnr"] Lemma fixedin_lazy_reserved : vm_reserved (m_vmmaps m') = vm_reserved (m_vmmaps m).
    Proof. rewrite fixedin_lazy_unfold. reflexivity. Qed.
    #[using="Hnr"] Lemma fixedin_lazy_noaccess : vm_noaccess (m_vmmaps m') = maps_subtract (vm_noaccess (m_vmmaps m)) lo hi.
    Proof. rewrite fixedin_lazy_unfold. reflexivity. Qed.
    #[using="Hal Hnl Hpos Hend Hnr"] Lemma fixedin_lazy_lazy : m_vm_lazy m' = (addr, n) :: maps_subtract (m_vm_lazy m) lo hi.
    Proof.
      rewrite fixedin_lazy_unfold. unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing.
      rewrite (lazy_interior_aligned addr n Hal Hnl Hpos Hend). reflexivity.
    Qed.
    #[using="Hnr"] Lemma fixedin_lazy_mat : m_vm_materialized m' = List.filter (page_outside_range lo hi) (m_vm_materialized m).
    Proof. rewrite fixedin_lazy_unfold. reflexivity. Qed.
    #[using="lo hi Hnr"] Lemma fixedin_lazy_limit : vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
    Proof. rewrite fixedin_lazy_unfold. reflexivity. Qed.
    #[using="lo hi Hnr"] Lemma fixedin_lazy_init_sp : vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m).
    Proof. rewrite fixedin_lazy_unfold. reflexivity. Qed.
    #[using="lo hi Hnr"] Lemma fixedin_lazy_halted : m_halted m' = m_halted m.
    Proof. rewrite fixedin_lazy_unfold. reflexivity. Qed.
    #[using="lo hi Hnr"] Lemma fixedin_lazy_fds : m_fds m' = m_fds m.
    Proof. rewrite fixedin_lazy_unfold. reflexivity. Qed.
    #[using="lo hi Hnr"] Lemma fixedin_lazy_fs : m_fs m' = m_fs m.
    Proof. rewrite fixedin_lazy_unfold. reflexivity. Qed.
    #[using="lo hi Hnr"] Lemma fixedin_lazy_tid : m_tid m' = m_tid m.
    Proof. rewrite fixedin_lazy_unfold. reflexivity. Qed.

    #[using="lo hi Hwf Hpos Hend Wm Wn Hnr"] Lemma model_ivs_wf_fixedin_lazy : model_ivs_wf m'.
    Proof.
      rewrite fixedin_lazy_unfold. apply model_ivs_wf_vm_add_lazy; [exact Hend|].
      apply model_ivs_wf_vm_forget_range; [apply lo_le_hi|].
      apply model_ivs_wf_with_vmmaps; [exact Hwf | exact Wm | | reflexivity].
      unfold mmap_fixed_rw_next. cbn. apply maps_subtract_wf; [exact Wn | apply lo_le_hi].
    Qed.

    #[using="lo hi Hwf Hal Hnl Hpos Hend Wm Wn Wl Hnr"] Lemma eager_used_fixedin_lazy_le : eager_used m' <= eager_used m.
    Proof.
      rewrite (eager_used_sem m' model_ivs_wf_fixedin_lazy), (eager_used_sem m Hwf).
      rewrite fixedin_lazy_maps, fixedin_lazy_noaccess, fixedin_lazy_lazy.
      destruct (maps_subtract_sem _ lo hi Wn lo_le_hi) as (_ & _ & Cn).
      destruct (maps_subtract_sem _ lo hi Wl lo_le_hi) as (_ & _ & Cl).
      apply sum_count_mono. intros x Hx.
      rewrite covered_app in Hx. unfold covered in Hx at 2. cbn [existsb] in Hx.
      fold (covered (maps_subtract (m_vm_lazy m) lo hi) x) in Hx. rewrite Cn, Cl in Hx. rewrite covered_app.
      change (in_iv (addr, n) x) with (in_rng lo hi x) in Hx.
      destruct (covered (vm_noaccess (m_vmmaps m)) x), (covered (m_vm_lazy m) x), (in_rng lo hi x); cbn in *; congruence.
    Qed.

    #[using="lo hi Hwf Hal Hnl Hpos Hend Wm Wn Wl Hnr"] Lemma MInv_fixedin_lazy : MInv A m -> MInv A m'.
    Proof.
      intros [Hnd Halg Hallow Hlz Hb]. constructor.
      - rewrite fixedin_lazy_mat. apply NoDup_filter. exact Hnd.
      - rewrite fixedin_lazy_mat. intros p Hp. apply filter_In in Hp as [Hp _]. exact (Halg p Hp).
      - rewrite fixedin_lazy_mat. intros p Hp. apply filter_In in Hp as [Hp _]. exact (Hallow p Hp).
      - rewrite fixedin_lazy_mat, fixedin_lazy_lazy. intros p Hp. rewrite page_in_ranges_cons. apply orb_true_iff. right.
        eapply forget_filter_lazy; [exact Wl | apply lo_le_hi | exact Hal | apply hi_aligned | exact Halg | exact Hlz | exact Hp].
      - rewrite fixedin_lazy_limit. pose proof eager_used_fixedin_lazy_le. lia.
    Qed.

    (* [comment removed for export] *)
    #[using="lo hi Hwf Hal Hnl Hpos Hend Wl Hnr"] Lemma lazy_pages_fixedin_lazy : map_contains (m_vm_lazy m) addr n = true ->
      forall p, page_in_ranges p (m_vm_lazy m') = true -> page_in_ranges p (m_vm_lazy m) = true.
    Proof.
      intros Hmc p. rewrite fixedin_lazy_lazy, page_in_ranges_cons. cbn [fst snd]. intros Hp.
      apply orb_true_iff in Hp as [Hp|Hp].
      - apply andb_prop in Hp as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
        unfold map_contains in Hmc. apply existsb_exists in Hmc as (r & Hr & Hc).
        apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
        apply (proj2 (page_in_ranges_true p (m_vm_lazy m))). exists r. split; [exact Hr | lia].
      - eapply pages_sub_maps_subtract; [exact Wl | apply lo_le_hi | exact Hp].
    Qed.

    #[using="lo hi Hwf Hal Hnl Hpos Hend Wl Hnr"] Lemma lazy_cover_fixedin_lazy : forall H, map_contains (m_vm_lazy m) addr n = true ->
      lazy_cover H (m_vm_lazy m) A -> lazy_cover H (m_vm_lazy m') A.
    Proof. intros H Hmc HL w Hp Hw. apply HL; [apply (lazy_pages_fixedin_lazy Hmc); exact Hp | exact Hw]. Qed.
  End Lazy.

  (* [comment removed for export] *)
  Section Destroyed.
    Let m' := fixedin_destroyed_model addr n m.

    #[using="Type"] Lemma destroyed_unfold :
      m' = vm_forget_range lo hi (with_vmmaps (fixedin_destroyed_vmmaps addr n (m_vmmaps m)) m).
    Proof. reflexivity. Qed.

    #[using="Type"] Lemma destroyed_maps : vm_maps (m_vmmaps m') = maps_subtract (vm_maps (m_vmmaps m)) lo hi.
    Proof. reflexivity. Qed.
    #[using="Type"] Lemma destroyed_reserved : vm_reserved (m_vmmaps m') = vm_reserved (m_vmmaps m).
    Proof. reflexivity. Qed.
    #[using="Type"] Lemma destroyed_noaccess : vm_noaccess (m_vmmaps m') = maps_subtract (vm_noaccess (m_vmmaps m)) lo hi.
    Proof. reflexivity. Qed.
    #[using="Type"] Lemma destroyed_lazy : m_vm_lazy m' = maps_subtract (m_vm_lazy m) lo hi.
    Proof. reflexivity. Qed.
    #[using="Type"] Lemma destroyed_mat : m_vm_materialized m' = List.filter (page_outside_range lo hi) (m_vm_materialized m).
    Proof. reflexivity. Qed.
    #[using="Type"] Lemma destroyed_limit : vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
    Proof. reflexivity. Qed.
    #[using="Type"] Lemma destroyed_init_sp : vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m).
    Proof. reflexivity. Qed.
    #[using="Type"] Lemma destroyed_halted : m_halted m' = m_halted m.
    Proof. reflexivity. Qed.
    #[using="Type"] Lemma destroyed_fds : m_fds m' = m_fds m.
    Proof. reflexivity. Qed.
    #[using="Type"] Lemma destroyed_fs : m_fs m' = m_fs m.
    Proof. reflexivity. Qed.
    #[using="Type"] Lemma destroyed_tid : m_tid m' = m_tid m.
    Proof. reflexivity. Qed.

    #[using="lo hi Hwf Hpos Wm Wn"] Lemma model_ivs_wf_destroyed : model_ivs_wf m'.
    Proof.
      rewrite destroyed_unfold. apply model_ivs_wf_vm_forget_range; [apply lo_le_hi|].
      apply model_ivs_wf_with_vmmaps; [exact Hwf | | | reflexivity]; unfold fixedin_destroyed_vmmaps; cbn;
        apply maps_subtract_wf; try apply lo_le_hi; [exact Wm | exact Wn].
    Qed.

    #[using="lo hi Hwf Hpos Wm Wn Wl"] Lemma eager_used_destroyed_le : eager_used m' <= eager_used m.
    Proof.
      rewrite (eager_used_sem m' model_ivs_wf_destroyed), (eager_used_sem m Hwf).
      rewrite destroyed_maps, destroyed_noaccess, destroyed_lazy.
      destruct (maps_subtract_sem _ lo hi Wm lo_le_hi) as (_ & Sm & _).
      destruct (maps_subtract_sem _ lo hi Wn lo_le_hi) as (_ & _ & Cn).
      destruct (maps_subtract_sem _ lo hi Wl lo_le_hi) as (_ & _ & Cl).
      rewrite Sm. apply sum_count_mono. intros x Hx.
      rewrite !covered_app, Cn, Cl in Hx. rewrite covered_app.
      destruct (covered (vm_noaccess (m_vmmaps m)) x), (covered (m_vm_lazy m) x), (in_rng lo hi x); cbn in *; congruence.
    Qed.

    #[using="lo hi Hwf Hal Hnl Hpos Wm Wn Wl"] Lemma MInv_destroyed : MInv A m -> MInv A m'.
    Proof.
      intros [Hnd Halg Hallow Hlz Hb]. constructor.
      - rewrite destroyed_mat. apply NoDup_filter. exact Hnd.
      - rewrite destroyed_mat. intros p Hp. apply filter_In in Hp as [Hp _]. exact (Halg p Hp).
      - rewrite destroyed_mat. intros p Hp. apply filter_In in Hp as [Hp _]. exact (Hallow p Hp).
      - rewrite destroyed_mat, destroyed_lazy. intros p Hp.
        eapply forget_filter_lazy; [exact Wl | apply lo_le_hi | exact Hal | apply hi_aligned | exact Halg | exact Hlz | exact Hp].
      - rewrite destroyed_limit. pose proof eager_used_destroyed_le. lia.
    Qed.

    #[using="lo hi Hwf Hpos Wl"] Lemma lazy_pages_destroyed : forall p,
      page_in_ranges p (m_vm_lazy m') = true -> page_in_ranges p (m_vm_lazy m) = true.
    Proof. intros p. rewrite destroyed_lazy. apply pages_sub_maps_subtract; [exact Wl | apply lo_le_hi]. Qed.

    #[using="lo hi Hwf Hpos Wl"] Lemma lazy_cover_destroyed : forall H, lazy_cover H (m_vm_lazy m) A -> lazy_cover H (m_vm_lazy m') A.
    Proof. intros H HL w Hp Hw. apply HL; [apply lazy_pages_destroyed; exact Hp | exact Hw]. Qed.
  End Destroyed.
End Fixedin.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma overlap_sum_one : forall l1 p l2 (lo n : word),
  region_free (l1 ++ l2) lo n = true ->
  overlap_sum (l1 ++ p :: l2) (bv_unsigned lo) (bv_unsigned lo + bv_unsigned n) <= bv_unsigned n.
Proof.
  intros l1 p l2 lo n Hrf. pose proof (bv_unsigned_in_range 64 n) as Hn.
  assert (Hrf' : region_free l1 lo n = true /\ region_free l2 lo n = true).
  { revert Hrf. clear. induction l1 as [|[b s] l1 IH]; cbn [region_free app]; intros Hrf; [auto|].
    apply andb_true_iff in Hrf as [H1 H2]. destruct (IH H2) as [IH1 IH2]. rewrite H1, IH1. auto. }
  destruct Hrf' as [H1 H2].
  rewrite overlap_sum_app, overlap_sum_cons, (overlap_sum_region_free l1 lo n H1), (overlap_sum_region_free l2 lo n H2).
  pose proof (iv_count_in_rng_le p (bv_unsigned lo) (bv_unsigned lo + bv_unsigned n) ltac:(lia)). lia.
Qed.
End AsanLedger.

(* [comment removed for export] *)
Module AsanBootMm.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require MmapSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require BackingAlgebra AsanNodesMmLib AsanNodesLibE. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanLedger.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sum_count_filter_le : forall P f l, sum_count P (List.filter f l) <= sum_count P l.
Proof.
  intros P f l. induction l as [|q l IH]; cbn -[Z.add]; [lia|].
  pose proof (zcount_nonneg P (B q) (Z.to_nat (S q))). unfold iv_count in *.
  destruct (f q); cbn -[Z.add]; unfold iv_count; lia.
Qed.

Lemma sum_count_ext_in : forall P Q l,
  (forall q x, In q l -> B q <= x < B q + S q -> P x = Q x) -> sum_count P l = sum_count Q l.
Proof.
  intros P Q l H. induction l as [|q l IH]; cbn -[Z.add]; [reflexivity|].
  unfold iv_count. rewrite (zcount_ext P Q (B q) (Z.to_nat (S q))).
  - rewrite IH; [reflexivity|]. intros q' x Hq' Hx. apply (H q' x); [right; exact Hq' | exact Hx].
  - intros x Hx. apply (H q x); [left; reflexivity|]. pose proof (S_range q). rewrite Z2Nat.id in Hx by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Munmap.
  Variable A : list (Z * Z).
  Variables (addr n : word) (m : Model).
  Let lo := bv_unsigned addr.
  Let hi := bv_unsigned addr + bv_unsigned n.
  Hypothesis Hwf : model_ivs_wf m.
  Hypothesis Hal : bv_unsigned addr mod page_size = 0.
  Hypothesis Hnl : bv_unsigned n mod page_size = 0.
  Hypothesis Hpos : 0 < bv_unsigned n.
  Hypothesis Hend : bv_unsigned addr + bv_unsigned n <= 2 ^ 64.
  (* [comment removed for export] *)
  Hypothesis Hapart : forall q, In q (map_remove (vm_maps (m_vmmaps m)) addr) -> B q + S q <= lo \/ hi <= B q.

  Let Wm := proj1 Hwf.
  Let Wn := proj1 (proj2 Hwf).
  Let Wl := proj1 (proj2 (proj2 Hwf)).
  Let Wsp := proj2 (proj2 (proj2 Hwf)).
  Let m' := munmap_model addr n m.

  #[using="Hpos"] Lemma mun_lo_le_hi : lo <= hi. Proof. unfold lo, hi. lia. Qed.
  #[using="lo Hal Hnl"] Lemma mun_hi_aligned : hi mod page_size = 0.
  Proof. unfold hi, page_size in *. rewrite Z.add_mod, Hal, Hnl by lia. reflexivity. Qed.

  #[using="Type"] Lemma munmap_unfold :
    m' = vm_forget_range lo hi (with_vmmaps
           (mkVmMapsFull (vm_reserved (m_vmmaps m)) (map_remove (vm_maps (m_vmmaps m)) addr)
              (maps_subtract (vm_noaccess (m_vmmaps m)) lo hi)
              (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
              (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).
  Proof. reflexivity. Qed.

  #[using="Type"] Lemma munmap_maps : vm_maps (m_vmmaps m') = map_remove (vm_maps (m_vmmaps m)) addr.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma munmap_reserved : vm_reserved (m_vmmaps m') = vm_reserved (m_vmmaps m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma munmap_noaccess : vm_noaccess (m_vmmaps m') = maps_subtract (vm_noaccess (m_vmmaps m)) lo hi.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma munmap_lazy : m_vm_lazy m' = maps_subtract (m_vm_lazy m) lo hi.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma munmap_mat : m_vm_materialized m' = List.filter (page_outside_range lo hi) (m_vm_materialized m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma munmap_limit : vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma munmap_init_sp : vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma munmap_start_brk : vm_start_brk (m_vmmaps m') = vm_start_brk (m_vmmaps m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma munmap_brk : vm_brk (m_vmmaps m') = vm_brk (m_vmmaps m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma munmap_mmap_base : vm_mmap_base (m_vmmaps m') = vm_mmap_base (m_vmmaps m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma munmap_halted : m_halted m' = m_halted m.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma munmap_fds : m_fds m' = m_fds m.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma munmap_fs : m_fs m' = m_fs m.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma munmap_tid : m_tid m' = m_tid m.
  Proof. reflexivity. Qed.

  #[using="lo hi Hwf Hpos Wm Wn"] Lemma model_ivs_wf_munmap : model_ivs_wf m'.
  Proof.
    rewrite munmap_unfold. apply model_ivs_wf_vm_forget_range; [apply mun_lo_le_hi|].
    apply model_ivs_wf_with_vmmaps; [exact Hwf | | | reflexivity]; cbn.
    - unfold map_remove. apply ivs_wf_filter. exact Wm.
    - apply maps_subtract_wf; [exact Wn | apply mun_lo_le_hi].
  Qed.

  #[using="lo hi Hwf Hpos Hapart Wm Wn Wl"] Lemma eager_used_munmap_le : eager_used m' <= eager_used m.
  Proof.
    rewrite (eager_used_sem m' model_ivs_wf_munmap), (eager_used_sem m Hwf).
    rewrite munmap_maps, munmap_noaccess, munmap_lazy.
    destruct (maps_subtract_sem _ lo hi Wn mun_lo_le_hi) as (_ & _ & Cn).
    destruct (maps_subtract_sem _ lo hi Wl mun_lo_le_hi) as (_ & _ & Cl).
    rewrite (sum_count_ext_in (fun x => negb (covered (maps_subtract (vm_noaccess (m_vmmaps m)) lo hi ++ maps_subtract (m_vm_lazy m) lo hi) x))
                             (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x))).
    - unfold map_remove. apply sum_count_filter_le.
    - intros q x Hq Hx. rewrite !covered_app, Cn, Cl.
      assert (Hr : in_rng lo hi x = false).
      { pose proof (Hapart q Hq). unfold in_rng. apply andb_false_iff.
        destruct (Z.le_gt_cases hi x); [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia]. }
      rewrite Hr. cbn [negb]. rewrite !andb_true_r. reflexivity.
  Qed.

  #[using="lo hi Hwf Hal Hnl Hpos Hapart Wm Wn Wl"] Lemma MInv_munmap : MInv A m -> MInv A m'.
  Proof.
    intros [Hnd Halg Hallow Hlz Hb]. constructor.
    - rewrite munmap_mat. apply NoDup_filter. exact Hnd.
    - rewrite munmap_mat. intros p Hp. apply filter_In in Hp as [Hp _]. exact (Halg p Hp).
    - rewrite munmap_mat. intros p Hp. apply filter_In in Hp as [Hp _]. exact (Hallow p Hp).
    - rewrite munmap_mat, munmap_lazy. intros p Hp.
      eapply forget_filter_lazy; [exact Wl | apply mun_lo_le_hi | exact Hal | apply mun_hi_aligned | exact Halg | exact Hlz | exact Hp].
    - rewrite munmap_limit. pose proof eager_used_munmap_le. lia.
  Qed.

  #[using="lo hi Hwf Hpos Wl"] Lemma lazy_pages_munmap : forall p,
    page_in_ranges p (m_vm_lazy m') = true -> page_in_ranges p (m_vm_lazy m) = true.
  Proof. intros p. rewrite munmap_lazy. apply pages_sub_maps_subtract; [exact Wl | apply mun_lo_le_hi]. Qed.

  #[using="lo hi Hwf Hpos Wl"] Lemma lazy_cover_munmap : forall H, lazy_cover H (m_vm_lazy m) A -> lazy_cover H (m_vm_lazy m') A.
  Proof. intros H HL w Hp Hw. apply HL; [apply lazy_pages_munmap; exact Hp | exact Hw]. Qed.

  (* [comment removed for export] *)
  #[using="Hwf Hpos Wl"] Lemma lazy_page_kept_munmap : forall p : word,
    bv_unsigned p mod page_size = 0 -> (bv_unsigned p + page_size <= lo \/ hi <= bv_unsigned p) ->
    page_in_ranges p (m_vm_lazy m) = true -> page_in_ranges p (m_vm_lazy m') = true.
  Proof.
    intros p Hp Hout Hin. rewrite munmap_lazy. rewrite (page_in_ranges_subtract_out p (m_vm_lazy m) lo hi Wl mun_lo_le_hi); [exact Hin | exact Hout].
  Qed.
End Munmap.
End AsanBootMm.

(* [comment removed for export] *)
Module AsanBootMm2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require MmapSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require BackingAlgebra AsanNodesMmLib AsanNodesLibE RefNodes. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanLedger OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanBootMm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FixedNoaccess.
  Variable A : list (Z * Z).
  Variables (addr n : word) (m : Model).
  Let lo := bv_unsigned addr.
  Let hi := bv_unsigned addr + bv_unsigned n.
  Hypothesis Hwf : model_ivs_wf m.
  Hypothesis Hal : bv_unsigned addr mod page_size = 0.
  Hypothesis Hnl : bv_unsigned n mod page_size = 0.
  Hypothesis Hpos : 0 < bv_unsigned n.
  Hypothesis Hend : bv_unsigned addr + bv_unsigned n <= 2 ^ 64.

  Let Wm := proj1 Hwf.
  Let Wn := proj1 (proj2 Hwf).
  Let Wl := proj1 (proj2 (proj2 Hwf)).
  Let Wsp := proj2 (proj2 (proj2 Hwf)).
  Let m' := fixed_noaccess_model addr n m.

  #[using="Hpos"] Lemma fxn_lo_le_hi : lo <= hi. Proof. unfold lo, hi. lia. Qed.
  #[using="lo Hal Hnl"] Lemma fxn_hi_aligned : hi mod page_size = 0.
  Proof. unfold hi, page_size in *. rewrite Z.add_mod, Hal, Hnl by lia. reflexivity. Qed.

  #[using="Type"] Lemma fxn_unfold :
    m' = vm_forget_range lo hi (with_vmmaps
           (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
              ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) lo hi)
              (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
              (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).
  Proof. reflexivity. Qed.

  #[using="Type"] Lemma fxn_maps : vm_maps (m_vmmaps m') = vm_maps (m_vmmaps m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma fxn_reserved : vm_reserved (m_vmmaps m') = vm_reserved (m_vmmaps m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma fxn_noaccess : vm_noaccess (m_vmmaps m') = (addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) lo hi.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma fxn_lazy : m_vm_lazy m' = maps_subtract (m_vm_lazy m) lo hi.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma fxn_mat : m_vm_materialized m' = List.filter (page_outside_range lo hi) (m_vm_materialized m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma fxn_limit : vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma fxn_init_sp : vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma fxn_start_brk : vm_start_brk (m_vmmaps m') = vm_start_brk (m_vmmaps m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma fxn_brk : vm_brk (m_vmmaps m') = vm_brk (m_vmmaps m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma fxn_mmap_base : vm_mmap_base (m_vmmaps m') = vm_mmap_base (m_vmmaps m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma fxn_halted : m_halted m' = m_halted m.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma fxn_fds : m_fds m' = m_fds m.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma fxn_fs : m_fs m' = m_fs m.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma fxn_tid : m_tid m' = m_tid m.
  Proof. reflexivity. Qed.

  #[using="lo hi Hwf Hpos Hend Wm Wn"] Lemma model_ivs_wf_fxn : model_ivs_wf m'.
  Proof.
    rewrite fxn_unfold. apply model_ivs_wf_vm_forget_range; [apply fxn_lo_le_hi|].
    apply model_ivs_wf_with_vmmaps; [exact Hwf | | | reflexivity]; cbn.
    - exact Wm.
    - apply ivs_wf_cons; [apply iv_wf_intro; exact Hend|]. apply maps_subtract_wf; [exact Wn | apply fxn_lo_le_hi].
  Qed.

  #[using="lo hi Hwf Hpos Hend Wm Wn Wl"] Lemma eager_used_fxn_le : eager_used m' <= eager_used m.
  Proof.
    rewrite (eager_used_sem m' model_ivs_wf_fxn), (eager_used_sem m Hwf).
    rewrite fxn_maps, fxn_noaccess, fxn_lazy.
    destruct (maps_subtract_sem _ lo hi Wn fxn_lo_le_hi) as (_ & _ & Cn).
    destruct (maps_subtract_sem _ lo hi Wl fxn_lo_le_hi) as (_ & _ & Cl).
    apply sum_count_negb_covered_mono. intros x Hx.
    cbn [app]. unfold covered. cbn [existsb]. fold (covered (maps_subtract (vm_noaccess (m_vmmaps m)) lo hi ++ maps_subtract (m_vm_lazy m) lo hi) x).
    rewrite covered_app, Cn, Cl. rewrite covered_app in Hx.
    destruct (in_rng lo hi x) eqn:Hr.
    - unfold in_iv, B, S. cbn [fst snd]. fold lo. replace (lo + bv_unsigned n) with hi by reflexivity. rewrite Hr. reflexivity.
    - cbn [negb]. rewrite !andb_true_r. rewrite Hx. apply orb_true_r.
  Qed.

  #[using="lo hi Hwf Hal Hnl Hpos Hend Wm Wn Wl"] Lemma MInv_fxn : MInv A m -> MInv A m'.
  Proof.
    intros [Hnd Halg Hallow Hlz Hb]. constructor.
    - rewrite fxn_mat. apply NoDup_filter. exact Hnd.
    - rewrite fxn_mat. intros p Hp. apply filter_In in Hp as [Hp _]. exact (Halg p Hp).
    - rewrite fxn_mat. intros p Hp. apply filter_In in Hp as [Hp _]. exact (Hallow p Hp).
    - rewrite fxn_mat, fxn_lazy. intros p Hp.
      eapply forget_filter_lazy; [exact Wl | apply fxn_lo_le_hi | exact Hal | apply fxn_hi_aligned | exact Halg | exact Hlz | exact Hp].
    - rewrite fxn_limit. pose proof eager_used_fxn_le. lia.
  Qed.

  #[using="lo hi Hwf Hpos Wl"] Lemma lazy_pages_fxn : forall p,
    page_in_ranges p (m_vm_lazy m') = true -> page_in_ranges p (m_vm_lazy m) = true.
  Proof. intros p. rewrite fxn_lazy. apply pages_sub_maps_subtract; [exact Wl | apply fxn_lo_le_hi]. Qed.

  #[using="lo hi Hwf Hpos Wl"] Lemma lazy_cover_fxn : forall H, lazy_cover H (m_vm_lazy m) A -> lazy_cover H (m_vm_lazy m') A.
  Proof. intros H HL w Hp Hw. apply HL; [apply lazy_pages_fxn; exact Hp | exact Hw]. Qed.

  #[using="Hwf Hpos Wl"] Lemma lazy_page_kept_fxn : forall p : word,
    bv_unsigned p mod page_size = 0 -> (bv_unsigned p + page_size <= lo \/ hi <= bv_unsigned p) ->
    page_in_ranges p (m_vm_lazy m) = true -> page_in_ranges p (m_vm_lazy m') = true.
  Proof.
    intros p Hp Hout Hin. rewrite fxn_lazy. rewrite (page_in_ranges_subtract_out p (m_vm_lazy m) lo hi Wl fxn_lo_le_hi); [exact Hin | exact Hout].
  Qed.
End FixedNoaccess.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Mprotect.
  Variable A : list (Z * Z).
  Variables (addr n : word) (m : Model).
  Let lo := bv_unsigned addr.
  Let hi := bv_unsigned addr + bv_unsigned n.
  Hypothesis Hwf : model_ivs_wf m.

  Let Wm := proj1 Hwf.
  Let Wn := proj1 (proj2 Hwf).
  Let Wl := proj1 (proj2 (proj2 Hwf)).
  Let Wsp := proj2 (proj2 (proj2 Hwf)).
  Let m' := mprotect_model addr n m.

  #[using="Type"] Lemma mp_lo_le_hi : lo <= hi. Proof. unfold lo, hi. pose proof (u64_range n). lia. Qed.

  #[using="Type"] Lemma mp_unfold :
    m' = with_vmmaps
           (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
              (maps_subtract (vm_noaccess (m_vmmaps m)) lo hi)
              (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
              (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
  Proof. reflexivity. Qed.

  #[using="Type"] Lemma mp_maps : vm_maps (m_vmmaps m') = vm_maps (m_vmmaps m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma mp_reserved : vm_reserved (m_vmmaps m') = vm_reserved (m_vmmaps m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma mp_noaccess : vm_noaccess (m_vmmaps m') = maps_subtract (vm_noaccess (m_vmmaps m)) lo hi.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma mp_lazy : m_vm_lazy m' = m_vm_lazy m.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma mp_mat : m_vm_materialized m' = m_vm_materialized m.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma mp_limit : vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma mp_init_sp : vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma mp_start_brk : vm_start_brk (m_vmmaps m') = vm_start_brk (m_vmmaps m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma mp_brk : vm_brk (m_vmmaps m') = vm_brk (m_vmmaps m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma mp_mmap_base : vm_mmap_base (m_vmmaps m') = vm_mmap_base (m_vmmaps m).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma mp_halted : m_halted m' = m_halted m.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma mp_fds : m_fds m' = m_fds m.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma mp_fs : m_fs m' = m_fs m.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma mp_tid : m_tid m' = m_tid m.
  Proof. reflexivity. Qed.

  #[using="lo hi Hwf Wm Wn"] Lemma model_ivs_wf_mp : model_ivs_wf m'.
  Proof.
    rewrite mp_unfold. apply model_ivs_wf_with_vmmaps; [exact Hwf | | | reflexivity]; cbn.
    - exact Wm.
    - apply maps_subtract_wf; [exact Wn | apply mp_lo_le_hi].
  Qed.

  (* [comment removed for export] *)
  #[using="Hwf"] Lemma eager_used_mp_le : eager_used m' <= eager_used m + overlap_sum (vm_maps (m_vmmaps m)) lo hi.
  Proof.
    pose proof (backing_mprotect_le m (m_vmmaps m') lo hi Hwf mp_lo_le_hi eq_refl eq_refl) as Hb.
    change (with_vmmaps (m_vmmaps m') m) with m' in Hb.
    rewrite !vm_backing_used_split, mp_mat in Hb. lia.
  Qed.

  #[using="Hwf"] Lemma MInv_mp : MInv A m -> eager_used m + overlap_sum (vm_maps (m_vmmaps m)) lo hi + A_bytes A <= vm_limit (m_vmmaps m) -> MInv A m'.
  Proof.
    intros HM Hbud. eapply MInv_transport; [exact HM | reflexivity | reflexivity |].
    rewrite mp_limit. pose proof eager_used_mp_le. lia.
  Qed.
End Mprotect.
End AsanBootMm2.

(* [comment removed for export] *)
Module AsanNodesBrk.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require MmapSim AllocSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require BackingAlgebra. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanNodesMmLib AsanNodesLibE. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.StreamExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.FileSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AsanAcctShape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanPlacement OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesFs__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanbrk_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma node_brk_lazy : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  node_ok segs (mkCfg ms model)
    {r : word | brk_resolution_ok model (ms_gpr ms 0) r}
    (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms
                       (mkEffectU (proj1_sig i) []
                          (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                          (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])))
                    (brk_model (ms_gpr ms 0) (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hsvc Hno.
  apply (node_chk_noacc segs ms model x8 {r : word | brk_resolution_ok model (ms_gpr ms 0) r}
           (fun i => mkEffectU (proj1_sig i) []
                          (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                          (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])
           (fun i => brk_model (ms_gpr ms 0) (proj1_sig i) model) Hh Hsvc).
  - intros [r Hr]. cbn [proj1_sig]. apply check_syscall_ok_iff.
    exact (brk_ok_intro segs ms x8 model r Hno Hr).
  - intros eff m' evs Hc. apply check_syscall_ok_iff in Hc.
    apply (brk_ok_iff segs ms x8 model eff m' evs Hno) in Hc as (Heff & -> & Hok & ->).
    exists (exist _ (eff_ret eff) Hok). cbn [proj1_sig]. rewrite <- Heff. repeat split; reflexivity.
  - intros eff Hc. apply (brk_no_unmodeled segs ms x8 model Hno).
    exact (proj1 (check_syscall_err_iff _ _ _) Hc).
  - intros [r Hr]. cbn [proj1_sig]. rewrite brk_model_halted. exact Hh.
  - intros [r Hr]. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_brk_query_lazy : forall regs (pc : word) mem rom model w K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  getr regs 10 = Z_to_bv 64 0 ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom) model) K ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w K HF HE Hh H17 H10 Hc.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = vm_brk (m_vmmaps model)).
  { intros r. rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
    unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_eq. }
  assert (Hq : brk_resolution_ok model (ms_gpr ms 0) (vm_brk (m_vmmaps model))) by (apply Hcases; reflexivity).
  eapply (srz_silent segs _ _ _ (exist _ _ Hq)).
  { apply cnode_lift_nr; [| eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno]].
    intros y eff m' evs Hy _. cbn in Hy |- *. injection Hy as <-.
    rewrite (brk_refusal_b_eq segs ms _ model _ Hno), H0. unfold brk_refusal_b, w_is0. rewrite bv_eqb_refl. reflexivity. }
  intros [r Hr]. cbn [proj1_sig].
  pose proof (proj1 (Hcases r) Hr) as Er. subst r.
  rewrite H0, brk_zeros_query, brk_unmaps_keep.
  rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta.
  unfold ms. rewrite adv_ret_epend. exact Hc.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_brk_grow_grant_lazy : forall regs (pc : word) mem rom model w (d : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
  brk_grow_adm d model = true ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                              (zfill b (Z_to_bv 64 d) mem) rom)
                        (brk_grown_model d model)) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w d KB HF HE Hh H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HB.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> (r = b \/ (r = req /\ Mmap.brk_grow_ok model req req = true))).
  { intros r. rewrite H0. apply brk_r_ok_grow_cases; fold h; fold b; rewrite ?Hureq; lia. }
  assert (Hgrow : brk_resolution_ok model (ms_gpr ms 0) req)
    by (apply Hcases; right; split; [reflexivity | exact Hadm]).
  assert (Hneq : req <> b).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E. unfold b in E. lia. }
  assert (Hrb : forall r, refusal_b (sys_input segs ms (getr regs 17)) model r = bv_eqb r b).
  { intros r. rewrite (brk_refusal_b_eq segs ms _ model r Hno), H0. unfold brk_refusal_b. fold h. fold b.
    unfold w_is0. rewrite (bv_eqb_neq _ _ Hneq).
    replace (bv_eqb req (Z_to_bv 64 0)) with false
      by (symmetry; apply bv_eqb_neq; intros E; apply (f_equal bv_unsigned) in E; rewrite Hureq in E;
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E; lia).
    unfold min_brk. fold h. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
  set (I := {r : word | brk_resolution_ok model (ms_gpr ms 0) r}).
  set (keep := fun i : I => negb (bv_eqb (proj1_sig i) b)).
  assert (Hk0 : keep (exist _ req Hgrow) = true) by (unfold keep; cbn [proj1_sig]; rewrite (bv_eqb_neq _ _ Hneq); reflexivity).
  apply (srz_prune segs ms model (getr regs 17) I
           (fun i => mkEffectU (proj1_sig i) [] (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                               (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])
           (fun i => brk_model (ms_gpr ms 0) (proj1_sig i) model) keep (exist _ req Hgrow) KB
           (epend_svc _ _ _ _ _) ltac:(rewrite Hno; reflexivity)
           (node_brk_lazy ms model (getr regs 17) Hh (epend_svc _ _ _ _ _) Hno)).
  - intros [r Hr] Hk. cbn [proj1_sig eff_ret] in *. rewrite Hrb. unfold keep in Hk. cbn [proj1_sig] in Hk.
    destruct (bv_eqb r b); [discriminate Hk | reflexivity].
  - intros [r Hr] Hk. cbn [proj1_sig eff_ret] in *. rewrite Hrb. unfold keep in Hk. cbn [proj1_sig] in Hk.
    destruct (bv_eqb r b); [reflexivity | discriminate Hk].
  - exact Hk0.
  - intros [r Hr] Hk. cbn [proj1_sig]. fold h.
    destruct (proj1 (Hcases r) Hr) as [-> | [-> Hg]].
    + exfalso. unfold keep in Hk. cbn [proj1_sig] in Hk. rewrite bv_eqb_refl in Hk. discriminate Hk.
    + assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
      assert (Hreq0 : req <> Z_to_bv 64 0).
      { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
      rewrite H0. fold b. rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
      unfold brk_page_range.
      rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
      rewrite (page_round_up_Z_aligned (bv_unsigned req))
        by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
      rewrite (proj2 (Z.ltb_lt _ _) Hlt).
      replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
      rewrite Hureq. replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia.
      unfold req, b, h. rewrite (brk_model_grow_eq model d) by assumption.
      unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_brk_grow_blocked_lazy : forall regs (pc : word) mem rom model w (req : word) KA,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  getr regs 10 = req ->
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
  (bv_unsigned b <= bv_unsigned req)%Z ->
  Mmap.brk_grow_ok model req req = false ->
  srealizes segs (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) KA ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KA.
Proof.
  intros regs pc mem rom model w req KA HF HE Hh H17 h b H10 Hpos Hs Hb Hblk HA.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = b).
  { intros r. rewrite H0, (brk_r_ok_grow_cases model req r Hpos Hs Hb). fold h. fold b. split.
    - intros [-> | [-> Hg]]; [reflexivity | rewrite Hblk in Hg; discriminate].
    - intros ->. left. reflexivity. }
  assert (Hkeep : brk_resolution_ok model (ms_gpr ms 0) b) by (apply Hcases; reflexivity).
  eapply (srz_silent segs _ _ _ (exist _ b Hkeep)).
  { destruct (bv_eqb req b) eqn:Ereq.
    - (* [comment removed for export] *)
      apply bv_eqb_eq in Ereq.
      apply cnode_lift_nr; [| eapply node_brk_lazy; [exact Hh | apply epend_svc | exact Hno]].
      intros y eff m' evs Hy _. cbn in Hy |- *. injection Hy as <-.
      rewrite (brk_refusal_b_eq segs ms _ model _ Hno), H0, Ereq. unfold brk_refusal_b. fold h. fold b.
      rewrite bv_eqb_refl. cbn [negb]. rewrite !Bool.andb_false_r. reflexivity.
    - (* [comment removed for export] *)
      assert (Hneq : req <> b) by (intros E; rewrite E, bv_eqb_refl in Ereq; discriminate Ereq).
      apply cnode_lift_forced; [| eapply node_brk_lazy; [exact Hh | apply epend_svc | exact Hno]].
      intros y eff m' evs Hy Hspec. cbn in Hy. injection Hy as <-. cbn [cfg_ms cfg_model] in Hspec |- *.
      apply (brk_ok_iff segs ms (getr regs 17) model eff m' evs Hno) in Hspec as (_ & _ & Hok & _).
      apply Hcases in Hok.
      rewrite (brk_refusal_b_eq segs ms _ model _ Hno), H0, Hok. unfold brk_refusal_b. fold h. fold b.
      unfold w_is0. rewrite (bv_eqb_neq _ _ Hneq), bv_eqb_refl.
      replace (bv_eqb req (Z_to_bv 64 0)) with false
        by (symmetry; apply bv_eqb_neq; intros E; apply (f_equal bv_unsigned) in E;
            change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E; lia).
      unfold min_brk. fold h. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
  intros [r Hr]. cbn [proj1_sig]. fold h.
  pose proof (proj1 (Hcases r) Hr) as Er. subst r. fold b.
  rewrite brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep.
  unfold ms. rewrite adv_ret_epend. exact HA.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma srz_mmap_fixed_noaccess_lazy : forall regs (pc : word) mem rom model w (addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 50 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) rom)
                        (fixed_noaccess_model addr n model)) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Htop H12 H13 H14 H15 n Hrf Hmc HB.
  pose proof (u64_range addr) as Har. pose proof (alloc_top_room (m_vmmaps model)) as Hroom.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as Hprb.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hlen' : (len < 2 ^ 64)%Z) by (unfold two_pow_64, stack_max_size in Hroom; lia).
  assert (Hargs : mmap_fixed_args_ok ms).
  { unfold mmap_fixed_args_ok, ms.
    rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
    intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
  pose proof (fun eff => mmap_fixed_check segs ms (getr regs 17) model eff addr len Hno Hargs
                           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Htop Hrf Hmc) as Hchk.
  cbv zeta in Hchk. fold n in Hchk.
  assert (Haddr_ne : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. unfold stack_max_size, two_pow_64 in *. lia. }
  pose (effs := fun i : three => match i with
                           | T1 => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | T2 => mkEffectU addr [] [] [(addr, n)] [] []
                           | T3 => mkEffectU (errno_ret ENOMEM) [] [] [(addr, n)] [] [] end).
  pose (ms' := fun i : three => match i with
                          | T1 => model
                          | T2 => fixed_noaccess_model addr n model
                          | T3 => fixed_destroyed_model addr n model end).
  pose (keep := fun i : three => match i with T2 => true | _ => false end).
  apply (srz_prune segs ms model (getr regs 17) three effs ms' keep T2 KB (epend_svc _ _ _ _ _) ltac:(rewrite Hno; reflexivity)).
  - apply (node_chk_noacc segs ms model (getr regs 17) three effs ms' Hh (epend_svc _ _ _ _ _)).
    + intros [| |]; cbn [effs ms']; rewrite Hchk.
      * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
      * rewrite Haddr_ne, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
      * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos), (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->). rewrite (mmap_errnos_is_ENOMEM e He).
        destruct us.
        -- injection Hc as <- <-. exists T1. repeat split; reflexivity.
        -- destruct (listNN_eqb (p :: us) [(addr, n)]) eqn:Hl; [|discriminate].
           apply listNN_eqb_eq in Hl. rewrite Hl. injection Hc as <- <-. exists T3. repeat split; reflexivity.
      * destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
        destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
        apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
        exists T2. repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; [discriminate|]; destruct (listNN_eqb _ _); discriminate|].
      destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool; discriminate.
    + intros [| |]; cbn [ms']; [exact Hh | unfold fixed_noaccess_model | unfold fixed_destroyed_model];
        rewrite vm_forget_range_halted, with_vmmaps_halted; exact Hh.
    + intros [| |]; reflexivity.
  - intros [| |] Hk; try discriminate Hk. cbn [effs eff_ret]. rewrite (mmap_refusal_b segs ms _ model _ Hno). exact Haddr_ne.
  - intros [| |] Hk; try discriminate Hk; cbn [effs eff_ret]; apply errno_refusal; first [exact Hno | exact ENOMEM_in_mmap_errnos].
  - reflexivity.
  - intros [| |] Hk; try discriminate Hk. cbn [effs ms']. unfold ms. rewrite adv_unmaps1_epend. exact HB.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma srz_mprotect_lazy : forall regs (pc : word) mem rom model w (addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 226 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  getr regs 12 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mprotect_budget_ok model addr n = true ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill addr n mem) rom)
                        (mprotect_model addr n model)) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len KB HF HE Hh H17 H10 Hal H11 Hlen Hnw H12 n Hna Hma Hbud HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 226%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (fun eff => mprotect_check segs ms (getr regs 17) model eff addr len Hno
                           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal
                           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hnw
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12) Hna Hma) as Hchk.
  cbv zeta in Hchk. fold n in Hchk. rewrite Hbud in Hchk.
  pose (I := (unit + unit)%type).
  pose (effs := fun i : I => match i with
                           | inl _ => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | inr _ => mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] [] end).
  pose (ms' := fun i : I => match i with inl _ => model | inr _ => mprotect_model addr n model end).
  pose (keep := fun i : I => match i with inl _ => false | inr _ => true end).
  apply (srz_prune segs ms model (getr regs 17) I effs ms' keep (inr tt) KB (epend_svc _ _ _ _ _) ltac:(rewrite Hno; reflexivity)).
  - apply (node_chk_noacc segs ms model (getr regs 17) I effs ms' Hh (epend_svc _ _ _ _ _)).
    + intros [[] | []]; cbn [effs ms']; rewrite Hchk.
      * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mprotect_errnos). reflexivity.
      * change (errno_ret_in mprotect_errnos (Z_to_bv 64 0)) with false.
        unfold w_is0. rewrite bv_eqb_refl. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mprotect_errnos r) eqn:Er.
      * destruct zs; [|discriminate]. injection Hc as <- <-.
        destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->).
        rewrite (mprotect_errnos_is_ENOMEM e He). exists (inl tt). repeat split; reflexivity.
      * cbn [andb] in Hc. destruct (w_is0 r) eqn:E0; [|discriminate].
        destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
        apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
        unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r.
        exists (inr tt). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mprotect_errnos r); [destruct zs; discriminate|].
      cbn [andb] in Hc. destruct (w_is0 r && listNN_eqb zs [(addr, n)])%bool; discriminate.
    + intros [[] | []]; cbn [ms']; [exact Hh | unfold mprotect_model; rewrite with_vmmaps_halted; exact Hh].
    + intros [[] | []]; reflexivity.
  - intros [[] | []] Hk; [discriminate Hk|]. cbn [effs eff_ret]. rewrite (mprotect_refusal_b segs ms _ model _ Hno). reflexivity.
  - intros [[] | []] Hk; [|discriminate Hk]. cbn [effs eff_ret]. rewrite (mprotect_refusal_b segs ms _ model _ Hno).
    apply errno_ret_in_intro. exact ENOMEM_in_mprotect_errnos.
  - reflexivity.
  - intros [[] | []] Hk; [discriminate Hk|]. cbn [effs ms']. unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

End WithSegs.
End AsanNodesBrk.
