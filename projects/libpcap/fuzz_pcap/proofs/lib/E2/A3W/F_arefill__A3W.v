(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MM_syscalls WStr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apopulate.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agetfrom__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepotKit__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_arefill.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MM_syscalls WStr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apopulate. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agetfrom__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_aensure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apopulate OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_agetfrom.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepotKit__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac alia_t1 := zify_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac solve_acc_with_t1 H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true)); alia_t1
      end
  | |- acc_in ?RNG (?x, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_varZ RNG lo len x n nz H (@eq_refl Z nz)); alia_t1
      end
  end.
Local Ltac acc_hint ::= lazymatch goal with |- acc_in ?RNG _ => match goal with H : rng RNG _ _ |- _ => solve_acc_with_t1 H end end.
(* [comment removed for export] *)
Local Ltac flia ::= flia_rl.
Local Ltac alia ::= alia_rl.
Local Ltac solve_acc1 ::= solve_acc1_rl.
Local Ltac slia ::= slia_rl.
Local Ltac tlia ::= tlia_rl.
Local Ltac slm_footprint_with segs m m' Heq a bs n Hn Ha Hl ::= slm_footprint_with_d0 segs m m' Heq a bs n Hn Ha Hl.   (* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. (nd_pre HP 3%nat; intros [lo' hi'] HI [H1 H2]; nd_post). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
(* [comment removed for export] *)
Local Ltac refresh H := let X := fresh in pose proof H as X; clear H; rename X into H.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition refill_entry := 0x38ad8.
End CANSEC1.
Notation REFILL_STACK := 672 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma v_divuw_lit : forall x y, 0 <= x < 2^31 -> 0 < y < 2^31 -> v_divuw (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x / y).
Proof.
  intros x y Hx Hy. unfold v_divuw. rewrite !unsigned_lit by lia.
  unfold bv_wrap, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. replace (Z.of_N (32 - 1)) with 31 by reflexivity.
  change (2^31) with 2147483648 in *.
  rewrite (Z.mod_small y) by lia. replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite (Z.mod_small x) by lia. f_equal.
  assert (B : 0 <= x / y <= x) by (Z.div_mod_to_equations; nia).
  Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Definition arec_hdr (L : alayout) (m : amem) (j cnt mc cs : Z) : Prop :=
  rw_cells asegs m (acache_addr L j) [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 cs)].

End CANSEC2.
Ltac zfact := first [ split; zfact | vm_compute; first [reflexivity | discriminate | intros ?; discriminate] ].
Section CANSEC3. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma mc_le4 : forall i, 1 <= i <= 4 -> max_cached i = 16 /\ 8 <= 1024 / (32 * i).
Proof.
  intros i Hi. assert (E : i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
  repeat (destruct E as [->|E]; [zfact|]). subst; zfact.
Qed.
#[using="Type"] Lemma mc_mid : forall i, 5 <= i <= 16 -> max_cached i = 2 * (1024 / (32 * i)) /\ 1 <= 1024 / (32 * i) < 8.
Proof.
  intros i Hi. assert (E : i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16) by lia.
  repeat (destruct E as [->|E]; [zfact|]). subst; zfact.
Qed.
#[using="Type"] Lemma mc_big : forall i, 17 <= i <= 30 -> max_cached i = 2 /\ 768 <= size_of_class i <= 65536 /\ 1024 / size_of_class i <= 1.
Proof.
  intros i Hi. assert (E : i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/ i = 30) by lia.
  repeat (destruct E as [->|E]; [zfact|]). subst; zfact.
Qed.
#[using="Type"] Lemma mc_31 : max_cached 31 = 16. Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma size_formula2 : forall i, 17 <= i <= 30 ->
  Z_to_bv 64 (Z.land ((Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl i 63))) 63) mod 18446744073709551616)
                     (Z.shiftr ((Z.shiftl 512 ((Z.shiftr (i - 16) 1) mod 64)) mod 18446744073709551616) 1)
              + Z.shiftl 512 ((Z.shiftr (i - 16) 1) mod 64)) = Z_to_bv 64 (size_of_class i).
Proof.
  intros i Hi.
  assert (E : i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/ i = 30) by lia.
  repeat (destruct E as [->|E]; [apply f_equal; vm_compute; reflexivity|]). subst. apply f_equal. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint ic_W (L : alayout) (i : Z) (d : nat) : list (Z * Z) :=
  match d with O => [] | Datatypes.S d' => (acache_addr L i + 4, acache_addr L i + 16) :: ic_W L (i + 1) d' end.

#[using="Type"] Lemma munch_cons_trans : forall p W m m1 m', munch [p] m m1 -> munch W m1 m' -> munch (p :: W) m m'.
Proof.
  intros [lo hi] W m m1 m' A B. eapply munch_trans; [eapply munch_weaken; [| exact A] | eapply munch_weaken; [| exact B]];
    unfold sub_fp; intros x Hx; cbn [outside] in *; tauto.
Qed.

#[using="Type"] Lemma ic_W_disjoint_below : forall L i d A n, A + n <= acache_addr L i + 4 -> disjoint_from (ic_W L i d) A n.
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i A n H; cbn [ic_W disjoint_from]; [exact I|].
  split; [unfold acache_addr in *; lia|]. apply IH. unfold acache_addr in *; lia.
Qed.

#[using="Type"] Lemma ic_W_disjoint_gen : forall L i d A n, (A + n <= acache_addr L i + 4 \/ al_t L + 2768 <= A) -> i + Z.of_nat d <= 32 -> 1 <= i ->
  disjoint_from (ic_W L i d) A n.
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i A n H Hd Hi; cbn [ic_W disjoint_from]; [exact I|].
  split; [unfold acache_addr in *; lia|]. apply IH; unfold acache_addr in *; lia.
Qed.

#[using="Type"] Lemma ic_W_disjoint_chunks : forall L i d c, disjoint_from (ic_W L i d) (acache_addr L c + 16) 64.
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i c; cbn [ic_W disjoint_from]; [exact I|].
  split; [unfold acache_addr; lia|]. apply IH.
Qed.

(* [comment removed for export] *)
End CANSEC3.
Ltac icdj tac := cbn [disjoint_from cells_size csize Nat.add length]; split; [tac | first [apply ic_W_disjoint_chunks | apply ic_W_disjoint_gen; [tac | clear; cbn; lia | clear; lia]]].

Section CANSEC4. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma ic_W_outside : forall L i d x, (x < acache_addr L i + 4 \/ al_t L + 2768 <= x) -> i + Z.of_nat d <= 32 -> 1 <= i -> outside (ic_W L i d) x.
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i x Hx Hd Hi; cbn [ic_W outside]; [exact I|].
  split; [unfold acache_addr in *; lia|]. apply IH; unfold acache_addr in *; lia.
Qed.

#[using="Type"] Lemma initcache_loop_spec : forall RNG (d : nat) (i : Z) (L : alayout) (cnt : Z -> Z)
    ra sp gp tp s0 s1 a0 a2 a4 t3 t4 t5 t6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (32 - i) -> 1 <= i <= 31 ->
  (forall j, i <= j <= 31 -> arec_hdr L m j (cnt j) 0 0) ->
  mem_inv asegs m -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) ->
  rng RNG (al_t L) 4096 ->
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  evtF asegs RNG (fun ms' => exists a1' a3' a5' t3' t4' t5' m',
      ms' = MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 a0 a1' a2 a3' a4 a5' (Z_to_bv 64 15) (Z_to_bv 64 1024)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6) F (Z_to_bv 64 0x38bd0) fc None m' (seg_rom asegs)
      /\ munch (ic_W L i d) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ (forall j, i <= j <= 31 -> arec_hdr L m' j (cnt j) (max_cached j) (size_of_class j)))
    (MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 a0 (Z_to_bv 64 (acache_addr L i + 8)) a2 (Z_to_bv 64 (32 * i)) a4
             (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15) (Z_to_bv 64 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38b7c) fc None m (seg_rom asegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I RECS MI T0 T1 RT TIC; [lia|]. band_lin.   (* [comment removed for export] *)
  atop_facts.
  pose proof (RECS i ltac:(lia)) as REC. unfold arec_hdr in REC.
  assert (ACE : acache_addr L i = al_t L + 208 + i * 80) by reflexivity.
  pose proof (munch_refl [(acache_addr L i + 4, acache_addr L i + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ ?P _ =>
  assert (TAILI : forall (q : Z) (t5x : word) (mm : amem), 0 <= q <= 8 -> 2 * Z.max 1 q = max_cached i ->
    rw_cells asegs mm (acache_addr L i) [C4 (Z_to_bv 64 (cnt i)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    (forall j, i + 1 <= j <= 31 -> arec_hdr L mm j (cnt j) 0 0) -> mem_inv asegs mm -> munch [(acache_addr L i + 4, acache_addr L i + 16)]%Z m mm -> wmono asegs m mm ->
    evtF asegs RNG P
      (MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 a0 (Z_to_bv 64 (acache_addr L i + 8)) a2 (Z_to_bv 64 (32 * i)) a4
               (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15) (Z_to_bv 64 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (size_of_class i)) (Z_to_bv 64 q) t5x t6)
          F (Z_to_bv 64 0x38b58) fc None mm (seg_rom asegs)))
  end.
  { intros q t5x mm Q QM RECi RECS' MI' MU' WM'. clear REC MI MU WM.
    zstep. zstep. zstep. zstep. zstep.                         (* [comment removed for export] *)
    setreg 29 (Z_to_bv 64 (max_cached i))
      ltac:(apply Z_to_bv_eqm; rewrite <- QM; clear -Q; destruct (Z.ltb_spec q 1); cbn [Z.b2z]; rewrite Z.shiftl_mul_pow2 by lia; rewrite Z.mod_small by lia;
            change (2^1) with 2; lia).
    snapshot [(acache_addr L i + 4, acache_addr L i + 16)]%Z MUs WMs.
    step. step.                                                (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    setreg 11 (Z_to_bv 64 (acache_addr L (i + 1) + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    setreg 13 (Z_to_bv 64 (32 * (i + 1))) ltac:(f_equal; clear; lia).
    setreg 15 (Z_to_bv 64 (i + 1 - 16)) ltac:(f_equal; clear; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) => assert (RECS2 : forall j, i + 1 <= j <= 31 -> arec_hdr L m2 j (cnt j) 0 0) end.
    { intros j Hj. unfold arec_hdr. eapply cells_frame; [exact (RECS' j Hj) | exact MUs | exact WMs |]. cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj; lia. }
    step. if_cases KX; zify_cond KX; rewrite ?unsigned_lit in KX by (clear -I; lia).   (* [comment removed for export] *)
    - assert (I31 : i = 31) by (clear -KX I; lia). assert (D0 : d = 0%nat) by (clear -KX I HD; lia). subst d.
      apply evtF_done. do 7 eexists. split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU'|]. split; [exact WM'|]. split; [assumption|].
      intros j Hj. assert (J : j = i) by (clear -Hj I31 I; lia). subst j. unfold arec_hdr.
      lazymatch goal with H : rw_cells asegs _ (acache_addr L i) _ |- _ => exact H end.
    - eapply evtF_mono.
      { eapply (IH (i + 1) L cnt); try eassumption; clear -KX I HD T0 T1 TIC; lia. }
      cbv beta. intros ms' (a1' & a3' & a5' & t3' & t4' & t5' & m' & -> & MU2 & WM2 & MI2 & RECS3).
      do 7 eexists. split; [reflexivity|].
      split; [cbn [ic_W]; eapply munch_cons_trans; [exact MU' | exact MU2]|].
      split; [eapply wmono_trans; [exact WM' | exact WM2]|]. split; [exact MI2|].
      intros j Hj. destruct (Z.eq_dec j i) as [->|NE].
      + unfold arec_hdr. eapply cells_frame; [| exact MU2 | exact WM2 |]; [lazymatch goal with H : rw_cells asegs _ (acache_addr L i) _ |- _ => exact H end|].
        cbn [cells_size csize Nat.add]. apply ic_W_disjoint_below. unfold acache_addr. clear -I; lia.
      + apply RECS3. clear -Hj NE; lia. }
  assert (RECS' : forall j, i + 1 <= j <= 31 -> arec_hdr L m j (cnt j) 0 0) by (intros j Hj; apply RECS; clear -Hj; lia).
  step. if_cases K31; zify_cond K31; rewrite ?unsigned_lit in K31 by (clear -I; lia).   (* [comment removed for export] *)
  { (* [comment removed for export] *)
    assert (I31 : i = 31) by (clear -K31 I; lia).
    step. step. step. step. if_lit.                            (* [comment removed for export] *)
    step. step. step.                                          (* [comment removed for export] *)
    replace (Z_to_bv 64 64) with (Z_to_bv 64 (size_of_class i) : word) by (rewrite I31; reflexivity).
    eapply (TAILI 8); [clear; lia | rewrite I31, mc_31; reflexivity | exact REC | exact RECS' | exact MI | exact MU | exact WM]. }
  zstep. setreg 29 (Z_to_bv 64 i) ltac:(f_equal; clear; lia).   (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. if_cases K17; zify_cond K17; rewrite ?unsigned_lit in K17 by (clear -I; lia).   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    setreg 29 (Z_to_bv 64 (1024 / (32 * i))) ltac:(symmetry; apply v_divuw_lit; clear -I; lia).
    assert (SZE : size_of_class i = 32 * i) by (unfold size_of_class; replace (i <=? 16) with true by (symmetry; apply Z.leb_le; clear -K17; lia); reflexivity).
    pose proof TAILI as TL. rewrite SZE in TL. clear TAILI.
    step. step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (clear -I; Z.div_mod_to_equations; nia).   (* [comment removed for export] *)
    + destruct (mc_mid i ltac:(clear -I K17 K8; assert (5 <= i) by (destruct (Z_lt_le_dec i 5); [exfalso; pose proof (proj2 (mc_le4 i ltac:(lia))); lia| lia]); lia)) as [MC Q8].
      eapply (TL (1024 / (32 * i))); [clear -Q8; lia | rewrite MC; clear -Q8; lia | exact REC | exact RECS' | exact MI | exact MU | exact WM].
    + step. step.                                              (* [comment removed for export] *)
      destruct (mc_le4 i ltac:(clear -I K8; assert (i <= 4) by (destruct (Z_lt_le_dec 4 i); [exfalso; pose proof (proj2 (mc_mid i ltac:(lia))); lia| lia]); lia)) as [MC Q8].
      eapply (TL 8); [clear; lia | rewrite MC; reflexivity | exact REC | exact RECS' | exact MI | exact MU | exact WM].
  - (* [comment removed for export] *)
    do 7 zstep.                                                (* [comment removed for export] *)
    setreg 28 (Z_to_bv 64 (size_of_class i)) ltac:(symmetry; apply size_formula2; clear -I K17 K31; lia).
    (nd_pre (mc_big i ltac:(clear -I K17 K31; lia)) 3%nat; intros MC SB Q1; nd_post).
    step.                                                      (* [comment removed for export] *)
    setreg 29 (Z_to_bv 64 (1024 / size_of_class i)) ltac:(symmetry; apply v_divuw_lit; clear -SB; lia).
    step. step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (clear -SB Q1; Z.div_mod_to_equations; nia).   (* [comment removed for export] *)
    2: { exfalso. clear -K8 Q1. lia. }
    eapply (TAILI (1024 / size_of_class i)); [clear -Q1 SB; Z.div_mod_to_equations; nia | rewrite MC; clear -Q1 SB; Z.div_mod_to_equations; nia | exact REC | exact RECS' | exact MI | exact MU | exact WM].
Qed.

#[using="Type"] Lemma max_cached_range : forall c, 1 <= c <= 31 -> 2 <= max_cached c <= 16 /\ max_cached c mod 2 = 0.
Proof.
  intros c Hc. unfold max_cached.
  assert (E : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16
              \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30 \/ c = 31) by lia.
  repeat (destruct E as [->|E]; [zfact|]). subst; zfact.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KKref {R} (k : astate -> bool -> AM R) (c n : Z) (st2 : astate) : AM R :=
  k (put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2) true.

(* [comment removed for export] *)
Definition refill_tail_ret (L : alayout) (RNG : footprint) (sp : word) (st1 : astate) (c lo : Z) (fl chunks0 : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st1 c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  fp_le RNG RNG' /\
  exists mu' mfa' ncnt sj' (stm' stn' : word),
  let nf2 := nf + ncnt in let au2 := au + ncnt * S in
     (   mu' = mu
      \/ (nf < n /\ mu < au + (n - nf) * S /\ mu' = mu + rup (au + (n - nf) * S - mu) K_USER_MAP
          /\ rw_cells asegs m' (RB + mu) [CB (Z.to_nat (mu' - mu)) (repeat (Z_to_bv 8 0) (Z.to_nat (mu' - mu)))]
          /\ fill_at m' (shad (RB + mu)) (shlen (mu' - mu)) 0xfa
          /\ rng RNG' (RB + mu) (mu' - mu) /\ rng RNG' (shad (RB + mu)) (shlen (mu' - mu)) /\ fp_bw RNG'))
  /\ mu <= mu' <= K_FREEARR_OFF /\ mu' mod K_USER_MAP = 0
  /\ ((n <= nf /\ ncnt = 0) \/ (nf < n /\ ncnt = (mu' - au) / S)) /\ 0 <= ncnt /\ au2 <= mu'
  /\ (   mfa' = mfa
      \/ (mfa < 4 * nf2 /\ mfa' = rup (4 * nf2) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf2 <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
  /\ n <= nf2
  /\ u32arr asegs m' FA (fl ++ fvals au S (Z.to_nat ncnt))
  /\ junk_at m' (FA + 4 * nf2) (mfa' - 4 * nf2)
  /\ get_cls st2 c = mkAClass mu' au2 nf2 mfa' (c_count r)
  /\ (st2 = st1 \/ st2 = put_cls c (get_cls st2 c) st1)
  /\ munch [(bv_unsigned sp - REFILL_STACK, bv_unsigned sp);
            (RB + mu, RB + mu'); (shad (RB + mu), shad (RB + mu) + shlen (mu' - mu));
            (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
            (al_t L + 2792, al_t L + 2800); (al_t L + 2800, al_t L + 3168);
            (RI, RI + 8); (RI + 16, RI + 56); (RI + 68, RI + 69); (RI + 72, RI + 80);
            (acache_addr L c, acache_addr L c + 4); (CHK, CHK + 4 * n)]%Z m m'
  /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' (RI + 16)
       [C8 (Z_to_bv 64 (nf2 - n)); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 au2); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu'); C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' (RI + 68) [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m' (RI + 72) [C8 stn']
  /\ u64arr asegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ rw_cells asegs m' (al_t L + 2792) [C8 stm']
  /\ rw_cells asegs m' (acache_addr L c) [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)]
  /\ u32arr asegs m' CHK (skipn (Z.to_nat (nf2 - n)) (fl ++ fvals au S (Z.to_nat ncnt)) ++ skipn (Z.to_nat n) chunks0)
  /\ azero m' (shad (RB + mu')) (shlen (K_FREEARR_OFF - mu'))
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

Definition refill_tail_spec__stmt : Prop := forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (rav sp gp tp t0 t1 t2 s0v s1v a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rax a1x a3x : word)
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st1 : astate) (c lo cntc : Z) (sj fl chunks0 : list word) (stm stn : word) (fj fr0 : list byte),
  let r := get_cls st1 c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk asegs m lo (bv_unsigned sp + -32) -> ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  rw_cells asegs m (bv_unsigned sp + -32) [CB 8 fr0; C8 s1v; C8 s0v; C8 rav] ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  u32arr asegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  rw_cells asegs m (acache_addr L c) [C4 (Z_to_bv 64 cntc); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)] ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st1 = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_tail_ret L RNG sp st1 c lo fl chunks0 m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc rav) fc None m' (seg_rom asegs))) ->
  evtF asegs RNG (fun ms' => implS asegs RNG (aembed ATOP (gfa_tree st1 c n k (KKref k c n))) (epostF Q) ms')
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1v
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 (max_cached c)) (Z_to_bv 64 AINSTANCE) a3x (Z_to_bv 64 c) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38af8) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 1).
Variable k : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 3).
Variable rav : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 10).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 11).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 12).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 13).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 14).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 15).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 16).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 17).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 18).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 19).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 20).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 21).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 22).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 23).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 24).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 25).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 26).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 27).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 28).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 29).
Variable rax : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 30).
Variable a1x : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 31).
Variable a3x : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 35).
Variable L : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 36).
Variable st1 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 37).
Variable c : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 39).
Variable cntc : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 40).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 41).
Variable fl : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 42).
Variable chunks0 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 43).
Variable stm : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 44).
Variable stn : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 45).
Variable fj : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 46).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 47).
Let n := max_cached c / 2.
#[using="a1x n"] Lemma refill_tail_spec__body : ltac:(let T := type of (fun (h : refill_tail_spec__stmt) => h RNG R k Q rav sp gp tp t0 t1 t2 s0v s1v a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rax a1x a3x F fc m L st1 c lo cntc sj fl chunks0 stm stn fj fr0) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (k, (Q, (rav, (sp, (gp, (tp, (t0, (t1, (t2, (s0v, (s1v, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (rax, (a1x, (a3x, (F, (fc, (m, (L, (st1, (c, (lo, (cntc, (sj, (fl, (chunks0, (stm, (stn, (fj, fr0)))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP FR MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ REC CH LCH AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RTLS RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  pose proof T0 as TB. unfold sclr, KLS in TB.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR. box TCX. box SCX. box TSP.
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCE].
  chg (max_cached c / 2) n.
  assert (N : 1 <= n <= 8 /\ 2 * n = max_cached c) by (subst n; clear -MCR MCE; Z.div_mod_to_equations; lia). destruct N as [N N2].
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  pose proof (munch_refl [(bv_unsigned sp - REFILL_STACK, bv_unsigned sp)]%Z m) as MUN. pose proof (wmono_refl asegs m) as WM.
  zstep.                                                       (* [comment removed for export] *)
  setreg 9 (Z_to_bv 64 n) ltac:(subst n; f_equal; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296;
                                replace (Z.of_N (32-1)) with 31 by reflexivity; change (2^31) with 2147483648;
                                rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^1) with 2; clear -MCR; Z.div_mod_to_equations; lia).
  zstep. zstep. zstep.                                         (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (al_t L + 2768)) ltac:(f_equal; clear; lia).
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  apply evtF_done. name_sp sp (-32).
  eapply getfrom_spec with (lo := lo) (L := L);
  try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length _ = _ => first [exact LSJ | exact LFL | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; eapply rng_sub'; [exact RSTK|]; clear -LO SPR CEIL; lia
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => exact RCTX
       | |- rng _ (al_t _) _ => exact RT
       | |- @eq word _ _ => first [reflexivity | exact TP | rewrite ACE; f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; rewrite ?ACE; first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM N HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC TB CXI; lia]).
  (* [comment removed for export] *)
  intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' GR.
  unfold getfrom_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP in GR. cbv zeta in GR.
  (nd_pre GR 37%nat; intros FPLE mu' mfa' ncnt sj' stm' stn' UD MUB MUM' NCE NC0 NCS FD NEWB NEWM NEWMOD NLE AR JR GC2 ST2E MU2 WM2 MI2 ST2 MTX2 REG2 EXH2 STN2 STATS2 LSJ2 STM2 CH2 AZU2 AZF2 MC2; nd_post).
  box UD. box FD. box NCE. box ST2E. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RTLS. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RT.
  assert (SHF : shad (afreearr L c + c_mapped_free_array (get_cls st1 c)) + shlen (mfa' - c_mapped_free_array (get_cls st1 c)) <= 0x10007fff8000
                /\ shad (aregion L c + c_mapped_user (get_cls st1 c)) + shlen (mu' - c_mapped_user (get_cls st1 c)) <= 0x10007fff8000
                /\ 0x2008fff7000 <= shad (afreearr L c + c_mapped_free_array (get_cls st1 c))
                /\ 0x2008fff7000 <= shad (aregion L c + c_mapped_user (get_cls st1 c))).   (* [comment removed for export] *)
  { unfold afreearr, aregion, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296. rewrite !shad_div, !shlen_div. unfold ASHOFF.
    clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM. Z.div_mod_to_equations. lia. }
  (nd_pre SHF 4%nat; intros SHF1 SHF2 SHF3 SHF4; nd_post).
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296 /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384).
  { unfold aregion_info, afreearr, aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  (nd_pre GEO 3%nat; intros RIE RBE FAE; nd_post).
  xport FR MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE RBE FAE ACE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 N Y TIC TB SHF3 SHF4; lia).
  xport REC MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE RBE FAE ACE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 N Y TIC TB SHF3 SHF4; lia).
  clear ST MI MC MTX REG EXH STN STATS STM FL FJ CH AZU AZF.
  replace (ret_pc (Z_to_bv 64 232216)) with (Z_to_bv 64 232216 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_lit.                                                (* [comment removed for export] *)
  snapshot [(acache_addr L c, acache_addr L c + 4)]%Z MUc WMc.
  box MTX2. box REG2. box EXH2. box STN2. box CH2. box STATS2. box STM2. box AR. box MU2. clear MUN WM.
  step.                                                        (* [comment removed for export] *)
  unbox MU2.
  carry AR MUc WMc ltac:(rewrite length_app, fvals_length, LFL, FAE, ACE; ub TSP; clear -SP1 SP2 HC T0 T1 NF NC0 NEWB Y TIC TB; lia).
  carry MTX2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry REG2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry EXH2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry STN2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry CH2 MUc WMc ltac:(rewrite length_app, !length_skipn, length_app, fvals_length, LFL, LCH, ACE; clear -HC NC0 N NLE NF; lia).
  carry STATS2 MUc WMc ltac:(rewrite LSJ2, ACE; clear -HC; lia).
  carry STM2 MUc WMc ltac:(rewrite ACE; clear -HC; lia).
  lazymatch goal with |- evtF _ _ ?P _ => remember P as PP eqn:HPP end.
  refresh RSTK. do 5 step.                                            (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -32) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  subst PP. apply evtF_done. eapply KONT.
  unfold refill_tail_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP. cbv zeta. fold n.
  split; [exact FPLE|]. exists mu', mfa', ncnt, sj', stm', stn'.
  split. { with_box UD ltac:(destruct DX as [Emu|(LT1 & LT & Emu & ZN & FI & G1 & G2 & BW)];
           [ left; exact Emu
           | right; split; [exact LT1|]; split; [exact LT|]; split; [exact Emu|]; split; [| split; [| split; [exact G1| split; [exact G2| exact BW]]]];
             [ eapply cells_frame; [exact ZN | exact MUc | exact WMc |]; cbn [disjoint_from cells_size csize Nat.add]; rewrite ?Z2Nat.id by (clear -MUB; lia)
             | eapply fill_frame; [exact FI | exact MUc | exact WMc |]; intros _; cbn [disjoint_from] ];
             ub TSP; rewrite RBE, ACE in *; clear -SPR CEIL LO SP1 SP2 HC T0 T1 MU MUB SHF2 Y TIC TB SHF3 SHF4; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia ]). }
  split; [exact MUB|]. split; [exact MUM'|]. split; [unboxed NCE|]. split; [exact NC0|]. split; [exact NCS|].
  split. { with_box FD ltac:(destruct DX as [Emfa|(LT & Emfa & FI & G1 & G2 & BW)];
           [ left; exact Emfa
           | right; split; [exact LT|]; split; [exact Emfa|]; split; [| split; [exact G1| split; [exact G2| exact BW]]];
             eapply fill_frame; [exact FI | exact MUc | exact WMc |]; intros _; cbn [disjoint_from];
             ub TSP; rewrite FAE, ACE in *; clear -SPR CEIL LO SP1 SP2 HC T0 T1 MFA NF NEWB NEWM SHF1 Y TIC TB; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia ]). }
  split; [exact NEWB|]. split; [exact NEWM|]. split; [exact NEWMOD|]. split; [exact NLE|].
  split; [exact AR|].
  split. { eapply junk_frame; [exact JR | exact MUc | exact WMc |]. intros _; cbn [disjoint_from]. rewrite FAE, ACE. ub TSP; clear -SP1 SP2 HC T0 T1 NF NC0 MFA NEWB NEWM Y TIC TB; lia. }
  split; [exact GC2|]. split; [unboxed ST2E|].
  split. { eapply munch_trans; [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MUc]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
  split; [exact WM2|]. split; [assumption|]. split; [assumption|].
  split; [exact MTX2|]. split; [exact REG2|]. split; [exact EXH2|]. split; [exact STN2|]. split; [exact STATS2|]. split; [exact LSJ2|]. split; [exact STM2|].
  split; [assumption|]. split; [exact CH2|].
  split. { eapply azero_frame; [exact AZU2 | exact MUc | exact WMc |]. intros _; cbn [disjoint_from]. rewrite RBE, ACE. rewrite shad_div, shlen_div. unfold ASHOFF.
           ub TSP; clear -SP1 SP2 HC T0 T1 MU MUB Y TIC TB; Z.div_mod_to_equations; lia. }
  split. { eapply azero_frame; [exact AZF2 | exact MUc | exact WMc |]. intros _; cbn [disjoint_from]. rewrite FAE, ACE. rewrite shad_div, shlen_div. unfold ASHOFF.
           ub TSP; clear -SP1 SP2 HC T0 T1 MFA NF NEWB NEWM Y TIC TB; Z.div_mod_to_equations; lia. }
  eapply m3_cells_frame; [exact MC2 | exact MUc | exact WMc |]. ub TCX. unfold AIMG_HI, AIMG_LO.
  apply Forall_cons; [cbn [fst snd]; rewrite ACE; clear -CX0 CX1 T0 T1 TIC HC Y TB CXI; with_band CX0 ltac:(lia) | apply Forall_nil].   (* [comment removed for export] *)
Qed.
End Zd1.
#[using="Type"] Lemma refill_tail_spec : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (rav sp gp tp t0 t1 t2 s0v s1v a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rax a1x a3x : word)
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st1 : astate) (c lo cntc : Z) (sj fl chunks0 : list word) (stm stn : word) (fj fr0 : list byte),
  let r := get_cls st1 c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk asegs m lo (bv_unsigned sp + -32) -> ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  rw_cells asegs m (bv_unsigned sp + -32) [CB 8 fr0; C8 s1v; C8 s0v; C8 rav] ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  u32arr asegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  rw_cells asegs m (acache_addr L c) [C4 (Z_to_bv 64 cntc); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)] ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st1 = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_tail_ret L RNG sp st1 c lo fl chunks0 m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc rav) fc None m' (seg_rom asegs))) ->
  evtF asegs RNG (fun ms' => implS asegs RNG (aembed ATOP (gfa_tree st1 c n k (KKref k c n))) (epostF Q) ms')
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1v
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 (max_cached c)) (Z_to_bv 64 AINSTANCE) a3x (Z_to_bv 64 c) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38af8) fc None m (seg_rom asegs)).
Proof. exact refill_tail_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition refill_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c lo : Z) (fl chunks0 : list word) (cnt : Z -> Z) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  exists m1, munch ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z m m1 /\ wmono asegs m m1
  /\ refill_tail_ret L RNG sp (init_cache st) c lo fl chunks0 m1 st2 RNG' m'
  /\ (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m' j (cnt j) (max_cached j) (size_of_class j)).

#[using="Type"] Lemma init_cache_cinit : forall st, a_cinit (init_cache st) = true.
Proof. intros st. unfold init_cache. destruct (a_cinit st) eqn:E; [exact E| reflexivity]. Qed.
#[using="Type"] Lemma init_cache_cls : forall st c, get_cls (init_cache st) c = get_cls st c.
Proof. intros st c. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
#[using="Type"] Lemma init_cache_space : forall st, a_space_beg (init_cache st) = a_space_beg st.
Proof. intros st. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.

(* [comment removed for export] *)
Definition refill_tailK__stmt : Prop := forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a5x a6x a7x s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6 (a3x : word)
    (F : bvmap 5 word) fc (m m1 : amem) (L : alayout) (st st1 : astate) (c lo cntc : Z) (cnt : Z -> Z) (sj fl chunks0 : list word) (stm stn : word) (fj fr0 : list byte),
  let r := get_cls st c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  st1 = init_cache st ->
  ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK -> tp = Z_to_bv 64 ATP ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  u32arr asegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  (* [comment removed for export] *)
  munch ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
  stk asegs m1 lo (bv_unsigned sp + -32) ->
  rw_cells asegs m1 (bv_unsigned sp + -32) [CB 8 fr0; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m1 (acache_addr L c) [C4 (Z_to_bv 64 cntc); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)] ->
  (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m1 j (cnt j) (max_cached j) (size_of_class j)) ->
  evtF asegs RNG (fun ms' => implS asegs RNG (aembed ATOP (gfa_tree st1 c n k (KKref k c n))) (epostF Q) ms')
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 (max_cached c)) (Z_to_bv 64 AINSTANCE) a3x (Z_to_bv 64 c) a5x a6x a7x
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6)
        F (Z_to_bv 64 0x38af8) fc None m1 (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 1).
Variable k : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 12).
Variable a5x : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 13).
Variable a6x : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 14).
Variable a7x : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 15).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 16).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 17).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 18).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 19).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 20).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 21).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 22).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 23).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 24).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 25).
Variable t3x : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 26).
Variable t4x : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 27).
Variable t5x : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 28).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 29).
Variable a3x : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 30).
Variable F : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 31).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 32).
Variable m : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 33).
Variable m1 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 34).
Variable L : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 36).
Variable st1 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 37).
Variable c : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 39).
Variable cntc : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 40).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 41).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 42).
Variable fl : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 43).
Variable chunks0 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 44).
Variable stm : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 45).
Variable stn : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 46).
Variable fj : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 47).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 48).
#[using="Type"] Lemma refill_tailK__body : ltac:(let T := type of (fun (h : refill_tailK__stmt) => h RNG R k Q ra sp gp tp t0 t1 t2 s0 s1 a5x a6x a7x s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6 a3x F fc m m1 L st st1 c lo cntc cnt sj fl chunks0 stm stn fj fr0) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (k, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a5x, (a6x, (a7x, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3x, (t4x, (t5x, (t6, (a3x, (F, (fc, (m, (m1, (L, (st, (st1, (c, (lo, (cntc, (cnt, (sj, (fl, (chunks0, (stm, (stn, (fj, fr0))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros E1 CEIL LO TP MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ CH LCH AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RTLS RSTK RCTX RT RRI RFA CXI TIC KONT MU1 WM1 MI1 ST1 FR1 REC1 RECS1. band_lin.   (* [comment removed for export] *)
  pose proof T0 as TB. unfold sclr, KLS in TB.   (* [comment removed for export] *)
  unfold AIMG_HI, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR. box TCX. box SCX. box TSP.
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCE].
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296 /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384).
  { unfold aregion_info, afreearr, aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  (nd_pre GEO 3%nat; intros RIE RBE FAE; nd_post).
  assert (WOK1 : Forall (fun iv => ((AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= ATPv + -88 \/ ATPv + -80 <= fst iv)) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv))
                  ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z).
  { ub TCX. unfold AIMG_HI, AIMG_LO. apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 T0 T1 TIC Y TB CXI; with_band CX0 ltac:(lia) |].   (* [comment removed for export] *)
    cbn [ic_W]. unfold acache_addr. repeat (apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 T0 T1 TIC Y TB CXI; with_band CX0 ltac:(lia) |]). apply Forall_nil. }   (* [comment removed for export] *)
  assert (GC1 : get_cls st1 c = get_cls st c) by (rewrite E1; apply init_cache_cls).
  assert (SB1 : a_space_beg st1 = al_space_beg L) by (rewrite E1, init_cache_space; exact SBE).
  (* [comment removed for export] *)
  eapply cells_frame in MTX; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply cells_frame in REG; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply cells_frame in EXH; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply cells_frame in STN; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply u64arr_frame in STATS; [| exact MU1 | exact WM1 | rewrite LSJ; icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia)].
  eapply cells_frame in STM; [| exact MU1 | exact WM1 | icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia)].
  eapply u32arr_frame in FL; [| exact MU1 | exact WM1 | rewrite LFL, FAE; icdj ltac:(ub TSP; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 NF MFA Y TIC TB; lia)].
  eapply cells_frame in FJ; [| exact MU1 | exact WM1 | rewrite FAE; icdj ltac:(ub TSP; unfold acache_addr; rewrite ?Z2Nat.id by (clear -NF MFA; lia); clear -SPR CEIL LO SP1 SP2 HC T0 T1 NF MFA Y TIC TB; lia)].
  eapply u32arr_frame in CH; [| exact MU1 | exact WM1 | rewrite LCH; icdj ltac:(rewrite ACE; clear -SPR CEIL LO T0 T1 HC TIC TB; lia)].
  assert (MC1 : m3_cells L m1) by (eapply m3_cells_frame; [exact MC | exact MU1 | exact WM1 | exact WOK1]).
  assert (AZU1 : azero m1 (shad (aregion L c + c_mapped_user (get_cls st c))) (shlen (3758096384 - c_mapped_user (get_cls st c)))).
  { eapply azero_frame; [exact AZU | exact MU1 | exact WM1 |]. intros _. rewrite RBE.
    assert (B : shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st c)) + shlen (3758096384 - c_mapped_user (get_cls st c)) <= 17594333495296
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st c)))   (* [comment removed for export] *)
      by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -SP1 SP2 HC MU MUX; Z.div_mod_to_equations; lia).
    icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 B TIC TB; lia). }
  assert (AZF1 : azero m1 (shad (afreearr L c + c_mapped_free_array (get_cls st c))) (shlen (536870912 - c_mapped_free_array (get_cls st c)))).
  { eapply azero_frame; [exact AZF | exact MU1 | exact WM1 |]. intros _. rewrite FAE.
    assert (B : shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st c)) + shlen (536870912 - c_mapped_free_array (get_cls st c)) <= 17594333495296
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st c)))   (* [comment removed for export] *)
      by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -SP1 SP2 HC MFA NF; Z.div_mod_to_equations; lia).
    icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 B TIC TB; lia). }
  clear MC AZU AZF.
  rewrite <- GC1 in REG, LFL, FJ, AZU1, AZF1, MU, MUX, MUM, AUM, NF, NFA, MFA, MFAM, RFA.
  eapply (refill_tail_spec RNG k Q ra sp gp tp) with (lo := lo) (L := L);
  try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => exact ST1
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => exact MI1
       | |- m3_cells _ _ => exact MC1
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR1
       | |- rw_cells _ _ (acache_addr _ _) _ => exact REC1
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length _ = _ => first [exact LSJ | exact LFL | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU1
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF1
       | |- a_space_beg _ = _ => exact SB1
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => exact RCTX
       | |- rng _ (al_t _) _ => exact RT
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       | |- forall st2, _ => idtac
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC TB CXI; lia]).
  (* [comment removed for export] *)
  intros * TR. eapply KONT. exists m1. split; [exact MU1|]. split; [exact WM1|]. split; [rewrite <- E1; exact TR|].
  intros j Hj Hjc. unfold refill_tail_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP in TR. cbv zeta in TR.
  (nd_pre TR 25%nat; intros _ mu' mfa' ncnt sj' stm' stn' _ MUB _ _ NC0 _ _ NEWB NEWM _ NLE _ _ _ _ MUT WMT _; nd_post).
  eapply cells_frame; [exact (RECS1 j Hj Hjc) | exact MUT | exact WMT |]. cbn [disjoint_from cells_size csize Nat.add].
  rewrite RIE, RBE, FAE. unfold acache_addr.
  assert (B1 : shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st1 c)) + shlen (mu' - c_mapped_user (get_cls st1 c)) <= 17594333495296
             /\ shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st1 c)) + shlen (mfa' - c_mapped_free_array (get_cls st1 c)) <= 17594333495296
             /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st1 c))
             /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st1 c)))   (* [comment removed for export] *)
    by (rewrite !shad_div, !shlen_div; unfold ASHOFF; clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM; Z.div_mod_to_equations; lia).
  (nd_pre B1 4%nat; intros B1 B2 B3 B4; nd_post).
  ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 MU MUB NF NC0 MFA NEWB NEWM NLE MCR Hj Hjc B1 B2 B3 B4 Y TIC TB. lia.
Qed.
End Zd2.
#[using="Type"] Lemma refill_tailK : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a5x a6x a7x s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6 (a3x : word)
    (F : bvmap 5 word) fc (m m1 : amem) (L : alayout) (st st1 : astate) (c lo cntc : Z) (cnt : Z -> Z) (sj fl chunks0 : list word) (stm stn : word) (fj fr0 : list byte),
  let r := get_cls st c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  st1 = init_cache st ->
  ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK -> tp = Z_to_bv 64 ATP ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  u32arr asegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  (* [comment removed for export] *)
  munch ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
  stk asegs m1 lo (bv_unsigned sp + -32) ->
  rw_cells asegs m1 (bv_unsigned sp + -32) [CB 8 fr0; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m1 (acache_addr L c) [C4 (Z_to_bv 64 cntc); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)] ->
  (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m1 j (cnt j) (max_cached j) (size_of_class j)) ->
  evtF asegs RNG (fun ms' => implS asegs RNG (aembed ATOP (gfa_tree st1 c n k (KKref k c n))) (epostF Q) ms')
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 (max_cached c)) (Z_to_bv 64 AINSTANCE) a3x (Z_to_bv 64 c) a5x a6x a7x
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6)
        F (Z_to_bv 64 0x38af8) fc None m1 (seg_rom asegs)).
Proof. exact refill_tailK__body. Qed.

Definition refill_spec__stmt : Prop := forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c lo : Z) (cnt : Z -> Z) (sj fl chunks0 : list word) (stm stn : word) (fj : list byte),
  let r := get_cls st c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 (acache_addr L c) -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  u32arr asegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  (* [comment removed for export] *)
  (forall j, 1 <= j <= 31 -> arec_hdr L m j (cnt j) (max_count st j) (if a_cinit st then size_of_class j else 0)) ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (cache_refill_tree st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 refill_entry) fc None m (seg_rom asegs)).
Section Zd3.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 1).
Variable k : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 37).
Variable L : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 38).
Variable st : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 39).
Variable c : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 41).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 42).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 43).
Variable fl : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 44).
Variable chunks0 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 45).
Variable stm : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 46).
Variable stn : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 47).
Variable fj : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 48).
#[using="Type"] Lemma refill_spec__body : ltac:(let T := type of (fun (h : refill_spec__stmt) => h RNG R k Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c lo cnt sj fl chunks0 stm stn fj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (k, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (L, (st, (c, (lo, (cnt, (sj, (fl, (chunks0, (stm, (stn, fj))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ CH LCH AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RTLS RSTK RCTX RT RRI RFA RECS CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  pose proof T0 as TB. unfold sclr, KLS in TB.   (* [comment removed for export] *)
  rewrite cache_refill_tree_gfa. cbv zeta.
  change (fun st2 : astate => k (put_cls c (cls_set_count (max_count (init_cache st) c / 2 - 1)
     (cls_set_num_freed (c_num_freed (get_cls st2 c) - max_count (init_cache st) c / 2) (get_cls st2 c))) st2) true)
    with (KKref k c (max_count (init_cache st) c / 2)).
  replace (max_count (init_cache st) c) with (max_cached c) by (unfold max_count; rewrite init_cache_cinit; reflexivity).
  (* [comment removed for export] *)
  pose proof (@refill_tailK RNG R k Q ra sp gp tp) as TK.
  unfold AIMG_HI, AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, refill_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  pose proof (RECS c ltac:(clear -HC; lia)) as REC. unfold arec_hdr in REC.
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCE].
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  pose proof (munch_refl [(bv_unsigned sp - REFILL_STACK, bv_unsigned sp)]%Z m) as MUN. pose proof (wmono_refl asegs m) as WM.
  iprefix.
  carve_frame 32%nat ST.
  refresh RSTK.
  box MTX. box REG. box EXH. box STN. box STATS. box STM. box FL. box FJ. box CH.
  step. step. step. step.                                      (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  unfold max_count in REC, RECS |- *. revert REC RECS. destruct (a_cinit st) eqn:CI; intros REC RECS.
  - (* [comment removed for export] *)
    rewrite sx32_lit by (clear -MCR; lia).
    step. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear -MCR; lia); [exfalso; clear -K0 MCR; lia|].   (* [comment removed for export] *)
    unbox MTX. unbox REG. unbox EXH. unbox STN. unbox STATS. unbox STM. unbox FL. unbox FJ. unbox CH.
    eapply TK with (st := st) (lo := lo) (cnt := cnt); try eassumption.
    all: try lazymatch goal with
         | |- _ = init_cache _ => unfold init_cache; rewrite CI; reflexivity
         | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
         | |- munch _ _ _ => eapply munch_weaken; [| exact MUN]; unfold sub_fp; cbn [outside]; clear; intros x Hx; tauto
         | |- forall j, _ => intros j Hj Hjc; pose proof (RECS j Hj) as RJ; unfold arec_hdr in RJ |- *;
               eapply cells_frame; [exact RJ | exact MUN | exact WM |]; cbn [disjoint_from cells_size csize Nat.add]; unfold acache_addr; clear -SPR CEIL LO T0 T1 Hj TIC TB; lia
         end.
    all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
              first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL LO CEIL TIC TB CXI; lia]).
  - (* [comment removed for export] *)
    rewrite sx32_lit by (clear; lia).
    step. if_lit.                                              (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    setreg 11 (Z_to_bv 64 (acache_addr L 1 + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    do 7 step.                                                 (* [comment removed for export] *)
    replace (Z_to_bv 64 32) with (Z_to_bv 64 (32 * 1) : word) by reflexivity.
    replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 (1 - 16) : word) by reflexivity.
    step.                                                      (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (initcache_loop_spec RNG 31%nat 1 L cnt); try reflexivity; try eassumption; try (clear -T0 T1 TIC TB; atop_facts; lia).
      intros j Hj. pose proof (RECS j Hj) as RJ. unfold arec_hdr in RJ |- *. cbn [negb] in RJ.
      eapply cells_frame; [exact RJ | exact MUN | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -SPR CEIL LO T0 T1 Hj TIC TB; lia. }
    cbv beta. intros ms' (a1' & a3' & a5' & t3' & t4' & t5' & m2 & -> & MUL & WML & MI2 & RECS2).
    pose proof (RECS2 c ltac:(clear -HC; lia)) as REC2. unfold arec_hdr in REC2.
    step. rewrite sx32_lit by (clear -MCR; lia).               (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    unbox MTX. unbox REG. unbox EXH. unbox STN. unbox STATS. unbox STM. unbox FL. unbox FJ. unbox CH.
    eapply TK with (st := st) (lo := lo) (cnt := cnt); try eassumption.
    all: try lazymatch goal with
         | |- _ = init_cache _ => unfold init_cache; rewrite CI; reflexivity
         | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
         | |- munch _ _ _ => eapply munch_cons_trans; [exact MUN | exact MUL]
         | |- wmono _ _ _ => eapply wmono_trans; [exact WM | exact WML]
         | |- stk _ _ _ _ => eapply stk_transport_disjoint; [exact ST | exact MUL | exact WML |]; apply ic_W_disjoint_gen; [unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia | clear; cbn; lia | clear; lia]
         | |- rw_cells _ _ (bv_unsigned _ + _) _ => eapply cells_frame; [exact FR | exact MUL | exact WML |]; cbn [cells_size csize Nat.add];
               apply ic_W_disjoint_gen; [unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia | clear; cbn; lia | clear; lia]
         | |- forall j, _ => intros j Hj Hjc; apply RECS2; exact Hj
         end.
    all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
              first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL LO CEIL TIC TB CXI; lia]).
Qed.
End Zd3.
#[using="Type"] Lemma refill_spec : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c lo : Z) (cnt : Z -> Z) (sj fl chunks0 : list word) (stm stn : word) (fj : list byte),
  let r := get_cls st c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 (acache_addr L c) -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  u32arr asegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  (* [comment removed for export] *)
  (forall j, 1 <= j <= 31 -> arec_hdr L m j (cnt j) (max_count st j) (if a_cinit st then size_of_class j else 0)) ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (cache_refill_tree st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 refill_entry) fc None m (seg_rom asegs)).
Proof. exact refill_spec__body. Qed.
End CANSEC4.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MM_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.WStr.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_aensure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apopulate.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_agetfrom.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac alia_t1 := zify_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac solve_acc_with_t1 H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true)); alia_t1
      end
  | |- acc_in ?RNG (?x, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_varZ RNG lo len x n nz H (@eq_refl Z nz)); alia_t1
      end
  end.
Local Ltac acc_hint ::= lazymatch goal with |- acc_in ?RNG _ => match goal with H : rng RNG _ _ |- _ => solve_acc_with_t1 H end end.
(* [comment removed for export] *)
Local Ltac flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.flia_rl.
Local Ltac alia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.alia_rl.
Local Ltac solve_acc1 ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.solve_acc1_rl.
Local Ltac slia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.slia_rl.
Local Ltac tlia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.tlia_rl.
Local Ltac slm_footprint_with segs m m' Heq a bs n Hn Ha Hl ::= slm_footprint_with_d0 segs m m' Heq a bs n Hn Ha Hl.   (* [comment removed for export] *)
Local Ltac lia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.pinned_lia.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. (nd_pre HP 3%nat; intros [lo' hi'] HI [H1 H2]; nd_post). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
(* [comment removed for export] *)
Local Ltac refresh H := let X := fresh in pose proof H as X; clear H; rename X into H.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition refill_entry := 0x38b40.
End CANSEC1.
Notation REFILL_STACK := 672 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma v_divuw_lit : forall x y, 0 <= x < 2^31 -> 0 < y < 2^31 -> v_divuw (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x / y).
Proof.
  intros x y Hx Hy. unfold v_divuw. rewrite !unsigned_lit by lia.
  unfold bv_wrap, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. replace (Z.of_N (32 - 1)) with 31 by reflexivity.
  change (2^31) with 2147483648 in *.
  rewrite (Z.mod_small y) by lia. replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite (Z.mod_small x) by lia. f_equal.
  assert (B : 0 <= x / y <= x) by (Z.div_mod_to_equations; nia).
  Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Definition arec_hdr (L : alayout) (m : amem) (j cnt mc cs : Z) : Prop :=
  rw_cells asegs m (acache_addr L j) [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 cs)].

End CANSEC2.
Ltac zfact := first [ split; zfact | vm_compute; first [reflexivity | discriminate | intros ?; discriminate] ].
Section CANSEC3. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma mc_le4 : forall i, 1 <= i <= 4 -> max_cached i = 16 /\ 8 <= 1024 / (32 * i).
Proof.
  intros i Hi. assert (E : i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
  repeat (destruct E as [->|E]; [zfact|]). subst; zfact.
Qed.
#[using="Type"] Lemma mc_mid : forall i, 5 <= i <= 16 -> max_cached i = 2 * (1024 / (32 * i)) /\ 1 <= 1024 / (32 * i) < 8.
Proof.
  intros i Hi. assert (E : i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16) by lia.
  repeat (destruct E as [->|E]; [zfact|]). subst; zfact.
Qed.
#[using="Type"] Lemma mc_big : forall i, 17 <= i <= 30 -> max_cached i = 2 /\ 768 <= size_of_class i <= 65536 /\ 1024 / size_of_class i <= 1.
Proof.
  intros i Hi. assert (E : i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/ i = 30) by lia.
  repeat (destruct E as [->|E]; [zfact|]). subst; zfact.
Qed.
#[using="Type"] Lemma mc_31 : max_cached 31 = 16. Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma size_formula2 : forall i, 17 <= i <= 30 ->
  Z_to_bv 64 (Z.land ((Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl i 63))) 63) mod 18446744073709551616)
                     (Z.shiftr ((Z.shiftl 512 ((Z.shiftr (i - 16) 1) mod 64)) mod 18446744073709551616) 1)
              + Z.shiftl 512 ((Z.shiftr (i - 16) 1) mod 64)) = Z_to_bv 64 (size_of_class i).
Proof.
  intros i Hi.
  assert (E : i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/ i = 30) by lia.
  repeat (destruct E as [->|E]; [apply f_equal; vm_compute; reflexivity|]). subst. apply f_equal. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint ic_W (L : alayout) (i : Z) (d : nat) : list (Z * Z) :=
  match d with O => [] | Datatypes.S d' => (acache_addr L i + 4, acache_addr L i + 16) :: ic_W L (i + 1) d' end.

#[using="Type"] Lemma munch_cons_trans : forall p W m m1 m', munch [p] m m1 -> munch W m1 m' -> munch (p :: W) m m'.
Proof.
  intros [lo hi] W m m1 m' A B. eapply munch_trans; [eapply munch_weaken; [| exact A] | eapply munch_weaken; [| exact B]];
    unfold sub_fp; intros x Hx; cbn [outside] in *; tauto.
Qed.

#[using="Type"] Lemma ic_W_disjoint_below : forall L i d A n, A + n <= acache_addr L i + 4 -> disjoint_from (ic_W L i d) A n.
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i A n H; cbn [ic_W disjoint_from]; [exact I|].
  split; [unfold acache_addr in *; lia|]. apply IH. unfold acache_addr in *; lia.
Qed.

#[using="Type"] Lemma ic_W_disjoint_gen : forall L i d A n, (A + n <= acache_addr L i + 4 \/ al_t L + 2768 <= A) -> i + Z.of_nat d <= 32 -> 1 <= i ->
  disjoint_from (ic_W L i d) A n.
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i A n H Hd Hi; cbn [ic_W disjoint_from]; [exact I|].
  split; [unfold acache_addr in *; lia|]. apply IH; unfold acache_addr in *; lia.
Qed.

#[using="Type"] Lemma ic_W_disjoint_chunks : forall L i d c, disjoint_from (ic_W L i d) (acache_addr L c + 16) 64.
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i c; cbn [ic_W disjoint_from]; [exact I|].
  split; [unfold acache_addr; lia|]. apply IH.
Qed.

(* [comment removed for export] *)
End CANSEC3.
Ltac icdj tac := cbn [disjoint_from cells_size csize Nat.add length]; split; [tac | first [apply ic_W_disjoint_chunks | apply ic_W_disjoint_gen; [tac | clear; cbn; lia | clear; lia]]].

Section CANSEC4. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma ic_W_outside : forall L i d x, (x < acache_addr L i + 4 \/ al_t L + 2768 <= x) -> i + Z.of_nat d <= 32 -> 1 <= i -> outside (ic_W L i d) x.
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i x Hx Hd Hi; cbn [ic_W outside]; [exact I|].
  split; [unfold acache_addr in *; lia|]. apply IH; unfold acache_addr in *; lia.
Qed.

#[using="Type"] Lemma initcache_loop_spec : forall RNG (d : nat) (i : Z) (L : alayout) (cnt : Z -> Z)
    ra sp gp tp s0 s1 a0 a2 a4 t3 t4 t5 t6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (32 - i) -> 1 <= i <= 31 ->
  (forall j, i <= j <= 31 -> arec_hdr L m j (cnt j) 0 0) ->
  mem_inv asegs m -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) ->
  rng RNG (al_t L) 4096 ->
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  evtF asegs RNG (fun ms' => exists a1' a3' a5' t3' t4' t5' m',
      ms' = MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 a0 a1' a2 a3' a4 a5' (Z_to_bv 64 15) (Z_to_bv 64 1024)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6) F (Z_to_bv 64 0x38c38) fc None m' (seg_rom asegs)
      /\ munch (ic_W L i d) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ (forall j, i <= j <= 31 -> arec_hdr L m' j (cnt j) (max_cached j) (size_of_class j)))
    (MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 a0 (Z_to_bv 64 (acache_addr L i + 8)) a2 (Z_to_bv 64 (32 * i)) a4
             (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15) (Z_to_bv 64 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38be4) fc None m (seg_rom asegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I RECS MI T0 T1 RT TIC; [lia|]. band_lin.   (* [comment removed for export] *)
  atop_facts.
  pose proof (RECS i ltac:(lia)) as REC. unfold arec_hdr in REC.
  assert (ACE : acache_addr L i = al_t L + 208 + i * 80) by reflexivity.
  pose proof (munch_refl [(acache_addr L i + 4, acache_addr L i + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ ?P _ =>
  assert (TAILI : forall (q : Z) (t5x : word) (mm : amem), 0 <= q <= 8 -> 2 * Z.max 1 q = max_cached i ->
    rw_cells asegs mm (acache_addr L i) [C4 (Z_to_bv 64 (cnt i)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    (forall j, i + 1 <= j <= 31 -> arec_hdr L mm j (cnt j) 0 0) -> mem_inv asegs mm -> munch [(acache_addr L i + 4, acache_addr L i + 16)]%Z m mm -> wmono asegs m mm ->
    evtF asegs RNG P
      (MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 a0 (Z_to_bv 64 (acache_addr L i + 8)) a2 (Z_to_bv 64 (32 * i)) a4
               (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15) (Z_to_bv 64 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (size_of_class i)) (Z_to_bv 64 q) t5x t6)
          F (Z_to_bv 64 0x38bc0) fc None mm (seg_rom asegs)))
  end.
  { intros q t5x mm Q QM RECi RECS' MI' MU' WM'. clear REC MI MU WM.
    zstep. zstep. zstep. zstep. zstep.                         (* [comment removed for export] *)
    setreg 29 (Z_to_bv 64 (max_cached i))
      ltac:(apply Z_to_bv_eqm; rewrite <- QM; clear -Q; destruct (Z.ltb_spec q 1); cbn [Z.b2z]; rewrite Z.shiftl_mul_pow2 by lia; rewrite Z.mod_small by lia;
            change (2^1) with 2; lia).
    snapshot [(acache_addr L i + 4, acache_addr L i + 16)]%Z MUs WMs.
    step. step.                                                (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    setreg 11 (Z_to_bv 64 (acache_addr L (i + 1) + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    setreg 13 (Z_to_bv 64 (32 * (i + 1))) ltac:(f_equal; clear; lia).
    setreg 15 (Z_to_bv 64 (i + 1 - 16)) ltac:(f_equal; clear; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) => assert (RECS2 : forall j, i + 1 <= j <= 31 -> arec_hdr L m2 j (cnt j) 0 0) end.
    { intros j Hj. unfold arec_hdr. eapply cells_frame; [exact (RECS' j Hj) | exact MUs | exact WMs |]. cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj; lia. }
    step. if_cases KX; zify_cond KX; rewrite ?unsigned_lit in KX by (clear -I; lia).   (* [comment removed for export] *)
    - assert (I31 : i = 31) by (clear -KX I; lia). assert (D0 : d = 0%nat) by (clear -KX I HD; lia). subst d.
      apply evtF_done. do 7 eexists. split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU'|]. split; [exact WM'|]. split; [assumption|].
      intros j Hj. assert (J : j = i) by (clear -Hj I31 I; lia). subst j. unfold arec_hdr.
      lazymatch goal with H : rw_cells asegs _ (acache_addr L i) _ |- _ => exact H end.
    - eapply evtF_mono.
      { eapply (IH (i + 1) L cnt); try eassumption; clear -KX I HD T0 T1 TIC; lia. }
      cbv beta. intros ms' (a1' & a3' & a5' & t3' & t4' & t5' & m' & -> & MU2 & WM2 & MI2 & RECS3).
      do 7 eexists. split; [reflexivity|].
      split; [cbn [ic_W]; eapply munch_cons_trans; [exact MU' | exact MU2]|].
      split; [eapply wmono_trans; [exact WM' | exact WM2]|]. split; [exact MI2|].
      intros j Hj. destruct (Z.eq_dec j i) as [->|NE].
      + unfold arec_hdr. eapply cells_frame; [| exact MU2 | exact WM2 |]; [lazymatch goal with H : rw_cells asegs _ (acache_addr L i) _ |- _ => exact H end|].
        cbn [cells_size csize Nat.add]. apply ic_W_disjoint_below. unfold acache_addr. clear -I; lia.
      + apply RECS3. clear -Hj NE; lia. }
  assert (RECS' : forall j, i + 1 <= j <= 31 -> arec_hdr L m j (cnt j) 0 0) by (intros j Hj; apply RECS; clear -Hj; lia).
  step. if_cases K31; zify_cond K31; rewrite ?unsigned_lit in K31 by (clear -I; lia).   (* [comment removed for export] *)
  { (* [comment removed for export] *)
    assert (I31 : i = 31) by (clear -K31 I; lia).
    step. step. step. step. if_lit.                            (* [comment removed for export] *)
    step. step. step.                                          (* [comment removed for export] *)
    replace (Z_to_bv 64 64) with (Z_to_bv 64 (size_of_class i) : word) by (rewrite I31; reflexivity).
    eapply (TAILI 8); [clear; lia | rewrite I31, mc_31; reflexivity | exact REC | exact RECS' | exact MI | exact MU | exact WM]. }
  zstep. setreg 29 (Z_to_bv 64 i) ltac:(f_equal; clear; lia).   (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. if_cases K17; zify_cond K17; rewrite ?unsigned_lit in K17 by (clear -I; lia).   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    setreg 29 (Z_to_bv 64 (1024 / (32 * i))) ltac:(symmetry; apply v_divuw_lit; clear -I; lia).
    assert (SZE : size_of_class i = 32 * i) by (unfold size_of_class; replace (i <=? 16) with true by (symmetry; apply Z.leb_le; clear -K17; lia); reflexivity).
    pose proof TAILI as TL. rewrite SZE in TL. clear TAILI.
    step. step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (clear -I; Z.div_mod_to_equations; nia).   (* [comment removed for export] *)
    + destruct (mc_mid i ltac:(clear -I K17 K8; assert (5 <= i) by (destruct (Z_lt_le_dec i 5); [exfalso; pose proof (proj2 (mc_le4 i ltac:(lia))); lia| lia]); lia)) as [MC Q8].
      eapply (TL (1024 / (32 * i))); [clear -Q8; lia | rewrite MC; clear -Q8; lia | exact REC | exact RECS' | exact MI | exact MU | exact WM].
    + step. step.                                              (* [comment removed for export] *)
      destruct (mc_le4 i ltac:(clear -I K8; assert (i <= 4) by (destruct (Z_lt_le_dec 4 i); [exfalso; pose proof (proj2 (mc_mid i ltac:(lia))); lia| lia]); lia)) as [MC Q8].
      eapply (TL 8); [clear; lia | rewrite MC; reflexivity | exact REC | exact RECS' | exact MI | exact MU | exact WM].
  - (* [comment removed for export] *)
    do 7 zstep.                                                (* [comment removed for export] *)
    setreg 28 (Z_to_bv 64 (size_of_class i)) ltac:(symmetry; apply size_formula2; clear -I K17 K31; lia).
    (nd_pre (mc_big i ltac:(clear -I K17 K31; lia)) 3%nat; intros MC SB Q1; nd_post).
    step.                                                      (* [comment removed for export] *)
    setreg 29 (Z_to_bv 64 (1024 / size_of_class i)) ltac:(symmetry; apply v_divuw_lit; clear -SB; lia).
    step. step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (clear -SB Q1; Z.div_mod_to_equations; nia).   (* [comment removed for export] *)
    2: { exfalso. clear -K8 Q1. lia. }
    eapply (TAILI (1024 / size_of_class i)); [clear -Q1 SB; Z.div_mod_to_equations; nia | rewrite MC; clear -Q1 SB; Z.div_mod_to_equations; nia | exact REC | exact RECS' | exact MI | exact MU | exact WM].
Qed.

#[using="Type"] Lemma max_cached_range : forall c, 1 <= c <= 31 -> 2 <= max_cached c <= 16 /\ max_cached c mod 2 = 0.
Proof.
  intros c Hc. unfold max_cached.
  assert (E : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16
              \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30 \/ c = 31) by lia.
  repeat (destruct E as [->|E]; [zfact|]). subst; zfact.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KKref {R} (k : astate -> bool -> AM R) (c n : Z) (st2 : astate) : AM R :=
  k (put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2) true.

(* [comment removed for export] *)
Definition refill_tail_ret (L : alayout) (RNG : footprint) (sp : word) (st1 : astate) (c lo : Z) (fl chunks0 : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st1 c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  fp_le RNG RNG' /\
  exists mu' mfa' ncnt sj' (stm' stn' : word),
  let nf2 := nf + ncnt in let au2 := au + ncnt * S in
     (   mu' = mu
      \/ (nf < n /\ mu < au + (n - nf) * S /\ mu' = mu + rup (au + (n - nf) * S - mu) K_USER_MAP
          /\ rw_cells asegs m' (RB + mu) [CB (Z.to_nat (mu' - mu)) (repeat (Z_to_bv 8 0) (Z.to_nat (mu' - mu)))]
          /\ fill_at m' (shad (RB + mu)) (shlen (mu' - mu)) 0xfa
          /\ rng RNG' (RB + mu) (mu' - mu) /\ rng RNG' (shad (RB + mu)) (shlen (mu' - mu)) /\ fp_bw RNG'))
  /\ mu <= mu' <= K_FREEARR_OFF /\ mu' mod K_USER_MAP = 0
  /\ ((n <= nf /\ ncnt = 0) \/ (nf < n /\ ncnt = (mu' - au) / S)) /\ 0 <= ncnt /\ au2 <= mu'
  /\ (   mfa' = mfa
      \/ (mfa < 4 * nf2 /\ mfa' = rup (4 * nf2) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf2 <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
  /\ n <= nf2
  /\ u32arr asegs m' FA (fl ++ fvals au S (Z.to_nat ncnt))
  /\ junk_at m' (FA + 4 * nf2) (mfa' - 4 * nf2)
  /\ get_cls st2 c = mkAClass mu' au2 nf2 mfa' (c_count r)
  /\ (st2 = st1 \/ st2 = put_cls c (get_cls st2 c) st1)
  /\ munch [(bv_unsigned sp - REFILL_STACK, bv_unsigned sp);
            (RB + mu, RB + mu'); (shad (RB + mu), shad (RB + mu) + shlen (mu' - mu));
            (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
            (al_t L + 2792, al_t L + 2800); (al_t L + 2800, al_t L + 3168);
            (RI, RI + 8); (RI + 16, RI + 56); (RI + 68, RI + 69); (RI + 72, RI + 80);
            (acache_addr L c, acache_addr L c + 4); (CHK, CHK + 4 * n)]%Z m m'
  /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' (RI + 16)
       [C8 (Z_to_bv 64 (nf2 - n)); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 au2); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu'); C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' (RI + 68) [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m' (RI + 72) [C8 stn']
  /\ u64arr asegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ rw_cells asegs m' (al_t L + 2792) [C8 stm']
  /\ rw_cells asegs m' (acache_addr L c) [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)]
  /\ u32arr asegs m' CHK (skipn (Z.to_nat (nf2 - n)) (fl ++ fvals au S (Z.to_nat ncnt)) ++ skipn (Z.to_nat n) chunks0)
  /\ azero m' (shad (RB + mu')) (shlen (K_FREEARR_OFF - mu'))
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

Definition refill_tail_spec__stmt : Prop := forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (rav sp gp tp t0 t1 t2 s0v s1v a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rax a1x a3x : word)
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st1 : astate) (c lo cntc : Z) (sj fl chunks0 : list word) (stm stn : word) (fj fr0 : list byte),
  let r := get_cls st1 c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk asegs m lo (bv_unsigned sp + -32) -> ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  rw_cells asegs m (bv_unsigned sp + -32) [CB 8 fr0; C8 s1v; C8 s0v; C8 rav] ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  u32arr asegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  rw_cells asegs m (acache_addr L c) [C4 (Z_to_bv 64 cntc); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)] ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st1 = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_tail_ret L RNG sp st1 c lo fl chunks0 m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc rav) fc None m' (seg_rom asegs))) ->
  evtF asegs RNG (fun ms' => implS asegs RNG (aembed ATOP (gfa_tree st1 c n k (KKref k c n))) (epostF Q) ms')
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1v
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 (max_cached c)) (Z_to_bv 64 AINSTANCE) a3x (Z_to_bv 64 c) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38b60) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 1).
Variable k : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 3).
Variable rav : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 10).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 11).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 12).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 13).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 14).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 15).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 16).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 17).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 18).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 19).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 20).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 21).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 22).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 23).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 24).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 25).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 26).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 27).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 28).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 29).
Variable rax : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 30).
Variable a1x : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 31).
Variable a3x : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 35).
Variable L : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 36).
Variable st1 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 37).
Variable c : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 39).
Variable cntc : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 40).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 41).
Variable fl : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 42).
Variable chunks0 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 43).
Variable stm : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 44).
Variable stn : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 45).
Variable fj : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 46).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'refill_tail_spec__stmt 47).
Let n := max_cached c / 2.
#[using="a1x n"] Lemma refill_tail_spec__body : ltac:(let T := type of (fun (h : refill_tail_spec__stmt) => h RNG R k Q rav sp gp tp t0 t1 t2 s0v s1v a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rax a1x a3x F fc m L st1 c lo cntc sj fl chunks0 stm stn fj fr0) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (k, (Q, (rav, (sp, (gp, (tp, (t0, (t1, (t2, (s0v, (s1v, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (rax, (a1x, (a3x, (F, (fc, (m, (L, (st1, (c, (lo, (cntc, (sj, (fl, (chunks0, (stm, (stn, (fj, fr0)))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP FR MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ REC CH LCH AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RTLS RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  pose proof T0 as TB. unfold sclr, KLS in TB.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR. box TCX. box SCX. box TSP.
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCE].
  chg (max_cached c / 2) n.
  assert (N : 1 <= n <= 8 /\ 2 * n = max_cached c) by (subst n; clear -MCR MCE; Z.div_mod_to_equations; lia). destruct N as [N N2].
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  pose proof (munch_refl [(bv_unsigned sp - REFILL_STACK, bv_unsigned sp)]%Z m) as MUN. pose proof (wmono_refl asegs m) as WM.
  zstep.                                                       (* [comment removed for export] *)
  setreg 9 (Z_to_bv 64 n) ltac:(subst n; f_equal; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296;
                                replace (Z.of_N (32-1)) with 31 by reflexivity; change (2^31) with 2147483648;
                                rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^1) with 2; clear -MCR; Z.div_mod_to_equations; lia).
  zstep. zstep. zstep.                                         (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (al_t L + 2768)) ltac:(f_equal; clear; lia).
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  apply evtF_done. name_sp sp (-32).
  eapply getfrom_spec with (lo := lo) (L := L);
  try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length _ = _ => first [exact LSJ | exact LFL | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; eapply rng_sub'; [exact RSTK|]; clear -LO SPR CEIL; lia
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => exact RCTX
       | |- rng _ (al_t _) _ => exact RT
       | |- @eq word _ _ => first [reflexivity | exact TP | rewrite ACE; f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; rewrite ?ACE; first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM N HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC TB CXI; lia]).
  (* [comment removed for export] *)
  intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' GR.
  unfold getfrom_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP in GR. cbv zeta in GR.
  (nd_pre GR 37%nat; intros FPLE mu' mfa' ncnt sj' stm' stn' UD MUB MUM' NCE NC0 NCS FD NEWB NEWM NEWMOD NLE AR JR GC2 ST2E MU2 WM2 MI2 ST2 MTX2 REG2 EXH2 STN2 STATS2 LSJ2 STM2 CH2 AZU2 AZF2 MC2; nd_post).
  box UD. box FD. box NCE. box ST2E. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RTLS. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RT.
  assert (SHF : shad (afreearr L c + c_mapped_free_array (get_cls st1 c)) + shlen (mfa' - c_mapped_free_array (get_cls st1 c)) <= 0x10007fff8000
                /\ shad (aregion L c + c_mapped_user (get_cls st1 c)) + shlen (mu' - c_mapped_user (get_cls st1 c)) <= 0x10007fff8000
                /\ 0x2008fff7000 <= shad (afreearr L c + c_mapped_free_array (get_cls st1 c))
                /\ 0x2008fff7000 <= shad (aregion L c + c_mapped_user (get_cls st1 c))).   (* [comment removed for export] *)
  { unfold afreearr, aregion, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296. rewrite !shad_div, !shlen_div. unfold ASHOFF.
    clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM. Z.div_mod_to_equations. lia. }
  (nd_pre SHF 4%nat; intros SHF1 SHF2 SHF3 SHF4; nd_post).
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296 /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384).
  { unfold aregion_info, afreearr, aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  (nd_pre GEO 3%nat; intros RIE RBE FAE; nd_post).
  xport FR MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE RBE FAE ACE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 N Y TIC TB SHF3 SHF4; lia).
  xport REC MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE RBE FAE ACE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 N Y TIC TB SHF3 SHF4; lia).
  clear ST MI MC MTX REG EXH STN STATS STM FL FJ CH AZU AZF.
  replace (ret_pc (Z_to_bv 64 232320)) with (Z_to_bv 64 232320 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_lit.                                                (* [comment removed for export] *)
  snapshot [(acache_addr L c, acache_addr L c + 4)]%Z MUc WMc.
  box MTX2. box REG2. box EXH2. box STN2. box CH2. box STATS2. box STM2. box AR. box MU2. clear MUN WM.
  step.                                                        (* [comment removed for export] *)
  unbox MU2.
  carry AR MUc WMc ltac:(rewrite length_app, fvals_length, LFL, FAE, ACE; ub TSP; clear -SP1 SP2 HC T0 T1 NF NC0 NEWB Y TIC TB; lia).
  carry MTX2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry REG2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry EXH2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry STN2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry CH2 MUc WMc ltac:(rewrite length_app, !length_skipn, length_app, fvals_length, LFL, LCH, ACE; clear -HC NC0 N NLE NF; lia).
  carry STATS2 MUc WMc ltac:(rewrite LSJ2, ACE; clear -HC; lia).
  carry STM2 MUc WMc ltac:(rewrite ACE; clear -HC; lia).
  lazymatch goal with |- evtF _ _ ?P _ => remember P as PP eqn:HPP end.
  refresh RSTK. do 5 step.                                            (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -32) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  subst PP. apply evtF_done. eapply KONT.
  unfold refill_tail_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP. cbv zeta. fold n.
  split; [exact FPLE|]. exists mu', mfa', ncnt, sj', stm', stn'.
  split. { with_box UD ltac:(destruct DX as [Emu|(LT1 & LT & Emu & ZN & FI & G1 & G2 & BW)];
           [ left; exact Emu
           | right; split; [exact LT1|]; split; [exact LT|]; split; [exact Emu|]; split; [| split; [| split; [exact G1| split; [exact G2| exact BW]]]];
             [ eapply cells_frame; [exact ZN | exact MUc | exact WMc |]; cbn [disjoint_from cells_size csize Nat.add]; rewrite ?Z2Nat.id by (clear -MUB; lia)
             | eapply fill_frame; [exact FI | exact MUc | exact WMc |]; intros _; cbn [disjoint_from] ];
             ub TSP; rewrite RBE, ACE in *; clear -SPR CEIL LO SP1 SP2 HC T0 T1 MU MUB SHF2 Y TIC TB SHF3 SHF4; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia ]). }
  split; [exact MUB|]. split; [exact MUM'|]. split; [unboxed NCE|]. split; [exact NC0|]. split; [exact NCS|].
  split. { with_box FD ltac:(destruct DX as [Emfa|(LT & Emfa & FI & G1 & G2 & BW)];
           [ left; exact Emfa
           | right; split; [exact LT|]; split; [exact Emfa|]; split; [| split; [exact G1| split; [exact G2| exact BW]]];
             eapply fill_frame; [exact FI | exact MUc | exact WMc |]; intros _; cbn [disjoint_from];
             ub TSP; rewrite FAE, ACE in *; clear -SPR CEIL LO SP1 SP2 HC T0 T1 MFA NF NEWB NEWM SHF1 Y TIC TB; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia ]). }
  split; [exact NEWB|]. split; [exact NEWM|]. split; [exact NEWMOD|]. split; [exact NLE|].
  split; [exact AR|].
  split. { eapply junk_frame; [exact JR | exact MUc | exact WMc |]. intros _; cbn [disjoint_from]. rewrite FAE, ACE. ub TSP; clear -SP1 SP2 HC T0 T1 NF NC0 MFA NEWB NEWM Y TIC TB; lia. }
  split; [exact GC2|]. split; [unboxed ST2E|].
  split. { eapply munch_trans; [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MUc]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
  split; [exact WM2|]. split; [assumption|]. split; [assumption|].
  split; [exact MTX2|]. split; [exact REG2|]. split; [exact EXH2|]. split; [exact STN2|]. split; [exact STATS2|]. split; [exact LSJ2|]. split; [exact STM2|].
  split; [assumption|]. split; [exact CH2|].
  split. { eapply azero_frame; [exact AZU2 | exact MUc | exact WMc |]. intros _; cbn [disjoint_from]. rewrite RBE, ACE. rewrite shad_div, shlen_div. unfold ASHOFF.
           ub TSP; clear -SP1 SP2 HC T0 T1 MU MUB Y TIC TB; Z.div_mod_to_equations; lia. }
  split. { eapply azero_frame; [exact AZF2 | exact MUc | exact WMc |]. intros _; cbn [disjoint_from]. rewrite FAE, ACE. rewrite shad_div, shlen_div. unfold ASHOFF.
           ub TSP; clear -SP1 SP2 HC T0 T1 MFA NF NEWB NEWM Y TIC TB; Z.div_mod_to_equations; lia. }
  eapply m3_cells_frame; [exact MC2 | exact MUc | exact WMc |]. ub TCX. unfold AIMG_HI, AIMG_LO.
  apply Forall_cons; [cbn [fst snd]; rewrite ACE; clear -CX0 CX1 T0 T1 TIC HC Y TB CXI; with_band CX0 ltac:(lia) | apply Forall_nil].   (* [comment removed for export] *)
Qed.
End Zd1.
#[using="Type"] Lemma refill_tail_spec : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (rav sp gp tp t0 t1 t2 s0v s1v a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rax a1x a3x : word)
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st1 : astate) (c lo cntc : Z) (sj fl chunks0 : list word) (stm stn : word) (fj fr0 : list byte),
  let r := get_cls st1 c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk asegs m lo (bv_unsigned sp + -32) -> ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  rw_cells asegs m (bv_unsigned sp + -32) [CB 8 fr0; C8 s1v; C8 s0v; C8 rav] ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  u32arr asegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  rw_cells asegs m (acache_addr L c) [C4 (Z_to_bv 64 cntc); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)] ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st1 = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_tail_ret L RNG sp st1 c lo fl chunks0 m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc rav) fc None m' (seg_rom asegs))) ->
  evtF asegs RNG (fun ms' => implS asegs RNG (aembed ATOP (gfa_tree st1 c n k (KKref k c n))) (epostF Q) ms')
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1v
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 (max_cached c)) (Z_to_bv 64 AINSTANCE) a3x (Z_to_bv 64 c) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38b60) fc None m (seg_rom asegs)).
Proof. exact refill_tail_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition refill_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c lo : Z) (fl chunks0 : list word) (cnt : Z -> Z) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  exists m1, munch ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z m m1 /\ wmono asegs m m1
  /\ refill_tail_ret L RNG sp (init_cache st) c lo fl chunks0 m1 st2 RNG' m'
  /\ (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m' j (cnt j) (max_cached j) (size_of_class j)).

#[using="Type"] Lemma init_cache_cinit : forall st, a_cinit (init_cache st) = true.
Proof. intros st. unfold init_cache. destruct (a_cinit st) eqn:E; [exact E| reflexivity]. Qed.
#[using="Type"] Lemma init_cache_cls : forall st c, get_cls (init_cache st) c = get_cls st c.
Proof. intros st c. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
#[using="Type"] Lemma init_cache_space : forall st, a_space_beg (init_cache st) = a_space_beg st.
Proof. intros st. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.

(* [comment removed for export] *)
Definition refill_tailK__stmt : Prop := forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a5x a6x a7x s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6 (a3x : word)
    (F : bvmap 5 word) fc (m m1 : amem) (L : alayout) (st st1 : astate) (c lo cntc : Z) (cnt : Z -> Z) (sj fl chunks0 : list word) (stm stn : word) (fj fr0 : list byte),
  let r := get_cls st c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  st1 = init_cache st ->
  ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK -> tp = Z_to_bv 64 ATP ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  u32arr asegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  (* [comment removed for export] *)
  munch ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
  stk asegs m1 lo (bv_unsigned sp + -32) ->
  rw_cells asegs m1 (bv_unsigned sp + -32) [CB 8 fr0; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m1 (acache_addr L c) [C4 (Z_to_bv 64 cntc); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)] ->
  (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m1 j (cnt j) (max_cached j) (size_of_class j)) ->
  evtF asegs RNG (fun ms' => implS asegs RNG (aembed ATOP (gfa_tree st1 c n k (KKref k c n))) (epostF Q) ms')
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 (max_cached c)) (Z_to_bv 64 AINSTANCE) a3x (Z_to_bv 64 c) a5x a6x a7x
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6)
        F (Z_to_bv 64 0x38b60) fc None m1 (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 1).
Variable k : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 12).
Variable a5x : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 13).
Variable a6x : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 14).
Variable a7x : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 15).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 16).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 17).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 18).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 19).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 20).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 21).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 22).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 23).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 24).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 25).
Variable t3x : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 26).
Variable t4x : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 27).
Variable t5x : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 28).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 29).
Variable a3x : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 30).
Variable F : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 31).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 32).
Variable m : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 33).
Variable m1 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 34).
Variable L : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 36).
Variable st1 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 37).
Variable c : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 39).
Variable cntc : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 40).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 41).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 42).
Variable fl : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 43).
Variable chunks0 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 44).
Variable stm : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 45).
Variable stn : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 46).
Variable fj : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 47).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'refill_tailK__stmt 48).
#[using="Type"] Lemma refill_tailK__body : ltac:(let T := type of (fun (h : refill_tailK__stmt) => h RNG R k Q ra sp gp tp t0 t1 t2 s0 s1 a5x a6x a7x s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6 a3x F fc m m1 L st st1 c lo cntc cnt sj fl chunks0 stm stn fj fr0) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (k, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a5x, (a6x, (a7x, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3x, (t4x, (t5x, (t6, (a3x, (F, (fc, (m, (m1, (L, (st, (st1, (c, (lo, (cntc, (cnt, (sj, (fl, (chunks0, (stm, (stn, (fj, fr0))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros E1 CEIL LO TP MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ CH LCH AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RTLS RSTK RCTX RT RRI RFA CXI TIC KONT MU1 WM1 MI1 ST1 FR1 REC1 RECS1. band_lin.   (* [comment removed for export] *)
  pose proof T0 as TB. unfold sclr, KLS in TB.   (* [comment removed for export] *)
  unfold AIMG_HI, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR. box TCX. box SCX. box TSP.
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCE].
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296 /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384).
  { unfold aregion_info, afreearr, aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  (nd_pre GEO 3%nat; intros RIE RBE FAE; nd_post).
  assert (WOK1 : Forall (fun iv => ((AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= ATPv + -88 \/ ATPv + -80 <= fst iv)) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv))
                  ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z).
  { ub TCX. unfold AIMG_HI, AIMG_LO. apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 T0 T1 TIC Y TB CXI; with_band CX0 ltac:(lia) |].   (* [comment removed for export] *)
    cbn [ic_W]. unfold acache_addr. repeat (apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 T0 T1 TIC Y TB CXI; with_band CX0 ltac:(lia) |]). apply Forall_nil. }   (* [comment removed for export] *)
  assert (GC1 : get_cls st1 c = get_cls st c) by (rewrite E1; apply init_cache_cls).
  assert (SB1 : a_space_beg st1 = al_space_beg L) by (rewrite E1, init_cache_space; exact SBE).
  (* [comment removed for export] *)
  eapply cells_frame in MTX; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply cells_frame in REG; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply cells_frame in EXH; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply cells_frame in STN; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply u64arr_frame in STATS; [| exact MU1 | exact WM1 | rewrite LSJ; icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia)].
  eapply cells_frame in STM; [| exact MU1 | exact WM1 | icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia)].
  eapply u32arr_frame in FL; [| exact MU1 | exact WM1 | rewrite LFL, FAE; icdj ltac:(ub TSP; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 NF MFA Y TIC TB; lia)].
  eapply cells_frame in FJ; [| exact MU1 | exact WM1 | rewrite FAE; icdj ltac:(ub TSP; unfold acache_addr; rewrite ?Z2Nat.id by (clear -NF MFA; lia); clear -SPR CEIL LO SP1 SP2 HC T0 T1 NF MFA Y TIC TB; lia)].
  eapply u32arr_frame in CH; [| exact MU1 | exact WM1 | rewrite LCH; icdj ltac:(rewrite ACE; clear -SPR CEIL LO T0 T1 HC TIC TB; lia)].
  assert (MC1 : m3_cells L m1) by (eapply m3_cells_frame; [exact MC | exact MU1 | exact WM1 | exact WOK1]).
  assert (AZU1 : azero m1 (shad (aregion L c + c_mapped_user (get_cls st c))) (shlen (3758096384 - c_mapped_user (get_cls st c)))).
  { eapply azero_frame; [exact AZU | exact MU1 | exact WM1 |]. intros _. rewrite RBE.
    assert (B : shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st c)) + shlen (3758096384 - c_mapped_user (get_cls st c)) <= 17594333495296
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st c)))   (* [comment removed for export] *)
      by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -SP1 SP2 HC MU MUX; Z.div_mod_to_equations; lia).
    icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 B TIC TB; lia). }
  assert (AZF1 : azero m1 (shad (afreearr L c + c_mapped_free_array (get_cls st c))) (shlen (536870912 - c_mapped_free_array (get_cls st c)))).
  { eapply azero_frame; [exact AZF | exact MU1 | exact WM1 |]. intros _. rewrite FAE.
    assert (B : shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st c)) + shlen (536870912 - c_mapped_free_array (get_cls st c)) <= 17594333495296
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st c)))   (* [comment removed for export] *)
      by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -SP1 SP2 HC MFA NF; Z.div_mod_to_equations; lia).
    icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 B TIC TB; lia). }
  clear MC AZU AZF.
  rewrite <- GC1 in REG, LFL, FJ, AZU1, AZF1, MU, MUX, MUM, AUM, NF, NFA, MFA, MFAM, RFA.
  eapply (refill_tail_spec RNG k Q ra sp gp tp) with (lo := lo) (L := L);
  try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => exact ST1
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => exact MI1
       | |- m3_cells _ _ => exact MC1
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR1
       | |- rw_cells _ _ (acache_addr _ _) _ => exact REC1
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length _ = _ => first [exact LSJ | exact LFL | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU1
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF1
       | |- a_space_beg _ = _ => exact SB1
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => exact RCTX
       | |- rng _ (al_t _) _ => exact RT
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       | |- forall st2, _ => idtac
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC TB CXI; lia]).
  (* [comment removed for export] *)
  intros * TR. eapply KONT. exists m1. split; [exact MU1|]. split; [exact WM1|]. split; [rewrite <- E1; exact TR|].
  intros j Hj Hjc. unfold refill_tail_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP in TR. cbv zeta in TR.
  (nd_pre TR 25%nat; intros _ mu' mfa' ncnt sj' stm' stn' _ MUB _ _ NC0 _ _ NEWB NEWM _ NLE _ _ _ _ MUT WMT _; nd_post).
  eapply cells_frame; [exact (RECS1 j Hj Hjc) | exact MUT | exact WMT |]. cbn [disjoint_from cells_size csize Nat.add].
  rewrite RIE, RBE, FAE. unfold acache_addr.
  assert (B1 : shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st1 c)) + shlen (mu' - c_mapped_user (get_cls st1 c)) <= 17594333495296
             /\ shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st1 c)) + shlen (mfa' - c_mapped_free_array (get_cls st1 c)) <= 17594333495296
             /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st1 c))
             /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st1 c)))   (* [comment removed for export] *)
    by (rewrite !shad_div, !shlen_div; unfold ASHOFF; clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM; Z.div_mod_to_equations; lia).
  (nd_pre B1 4%nat; intros B1 B2 B3 B4; nd_post).
  ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 MU MUB NF NC0 MFA NEWB NEWM NLE MCR Hj Hjc B1 B2 B3 B4 Y TIC TB. lia.
Qed.
End Zd2.
#[using="Type"] Lemma refill_tailK : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a5x a6x a7x s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6 (a3x : word)
    (F : bvmap 5 word) fc (m m1 : amem) (L : alayout) (st st1 : astate) (c lo cntc : Z) (cnt : Z -> Z) (sj fl chunks0 : list word) (stm stn : word) (fj fr0 : list byte),
  let r := get_cls st c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  st1 = init_cache st ->
  ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK -> tp = Z_to_bv 64 ATP ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  u32arr asegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  (* [comment removed for export] *)
  munch ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
  stk asegs m1 lo (bv_unsigned sp + -32) ->
  rw_cells asegs m1 (bv_unsigned sp + -32) [CB 8 fr0; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m1 (acache_addr L c) [C4 (Z_to_bv 64 cntc); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)] ->
  (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m1 j (cnt j) (max_cached j) (size_of_class j)) ->
  evtF asegs RNG (fun ms' => implS asegs RNG (aembed ATOP (gfa_tree st1 c n k (KKref k c n))) (epostF Q) ms')
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 (max_cached c)) (Z_to_bv 64 AINSTANCE) a3x (Z_to_bv 64 c) a5x a6x a7x
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6)
        F (Z_to_bv 64 0x38b60) fc None m1 (seg_rom asegs)).
Proof. exact refill_tailK__body. Qed.

Definition refill_spec__stmt : Prop := forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c lo : Z) (cnt : Z -> Z) (sj fl chunks0 : list word) (stm stn : word) (fj : list byte),
  let r := get_cls st c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 (acache_addr L c) -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  u32arr asegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  (* [comment removed for export] *)
  (forall j, 1 <= j <= 31 -> arec_hdr L m j (cnt j) (max_count st j) (if a_cinit st then size_of_class j else 0)) ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (cache_refill_tree st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 refill_entry) fc None m (seg_rom asegs)).
Section Zd3.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 1).
Variable k : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 37).
Variable L : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 38).
Variable st : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 39).
Variable c : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 41).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 42).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 43).
Variable fl : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 44).
Variable chunks0 : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 45).
Variable stm : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 46).
Variable stn : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 47).
Variable fj : ltac2:(SecDietF.SzSecF.ty 'refill_spec__stmt 48).
#[using="Type"] Lemma refill_spec__body : ltac:(let T := type of (fun (h : refill_spec__stmt) => h RNG R k Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c lo cnt sj fl chunks0 stm stn fj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (k, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (L, (st, (c, (lo, (cnt, (sj, (fl, (chunks0, (stm, (stn, fj))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ CH LCH AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RTLS RSTK RCTX RT RRI RFA RECS CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  pose proof T0 as TB. unfold sclr, KLS in TB.   (* [comment removed for export] *)
  rewrite cache_refill_tree_gfa. cbv zeta.
  change (fun st2 : astate => k (put_cls c (cls_set_count (max_count (init_cache st) c / 2 - 1)
     (cls_set_num_freed (c_num_freed (get_cls st2 c) - max_count (init_cache st) c / 2) (get_cls st2 c))) st2) true)
    with (KKref k c (max_count (init_cache st) c / 2)).
  replace (max_count (init_cache st) c) with (max_cached c) by (unfold max_count; rewrite init_cache_cinit; reflexivity).
  (* [comment removed for export] *)
  pose proof (@refill_tailK RNG R k Q ra sp gp tp) as TK.
  unfold AIMG_HI, AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, refill_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  pose proof (RECS c ltac:(clear -HC; lia)) as REC. unfold arec_hdr in REC.
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCE].
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  pose proof (munch_refl [(bv_unsigned sp - REFILL_STACK, bv_unsigned sp)]%Z m) as MUN. pose proof (wmono_refl asegs m) as WM.
  iprefix.
  carve_frame 32%nat ST.
  refresh RSTK.
  box MTX. box REG. box EXH. box STN. box STATS. box STM. box FL. box FJ. box CH.
  step. step. step. step.                                      (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  unfold max_count in REC, RECS |- *. revert REC RECS. destruct (a_cinit st) eqn:CI; intros REC RECS.
  - (* [comment removed for export] *)
    rewrite sx32_lit by (clear -MCR; lia).
    step. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear -MCR; lia); [exfalso; clear -K0 MCR; lia|].   (* [comment removed for export] *)
    unbox MTX. unbox REG. unbox EXH. unbox STN. unbox STATS. unbox STM. unbox FL. unbox FJ. unbox CH.
    eapply TK with (st := st) (lo := lo) (cnt := cnt); try eassumption.
    all: try lazymatch goal with
         | |- _ = init_cache _ => unfold init_cache; rewrite CI; reflexivity
         | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
         | |- munch _ _ _ => eapply munch_weaken; [| exact MUN]; unfold sub_fp; cbn [outside]; clear; intros x Hx; tauto
         | |- forall j, _ => intros j Hj Hjc; pose proof (RECS j Hj) as RJ; unfold arec_hdr in RJ |- *;
               eapply cells_frame; [exact RJ | exact MUN | exact WM |]; cbn [disjoint_from cells_size csize Nat.add]; unfold acache_addr; clear -SPR CEIL LO T0 T1 Hj TIC TB; lia
         end.
    all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
              first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL LO CEIL TIC TB CXI; lia]).
  - (* [comment removed for export] *)
    rewrite sx32_lit by (clear; lia).
    step. if_lit.                                              (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    setreg 11 (Z_to_bv 64 (acache_addr L 1 + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    do 7 step.                                                 (* [comment removed for export] *)
    replace (Z_to_bv 64 32) with (Z_to_bv 64 (32 * 1) : word) by reflexivity.
    replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 (1 - 16) : word) by reflexivity.
    step.                                                      (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (initcache_loop_spec RNG 31%nat 1 L cnt); try reflexivity; try eassumption; try (clear -T0 T1 TIC TB; atop_facts; lia).
      intros j Hj. pose proof (RECS j Hj) as RJ. unfold arec_hdr in RJ |- *. cbn [negb] in RJ.
      eapply cells_frame; [exact RJ | exact MUN | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -SPR CEIL LO T0 T1 Hj TIC TB; lia. }
    cbv beta. intros ms' (a1' & a3' & a5' & t3' & t4' & t5' & m2 & -> & MUL & WML & MI2 & RECS2).
    pose proof (RECS2 c ltac:(clear -HC; lia)) as REC2. unfold arec_hdr in REC2.
    step. rewrite sx32_lit by (clear -MCR; lia).               (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    unbox MTX. unbox REG. unbox EXH. unbox STN. unbox STATS. unbox STM. unbox FL. unbox FJ. unbox CH.
    eapply TK with (st := st) (lo := lo) (cnt := cnt); try eassumption.
    all: try lazymatch goal with
         | |- _ = init_cache _ => unfold init_cache; rewrite CI; reflexivity
         | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
         | |- munch _ _ _ => eapply munch_cons_trans; [exact MUN | exact MUL]
         | |- wmono _ _ _ => eapply wmono_trans; [exact WM | exact WML]
         | |- stk _ _ _ _ => eapply stk_transport_disjoint; [exact ST | exact MUL | exact WML |]; apply ic_W_disjoint_gen; [unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia | clear; cbn; lia | clear; lia]
         | |- rw_cells _ _ (bv_unsigned _ + _) _ => eapply cells_frame; [exact FR | exact MUL | exact WML |]; cbn [cells_size csize Nat.add];
               apply ic_W_disjoint_gen; [unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia | clear; cbn; lia | clear; lia]
         | |- forall j, _ => intros j Hj Hjc; apply RECS2; exact Hj
         end.
    all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
              first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL LO CEIL TIC TB CXI; lia]).
Qed.
End Zd3.
#[using="Type"] Lemma refill_spec : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c lo : Z) (cnt : Z -> Z) (sj fl chunks0 : list word) (stm stn : word) (fj : list byte),
  let r := get_cls st c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 (acache_addr L c) -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  u32arr asegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  (* [comment removed for export] *)
  (forall j, 1 <= j <= 31 -> arec_hdr L m j (cnt j) (max_count st j) (if a_cinit st then size_of_class j else 0)) ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (cache_refill_tree st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 refill_entry) fc None m (seg_rom asegs)).
Proof. exact refill_spec__body. Qed.
End CANSEC4.
End TwB.
End F_arefill.

(* [comment removed for export] *)
Module F_acdealloc.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MM_syscalls WStr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agetfrom__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_aensure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_agetfrom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_arefill OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_amaybe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_areturn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_acdrain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac ic_norm := repeat match goal with |- context [(?a + ?b)%Z] => is_Zlit a; is_Zlit b;
                          let v := eval vm_compute in (a + b)%Z in change (a + b)%Z with v end.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
(* [comment removed for export] *)
Local Ltac find_ivw_syn :=
  first [ apply Exists_cons_hd; cbn [fst snd];
          lazymatch goal with |- (?a <= ?b /\ ?c <= ?d)%Z => constr_eq a b; constr_eq c d end; split; apply Z.le_refl
        | apply Exists_cons_tl; find_ivw_syn ].
Local Ltac find_ivw_orig tac :=
  first [ apply Exists_cons_hd; cbn [fst snd]; split; apply Z.le_refl
        | apply Exists_cons_hd; cbn [fst snd]; solve [tac]
        | apply Exists_cons_tl; find_ivw_orig tac ].
Local Ltac find_ivw tac ::= first [ find_ivw_syn | find_ivw_orig tac ].

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition cdealloc_entry : Z := 0x36344.
End CANSEC1.
Notation CDEALLOC_STACK := 688 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma initcache_loop2_spec : forall RNG (d : nat) (i : Z) (L : alayout) (cnt : Z -> Z)
    ra sp gp tp s0 s1 a0 a1 a2 a3 t4 t5 t6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (32 - i) -> 1 <= i <= 31 ->
  (forall j, i <= j <= 31 -> arec_hdr L m j (cnt j) 0 0) ->
  mem_inv asegs m -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) ->
  rng RNG (al_t L) 4096 ->
  evtF asegs RNG (fun ms' => exists a4' a5' a6' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp (Z_to_bv 64 1024) (Z_to_bv 64 16) (Z_to_bv 64 17) s0 s1 a0 a1 a2 a3 a4' a5' a6' (Z_to_bv 64 15)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 512) t4' t5' t6') F (Z_to_bv 64 0x364c8) fc None m' (seg_rom asegs)
      /\ munch (ic_W L i d) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ (forall j, i <= j <= 31 -> arec_hdr L m' j (cnt j) (max_cached j) (size_of_class j)))
    (MS (mkR ra sp gp tp (Z_to_bv 64 1024) (Z_to_bv 64 16) (Z_to_bv 64 17) s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (acache_addr L i + 8)) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15)
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 512) t4 t5 t6)
        F (Z_to_bv 64 0x36474) fc None m (seg_rom asegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I RECS MI T0 T1 RT; [lia|]. band_lin.   (* [comment removed for export] *)
  atop_facts.
  pose proof (RECS i ltac:(lia)) as REC. unfold arec_hdr in REC.
  assert (ACE : acache_addr L i = al_t L + 208 + i * 80) by reflexivity.
  pose proof (munch_refl [(acache_addr L i + 4, acache_addr L i + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ ?P _ =>
  assert (TAILI : forall (q : Z) (t6x : word) (mm : amem), 0 <= q <= 8 -> 2 * Z.max 1 q = max_cached i ->
    rw_cells asegs mm (acache_addr L i) [C4 (Z_to_bv 64 (cnt i)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    (forall j, i + 1 <= j <= 31 -> arec_hdr L mm j (cnt j) 0 0) -> mem_inv asegs mm -> munch [(acache_addr L i + 4, acache_addr L i + 16)]%Z m mm -> wmono asegs m mm ->
    evtF asegs RNG P
      (MS (mkR ra sp gp tp (Z_to_bv 64 1024) (Z_to_bv 64 16) (Z_to_bv 64 17) s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (acache_addr L i + 8)) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 512) (Z_to_bv 64 (size_of_class i)) (Z_to_bv 64 q) t6x)
          F (Z_to_bv 64 0x36450) fc None mm (seg_rom asegs)))
  end.
  { intros q t6x mm Q QM RECi RECS' MI' MU' WM'. clear REC MI MU WM.
    zstep. zstep. zstep. zstep. zstep.                         (* [comment removed for export] *)
    setreg 30 (Z_to_bv 64 (max_cached i))
      ltac:(apply Z_to_bv_eqm; rewrite <- QM; clear -Q; destruct (Z.ltb_spec q 1); cbn [Z.b2z]; rewrite Z.shiftl_mul_pow2 by lia; rewrite Z.mod_small by lia;
            change (2^1) with 2; lia).
    snapshot [(acache_addr L i + 4, acache_addr L i + 16)]%Z MUs WMs.
    step. step.                                                (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    setreg 14 (Z_to_bv 64 (acache_addr L (i + 1) + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    setreg 15 (Z_to_bv 64 (32 * (i + 1))) ltac:(f_equal; clear; lia).
    setreg 16 (Z_to_bv 64 (i + 1 - 16)) ltac:(f_equal; clear; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) => assert (RECS2 : forall j, i + 1 <= j <= 31 -> arec_hdr L m2 j (cnt j) 0 0) end.
    { intros j Hj. unfold arec_hdr. eapply cells_frame; [exact (RECS' j Hj) | exact MUs | exact WMs |]. cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj; lia. }
    step. if_cases KX; zify_cond KX; rewrite ?unsigned_lit in KX by (clear -I; lia).   (* [comment removed for export] *)
    - assert (I31 : i = 31) by (clear -KX I; lia). assert (D0 : d = 0%nat) by (clear -KX I HD; lia). subst d.
      apply evtF_done. do 7 eexists. split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU'|]. split; [exact WM'|]. split; [assumption|].
      intros j Hj. assert (J : j = i) by (clear -Hj I31 I; lia). subst j. unfold arec_hdr.
      lazymatch goal with H : rw_cells asegs _ (acache_addr L i) _ |- _ => exact H end.
    - eapply evtF_mono.
      { eapply (IH (i + 1) L cnt); try eassumption; clear -KX I HD T0 T1; lia. }
      cbv beta. intros ms' (a4' & a5' & a6' & t4' & t5' & t6' & m' & -> & MU2 & WM2 & MI2 & RECS3).
      do 7 eexists. split; [reflexivity|].
      split; [cbn [ic_W]; eapply munch_cons_trans; [exact MU' | exact MU2]|].
      split; [eapply wmono_trans; [exact WM' | exact WM2]|]. split; [exact MI2|].
      intros j Hj. destruct (Z.eq_dec j i) as [->|NE].
      + unfold arec_hdr. eapply cells_frame; [| exact MU2 | exact WM2 |]; [lazymatch goal with H : rw_cells asegs _ (acache_addr L i) _ |- _ => exact H end|].
        cbn [cells_size csize Nat.add]. apply ic_W_disjoint_below. unfold acache_addr. clear -I; lia.
      + apply RECS3. clear -Hj NE; lia. }
  assert (RECS' : forall j, i + 1 <= j <= 31 -> arec_hdr L m j (cnt j) 0 0) by (intros j Hj; apply RECS; clear -Hj; lia).
  step. if_cases K31; zify_cond K31; rewrite ?unsigned_lit in K31 by (clear -I; lia).   (* [comment removed for export] *)
  { (* [comment removed for export] *)
    assert (I31 : i = 31) by (clear -K31 I; lia).
    step. step. step. step. if_lit.                            (* [comment removed for export] *)
    step. step. step.                                          (* [comment removed for export] *)
    replace (Z_to_bv 64 64) with (Z_to_bv 64 (size_of_class i) : word) by (rewrite I31; reflexivity).
    eapply (TAILI 8); [clear; lia | rewrite I31, mc_31; reflexivity | exact REC | exact RECS' | exact MI | exact MU | exact WM]. }
  zstep. setreg 30 (Z_to_bv 64 i) ltac:(f_equal; clear; lia).   (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. if_cases K17; zify_cond K17; rewrite ?unsigned_lit in K17 by (clear -I; lia).   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    setreg 30 (Z_to_bv 64 (1024 / (32 * i))) ltac:(symmetry; apply v_divuw_lit; clear -I; lia).
    assert (SZE : size_of_class i = 32 * i) by (unfold size_of_class; replace (i <=? 16) with true by (symmetry; apply Z.leb_le; clear -K17; lia); reflexivity).
    pose proof TAILI as TL. rewrite SZE in TL. clear TAILI.
    step. step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (clear -I; Z.div_mod_to_equations; nia).   (* [comment removed for export] *)
    + destruct (mc_mid i ltac:(clear -I K17 K8; assert (5 <= i) by (destruct (Z_lt_le_dec i 5); [exfalso; pose proof (proj2 (mc_le4 i ltac:(lia))); lia| lia]); lia)) as [MC Q8].
      eapply (TL (1024 / (32 * i))); [clear -Q8; lia | rewrite MC; clear -Q8; lia | exact REC | exact RECS' | exact MI | exact MU | exact WM].
    + step. step.                                              (* [comment removed for export] *)
      destruct (mc_le4 i ltac:(clear -I K8; assert (i <= 4) by (destruct (Z_lt_le_dec 4 i); [exfalso; pose proof (proj2 (mc_mid i ltac:(lia))); lia| lia]); lia)) as [MC Q8].
      eapply (TL 8); [clear; lia | rewrite MC; reflexivity | exact REC | exact RECS' | exact MI | exact MU | exact WM].
  - (* [comment removed for export] *)
    do 7 zstep.                                                (* [comment removed for export] *)
    setreg 29 (Z_to_bv 64 (size_of_class i)) ltac:(symmetry; apply size_formula2; clear -I K17 K31; lia).
    (nd_pre (mc_big i ltac:(clear -I K17 K31; lia)) 3%nat; intros MC SB Q1; nd_post).
    step.                                                      (* [comment removed for export] *)
    setreg 30 (Z_to_bv 64 (1024 / size_of_class i)) ltac:(symmetry; apply v_divuw_lit; clear -SB; lia).
    step. step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (clear -SB Q1; Z.div_mod_to_equations; nia).   (* [comment removed for export] *)
    2: { exfalso. clear -K8 Q1. lia. }
    eapply (TAILI (1024 / size_of_class i)); [clear -Q1 SB; Z.div_mod_to_equations; nia | rewrite MC; clear -Q1 SB; Z.div_mod_to_equations; nia | exact REC | exact RECS' | exact MI | exact MU | exact WM].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cdmain_post (rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : alayout) (c k0 mc csz P lo : Z) (chunks : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (sta' : word) m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (acache_addr L c, acache_addr L c + 4); (acache_addr L c + 16, acache_addr L c + 80);
              (al_t L + 2784, al_t L + 2792)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (acache_addr L c) [C4 (Z_to_bv 64 (k0 + 1)); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)]
    /\ u32arr asegs m' (acache_addr L c + 16) (upd chunks (Z.to_nat k0) (Z_to_bv 64 ((P - aregion L c) / 16)))
    /\ rw_cells asegs m' (al_t L + 2784) [C8 sta'].

Definition cd_main_spec__stmt : Prop := forall RNG (rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 : word)
    (rax t0 t1 t2 a5 a6 a7 s1x s2x s3x s4x t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (c k0 mc csz P lo : Z) (chunks : list word) (sta : word),
  stk asegs m lo (bv_unsigned sp + -48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 (al_space_beg L))] ->
  rw_cells asegs m (acache_addr L c) [C4 (Z_to_bv 64 k0); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)] ->
  u32arr asegs m (acache_addr L c + 16) chunks -> length chunks = 16%nat ->
  rw_cells asegs m (al_t L + 2784) [C8 sta] ->
  1 <= c < K_NUM_CLASSES -> 0 <= k0 < 16 -> 0 <= mc < 2^31 -> 0 <= csz < 2^63 ->
  aregion L c <= P -> P < aregion L c + K_REGION ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP ->
  sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_t L) 4096 ->
  evtF asegs RNG (cdmain_post rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc L c k0 mc csz P lo chunks m)
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1x
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 c) (Z_to_bv 64 P) (Z_to_bv 64 k0) a5 a6 a7
             s2x s3x s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x36388) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 0).
Variable rav : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 4).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 5).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 6).
Variable s2v : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 7).
Variable s3v : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 8).
Variable s4v : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 9).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 10).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 11).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 12).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 13).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 14).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 15).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 16).
Variable rax : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 17).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 18).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 19).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 20).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 21).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 22).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 23).
Variable s1x : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 24).
Variable s2x : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 25).
Variable s3x : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 26).
Variable s4x : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 34).
Variable L : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 35).
Variable c : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 36).
Variable k0 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 37).
Variable mc : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 38).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 39).
Variable P : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 41).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 42).
Variable sta : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 43).
#[using="Type"] Lemma cd_main_spec__body : ltac:(let T := type of (fun (h : cd_main_spec__stmt) => h RNG rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 rax t0 t1 t2 a5 a6 a7 s1x s2x s3x s4x t3 t4 t5 t6 F fc m L c k0 mc csz P lo chunks sta) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (rav, (sp, (gp, (tp, (s0v, (s1v, (s2v, (s3v, (s4v, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (rax, (t0, (t1, (t2, (a5, (a6, (a7, (s1x, (s2x, (s3x, (s4x, (t3, (t4, (t5, (t6, (F, (fc, (m, (L, (c, (k0, (mc, (csz, (P, (lo, (chunks, sta)))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI FR ISB CR CH LCH STA HC K0 MC CSZ P0 P1 SP1 SP2 T0 T1 TAL TI RIMG RTLS RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AINSTANCE, K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
  word_range sp SPR.
  assert (CAE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (acache_addr L c, acache_addr L c + 4); (acache_addr L c + 16, acache_addr L c + 80);
                          (al_t L + 2784, al_t L + 2792)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  step.                                                        (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  setreg 12 (Z_to_bv 64 (acache_addr L c + 4 * k0)) ltac:(rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by (clear; lia); rewrite Z.mod_small by (clear -K0; lia); f_equal;
      change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by (clear; lia); clear; lia).
  setreg 13 (Z_to_bv 64 ((P - aregion L c) / 16))
    ltac:(rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by (clear; lia); change (2^4) with 16; change (2^32) with 4294967296; f_equal; f_equal;
          rewrite RBE; rewrite (Z.mod_small (c * 4294967296)) by (clear -HC; lia);
          rewrite (Z.mod_small (P - c * 4294967296)) by (clear -HC P0 P1 SP1 SP2 RBE; lia);
          rewrite Z.mod_small by (clear -HC P0 P1 SP1 SP2 RBE; lia); clear; lia).
  box CH. box STA. box ISB.
  snapshot [(acache_addr L c, acache_addr L c + 4)]%Z MUc WMc.
  step.                                                        (* [comment removed for export] *)
  carry CH MUc WMc ltac:(rewrite LCH; clear; lia).
  carry STA MUc WMc ltac:(rewrite CAE; clear -HC; lia).
  carry ISB MUc WMc ltac:(rewrite CAE; clear -HC TI; lia).   (* [comment removed for export] *)
  clear MUc WMc.
  pose proof (u32arr_store_ok asegs _ (acache_addr L c + 16) _ k0 (wa (acache_addr L c + 16 + 4 * k0)) CH ltac:(rewrite LCH; clear -K0; lia) eq_refl) as SOK.
  box CR. box STA. box ISB. box FR.
  snapshot [(acache_addr L c + 16, acache_addr L c + 80)]%Z MUa WMa.
  step.                                                        (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a (le4 ?v)) _) =>
    pose proof (u32arr_write asegs mm (acache_addr L c + 16) _ k0 v CH ltac:(rewrite LCH; clear -K0; lia)) as CH2
  end.
  clear CH. store_done. try clear SOK.
  carry CR MUa WMa ltac:(clear; lia). carry STA MUa WMa ltac:(rewrite CAE; clear -HC; lia). carry ISB MUa WMa ltac:(rewrite CAE; clear -HC TI; lia).
  carry FR MUa WMa ltac:(rewrite CAE; clear -HC T1 SPR CEIL LO; lia). clear MUa WMa.
  zstep.                                                       (* [comment removed for export] *)
  assert (AMO : amo_aligned AD (Z_to_bv 64 (al_t L + 2784)) = true) by (pose proof atop_range as AR; apply amo_alignedD_intro; [clear -TI T1 AR; lia| clear -TAL; Z.div_mod_to_equations; lia]).   (* [comment removed for export] *)
  box CH2. box CR. box ISB.
  snapshot [(al_t L + 2784, al_t L + 2792)]%Z MUb WMb.
  amo_stepA AMO.                                               (* [comment removed for export] *)
  carry CH2 MUb WMb ltac:(rewrite ?upd_length, LCH, CAE; clear -HC; lia). carry CR MUb WMb ltac:(rewrite CAE; clear -HC; lia). carry ISB MUb WMb ltac:(clear -TI; lia).
  clear MUb WMb.
  do 8 step.                                                   (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  unfold cdmain_post. finish.
  all: try eassumption.
Qed.
End Zd1.
#[using="Type"] Lemma cd_main_spec : ltac:(let t := eval cbv delta [cd_main_spec__stmt] in cd_main_spec__stmt in exact t).
Proof. exact cd_main_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma get_cls_init_cache : forall st c, get_cls (init_cache st) c = get_cls st c.
Proof. intros st c. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
#[using="Type"] Lemma a_cinit_init_cache : forall st, a_cinit (init_cache st) = true.
Proof. intros st. unfold init_cache. destruct (a_cinit st) eqn:E; [exact E| reflexivity]. Qed.
#[using="Type"] Lemma max_count_init_cache : forall st c, max_count (init_cache st) c = max_cached c.
Proof. intros st c. unfold max_count. rewrite a_cinit_init_cache. reflexivity. Qed.
#[using="Type"] Lemma put_cls_put_cls : forall c x y st, put_cls c x (put_cls c y st) = put_cls c x st.
Proof. intros c x y st. unfold put_cls, set_cls. cbn. f_equal. rewrite insert_insert. destruct (decide (c = c)) as [|NE]; [reflexivity| exfalso; apply NE; reflexivity]. Qed.
#[using="Type"] Lemma get_cls_put_cls_same : forall c r st, get_cls (put_cls c r st) c = r.
Proof. intros. apply get_cls_put_cls_eq. Qed.

(* [comment removed for export] *)
Definition cd_W (L : alayout) (sp : Z) (c nf mfa mfa' : Z) : list (Z * Z) :=
  let CA := acache_addr L c in let FA := afreearr L c in let RI := aregion_info L c in
  ([(sp - 688, sp)] ++ ic_W L 1 31 ++
   [(CA, CA + 4); (CA + 16, CA + 80); (al_t L + 2784, al_t L + 2792); (al_t L + 2800, al_t L + 3168);
    (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
    (RI, RI + 8); (RI + 16, RI + 32); (RI + 72, RI + 128)])%Z.

(* [comment removed for export] *)
Definition cdealloc_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c P lo : Z) (chunks : list word) (m : amem)
    (stX : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st c in let CA := acache_addr L c in let FA := afreearr L c in let RI := aregion_info L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let mc := max_cached c in let half := mc / 2 in let cnt := c_count r in
  fp_le RNG RNG' /\
  exists (drained : bool) mfa' sj' (sta' : word),
  let nf' := if drained then nf + half else nf in
  let cnt' := if drained then cnt - half + 1 else cnt + 1 in
     (* [comment removed for export] *)
     drained = (a_cinit st && (cnt =? mc))%bool
  /\ get_cls stX c = mkAClass (c_mapped_user r) (c_allocated_user r) nf' mfa' cnt'
  /\ stX = put_cls c (get_cls stX c) (init_cache st)
  /\ (   mfa' = mfa
      \/ (drained = true /\ mfa < 4 * (nf + half) /\ mfa' = rup (4 * (nf + half)) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf' <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
     (* [comment removed for export] *)
  /\ munch (cd_W L (bv_unsigned sp) c nf mfa mfa') m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
     (* [comment removed for export] *)
  /\ (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m' j (c_count (get_cls st j)) (max_cached j) (size_of_class j))
  /\ arec_hdr L m' c cnt' (max_cached c) (size_of_class c)
  /\ u32arr asegs m' (CA + 16) (upd chunks (Z.to_nat (cnt' - 1)) (Z_to_bv 64 ((P - aregion L c) / 16)))
  /\ rw_cells asegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' (RI + 16)
       [C8 (Z_to_bv 64 nf'); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)]
  /\ junk_at m' (RI + 72) 56
  /\ u64arr asegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ rw_cells asegs m' (al_t L + 2784) [C8 sta']
  /\ (drained = true -> u32arr asegs m' (FA + 4 * nf) (firstn (Z.to_nat half) (skipn (Z.to_nat (cnt - half)) chunks)))
  /\ junk_at m' (FA + 4 * nf') (mfa' - 4 * nf')
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

Definition cdealloc_spec__stmt : Prop := forall RNG {R} (k : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c P lo : Z) (sj chunks : list word) (sta : word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in let CA := acache_addr L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let cnt := c_count r in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CDEALLOC_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 c -> a3 = Z_to_bv 64 P ->
  m3_cells L m ->
  (forall j, 1 <= j <= 31 -> arec_hdr L m j (c_count (get_cls st j)) (max_count st j) (if a_cinit st then size_of_class j else 0)) ->
  u32arr asegs m (CA + 16) chunks -> length chunks = 16%nat -> Forall (fun w : word => bv_unsigned w < 2^31) (firstn (Z.to_nat cnt) chunks) ->
  rw_cells asegs m (al_t L + 2784) [C8 sta] ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  junk_at m (RI + 72) 56 ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  junk_at m (FA + 4 * nf) (mfa - 4 * nf) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  (forall j, 1 <= j <= 31 -> 0 <= c_count (get_cls st j) <= max_count st j) ->
  0 <= nf -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 4 * (nf + max_cached c / 2) <= K_FREEARR_MAX ->
  aregion L c <= P -> P < aregion L c + K_REGION ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall stX RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      cdealloc_ret L RNG sp st c P lo chunks m stX RNG' m' ->
      implS asegs RNG' (aembed ATOP (k stX)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (cache_dealloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 cdealloc_entry) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 1).
Variable k : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 37).
Variable L : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 38).
Variable st : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 39).
Variable c : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 40).
Variable P : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 41).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 42).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 43).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 44).
Variable sta : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 45).
Let nf := c_num_freed (get_cls st c).
Let mfa := c_mapped_free_array (get_cls st c).
#[using="nf mfa"] Lemma cdealloc_spec__body : ltac:(let T := type of (fun (h : cdealloc_spec__stmt) => h RNG R k Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c P lo sj chunks sta) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (k, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (L, (st, (c, (P, (lo, (sj, (chunks, sta)))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC RECS CH LCH CH31 STA MTX REG J72 STATS LSJ FJ AZF SBE HC CNTS NF MFA MFAM NFN P0 P1
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RTLS RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  destruct (sclr_int _ _ T0 ltac:(clear -TIC; lia) ltac:(pose proof atop_range as AR; clear -T1 AR; lia)) as (kT0 & T0k).   (* [comment removed for export] *)
  pose proof atop_range as AR.   (* [comment removed for export] *)
  unfold AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, cdealloc_entry in *.
  change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
  word_range sp SPR.
  chg (c_num_freed (get_cls st c)) nf. chg (c_mapped_free_array (get_cls st c)) mfa.
  assert (CAE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCEV].
  pose proof (CNTS c ltac:(clear -HC; lia)) as CNTc. fold nf in CNTc.
  pose proof (RECS c ltac:(clear -HC; lia)) as CR. unfold arec_hdr in CR.
  box TCX. box SCX. box TSP.
  pose proof (munch_refl [(bv_unsigned sp - 688, bv_unsigned sp)]%Z m) as MUN. pose proof (wmono_refl asegs m) as WM.
  iprefix.
  carve_frame 48%nat ST.
  box MTX. box REG. box STA. box CH. box STATS. clear CR.
  do 7 step.                                                   (* [comment removed for export] *)
  carry STATS MUN WM ltac:(rewrite LSJ; clear -SPR CEIL LO T0 T1; lia).
  carry MTX MUN WM ltac:(rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC; lia).
  carry REG MUN WM ltac:(rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC; lia).
  carry STA MUN WM ltac:(clear -SPR CEIL LO T0 T1; lia).
  carry CH MUN WM ltac:(rewrite LCH, CAE; clear -SPR CEIL LO T0 T1 HC; lia).
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RECS0 : forall j, 1 <= j <= 31 -> arec_hdr L mm j (c_count (get_cls st j)) (max_count st j) (if a_cinit st then size_of_class j else 0));
    [ intros j Hj; unfold arec_hdr; eapply cells_frame; [exact (RECS j Hj) | exact MUN | exact WM |];
      cbn [disjoint_from cells_size csize Nat.add]; unfold acache_addr; clear -Hj SPR CEIL LO T0 T1; lia |]
  end.
  clear RECS.
  eapply junk_frame in J72; [| exact MUN | exact WM | intros _; cbn [disjoint_from]; rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC; lia].
  eapply junk_frame in FJ; [| exact MUN | exact WM | intros _; cbn [disjoint_from]; rewrite FAE; clear -SPR CEIL LO SP1 SP2 HC NF MFA; lia].
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AZF0 : azero mm (shad (afreearr L c + mfa)) (shlen (536870912 - mfa)));
    [ eapply azero_frame; [exact AZF | exact MUN | exact WM |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC SPR CEIL LO MFA NF; Z.div_mod_to_equations; lia |];
    assert (MC0 : m3_cells L mm);
    [ eapply m3_cells_frame; [exact MC | exact MUN | exact WM |]; unfold AIMG_HI, AIMG_LO;
      apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 CXI TIC SPR CEIL LO T1; lia |]; apply Forall_nil |]
  end.
  clear AZF MC.
  pose proof (RECS0 c ltac:(clear -HC; lia)) as CR. unfold arec_hdr in CR.
  step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (clear -HC; lia); clear -KZ HC; lia|].   (* [comment removed for export] *)
  step. step. if_cases K32; zify_cond K32; [exfalso; rewrite ?unsigned_lit in K32 by (clear -HC; lia); clear -K32 HC; lia|].   (* [comment removed for export] *)
  step. zstep. zstep.                                          (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 (acache_addr L c)) ltac:(rewrite CAE; f_equal; clear; lia).
  step.                                                        (* [comment removed for export] *)
  unfold max_count in *.
  destruct (a_cinit st) eqn:CI.
  - (* [comment removed for export] *)
    rewrite (sx32_lit (max_cached c)) by (clear -MCR; lia).
    step. if_cases KM; zify_cond KM; [exfalso; rewrite ?unsigned_lit in KM by (clear -MCR; lia); clear -KM MCR; lia|].   (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    rewrite (sx32_lit (c_count (get_cls st c))) by (clear -CNTc MCR; lia).
    step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by (clear -CNTc MCR; lia).   (* [comment removed for export] *)
    + (* [comment removed for export] *)
      do 7 step.                                               (* [comment removed for export] *)
      step.                                                    (* [comment removed for export] *)
      apply evtF_done.
      unfold cache_dealloc. cbv zeta. unfold init_cache, max_count. rewrite !CI. fold nf.
      replace (c_count (get_cls st c) =? max_cached c) with true by (symmetry; apply Z.eqb_eq; exact KD).
      name_sp sp (-48).
      eapply cdrain_spec with (lo := lo) (L := L) (sj := sj) (chunks := chunks) (cnt := c_count (get_cls st c)) (mc := max_cached c) (csz := size_of_class c);
      try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- iclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
       | |- m3_cells _ _ => exact MC0
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (acache_addr _ _) _ => exact CR
       | |- junk_at _ (aregion_info _ _ + 72) _ => exact J72
       | |- junk_at _ _ _ => exact FJ
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ _ _ => exact CH
       | |- length _ = _ => first [exact LSJ | exact LCH]
       | |- Forall _ _ => exact CH31
       | |- azero _ _ _ => exact AZF0
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
      all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
              clear KONT; fold nf mfa; first [assumption | clear -NF MFA MFAM NFN HC SP1 SP2 SP3 CX0 CX1 T0 T1 CNTc KD MCR; lia]).
      (* [comment removed for export] *)
      intros st2 RNG' m2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' DR.
      unfold cdrain_ret in DR. cbv zeta in DR. (nd_pre DR 7%nat; intros md MU01 WM01 RR CR2 CH2 ST2; nd_post).
      pose proof RR as RR0. unfold rta_ret, K_FREEARR_MAX, K_FREEARR_MAP in RR0. cbv zeta in RR0. fold nf mfa in RR0.
      (nd_pre RR0 22%nat; intros FPLE new sj' UD NEWB NEWGE NEWM GC2 ST2E MU2 WM2 MI2 _ MTX2 REG2 J722 STATS2 LSJ2 SRC2 JR2 AZF2 MC2; nd_post).
      rewrite Hsp in *. unname_sp.
      rewrite ?unsigned_lit in MU2 by (clear -SPR CEIL LO; lia).
      rewrite ?unsigned_lit in ST2 by (clear -SPR CEIL LO; lia).
      apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RTLS. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RT.
      assert (SHF : shad (afreearr L c + mfa) + shlen (new - mfa) <= 0x10007fff8000).
      { rewrite !shad_div, !shlen_div, FAE. unfold ASHOFF. clear -SP1 SP2 HC MFA NF NEWB NEWGE MCR. Z.div_mod_to_equations. lia. }
      assert (SHB2 : 2148238848 <= shad (afreearr L c + mfa)) by (rewrite shad_div, FAE; unfold ASHOFF; clear -SP1 HC MFA NF; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      xport FR MU01 WM01 ltac:(rewrite CAE; clear -SPR CEIL LO T1 HC; lia).
      xport FR MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T0k SHB2 T1 NF MFA NEWB NEWGE SHF MCR Y RIE FAE; lia).
      xport STA MU01 WM01 ltac:(rewrite CAE; clear -SPR CEIL LO T0 T1 HC; lia).
      xport STA MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T0k SHB2 T1 NF MFA NEWB NEWGE SHF MCR Y RIE FAE; lia).
      pose proof MC2 as MC2'. (nd_pre MC2' 9%nat; intros _ _ _ _ _ _ _ ISB2 _; nd_post).
      replace (ret_pc (Z_to_bv 64 222452)) with (Z_to_bv 64 222452 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      iprefix.
      step. step. step. step.                                  (* [comment removed for export] *)
      step.                                                    (* [comment removed for export] *)
      rewrite (sx32_lit (c_count (get_cls st c) - max_cached c / 2)) by (clear -CNTc MCR KD; lia).
      step.                                                    (* [comment removed for export] *)
      pose proof (size_of_class_facts c ltac:(unfold K_NUM_CLASSES; clear -HC; lia)) as [SZP SZ16].
      eapply evtF_cut.
      { eapply (cd_main_spec RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (chunks := chunks);
        try lazymatch goal with
         | |- stk _ _ _ _ => exact ST2
         | |- ATOP <= _ => atop_facts; exact CEIL
         | |- mem_inv _ _ => assumption
         | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
         | |- rw_cells _ _ 700344 _ => exact ISB2
         | |- rw_cells _ _ (acache_addr _ _) _ => exact CR2
         | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
         | |- u32arr _ _ _ _ => exact CH2
         | |- length _ = _ => exact LCH
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
         | |- rng _ (al_t _) _ => exact RT
         | |- iclr _ _ => exact TIC                              (* [comment removed for export] *)
         end;
        unfold K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA; change (2^32) with 4294967296; change (2^37) with 137438953472;
        first [assumption | clear -CNTc MCR KD HC SZP P0 P1 SP1 SP2 T0 T1 TAL LO; lia]. }
      cbv beta. intros ms' (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & sta' & m3 & -> & MU3 & WM3 & MI3 & ST3 & CR3 & CH3 & STA3).
      apply evtF_done. cbv beta. eapply KONT.
      (* [comment removed for export] *)
      unfold cdealloc_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold nf mfa.
      split; [exact FPLE|].
      exists true, new, sj', sta'. cbn [andb].
      rewrite CI. cbn [andb].
      split; [symmetry; apply Z.eqb_eq; exact KD|].
      assert (GCX : get_cls (put_cls c (cls_set_count (c_count (get_cls st2 c) - max_cached c / 2 + 1)
                        (cls_set_num_freed (c_num_freed (get_cls st2 c) + max_cached c / 2) (get_cls st2 c))) st2) c
                    = mkAClass (c_mapped_user (get_cls st c)) (c_allocated_user (get_cls st c)) (nf + max_cached c / 2) new (c_count (get_cls st c) - max_cached c / 2 + 1)).
      { rewrite get_cls_put_cls_eq, GC2. reflexivity. }
      split; [exact GCX|].
      split. { rewrite GCX. unfold init_cache. rewrite CI. rewrite GC2. cbn [cls_set_count cls_set_num_freed c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count].
               destruct ST2E as [E|E]; rewrite E; [reflexivity|]. rewrite GC2, put_cls_put_cls. reflexivity. }
      split. { destruct UD as [E|(LT & E & FILL & R1 & R2 & BW)]; [left; exact E| right].
               split; [reflexivity|]. split; [exact LT|]. split; [exact E|]. split; [| split; [exact R1| split; [exact R2| exact BW]]].
               eapply fill_frame; [exact FILL | exact MU3 | exact WM3 |]. intros _. cbn [disjoint_from].
               clear -SPR CEIL LO SP1 SP2 HC T0 T0k SHB2 T1 NF MFA NEWB NEWGE SHF CAE. lia. }
      split; [exact NEWB|]. split; [exact NEWGE|]. split; [exact NEWM|].
      split. { unfold cd_W. cbv zeta. cbn [ic_W app]. ic_norm.
               eapply munch_trans; [eapply munch_weaken; [| exact MUN]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF NEWB NEWGE; lia)|].
               eapply munch_trans; [eapply munch_weaken; [| exact MU01]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF NEWB NEWGE; lia)|].
               eapply munch_trans; [eapply munch_weaken; [| exact MU2]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF NEWB NEWGE; lia)|].
               eapply munch_weaken; [| exact MU3]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF NEWB NEWGE; lia). }
      split; [eapply wmono_trans; [exact WM| eapply wmono_trans; [exact WM01| eapply wmono_trans; [exact WM2| exact WM3]]]|].
      split; [exact MI3|]. split; [exact ST3|].
      split. { intros j Hj NE. unfold arec_hdr.
               eapply cells_frame; [| exact MU3 | exact WM3 |].
               { eapply cells_frame; [| exact MU2 | exact WM2 |].
                 { eapply cells_frame; [exact (RECS0 j Hj) | exact MU01 | exact WM01 |].
                   cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj NE SPR CEIL LO T0 T1 HC; lia. }
                 cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. ub TSP; clear -Hj NE SPR CEIL LO T0 T0k SHB2 T1 HC SP1 SP2 RIE FAE NF MFA NEWB SHF Y; lia. }
               cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj NE SPR CEIL LO T0 T1 HC; lia. }
      split; [exact CR3|].
      split; [eapply u32arr_addr_eq; [replace (c_count (get_cls st c) - max_cached c / 2 + 1 - 1) with (c_count (get_cls st c) - max_cached c / 2) by (clear; lia); exact CH3| reflexivity]|].
      split; [eapply cells_frame; [exact MTX2 | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply cells_frame; [exact REG2 | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply junk_frame; [exact J722 | exact MU3 | exact WM3 | intros _; cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply u64arr_frame; [exact STATS2 | exact MU3 | exact WM3 | rewrite LSJ2; cbn; rewrite CAE; clear -SPR CEIL LO T0 T1 HC; lia]|].
      split; [exact LSJ2|]. split; [exact STA3|].
      split. { intros _. eapply u32arr_frame; [exact SRC2 | exact MU3 | exact WM3 |]. rewrite length_firstn, length_skipn, LCH. cbn [disjoint_from]. rewrite FAE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y NF MCR CNTc NFN; lia. }
      split; [eapply junk_frame; [exact JR2 | exact MU3 | exact WM3 | intros _; cbn; rewrite FAE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y NF MCR NEWB; lia]|].
      assert (SHF3 : 2148238848 <= shad (afreearr L c + new) /\ shad (afreearr L c + new) + shlen (536870912 - new) <= 17594332446208)
        by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC NF NEWB MCR AR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      split; [eapply azero_frame; [exact AZF2 | exact MU3 | exact WM3 | intros _; cbn [disjoint_from]; rewrite CAE; clear -SPR CEIL LO SP1 SP2 HC T0k T1 SHF3; lia]|].
      eapply m3_cells_frame; [exact MC2 | exact MU3 | exact WM3 |]. unfold AIMG_HI, AIMG_LO. rewrite CAE. ub TCX.
      repeat (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI TIC T0 T1 HC Y; lia |]). apply Forall_nil.
    + (* [comment removed for export] *)
      pose proof MC0 as MC0'. (nd_pre MC0' 9%nat; intros _ _ _ _ _ _ _ ISB0 _; nd_post).
      pose proof (size_of_class_facts c ltac:(unfold K_NUM_CLASSES; clear -HC; lia)) as [SZP SZ16].
      eapply evtF_cut.
      { eapply (cd_main_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (chunks := chunks);
        try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- ATOP <= _ => atop_facts; exact CEIL
         | |- mem_inv _ _ => assumption
         | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
         | |- rw_cells _ _ 700344 _ => exact ISB0
         | |- rw_cells _ _ (acache_addr _ _) _ => exact CR
         | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
         | |- u32arr _ _ _ _ => exact CH
         | |- length _ = _ => exact LCH
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
         | |- rng _ (al_t _) _ => exact RT
         | |- iclr _ _ => exact TIC                              (* [comment removed for export] *)
         end;
        unfold K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA; change (2^32) with 4294967296; change (2^37) with 137438953472;
        first [assumption | clear -CNTc MCR KD HC SZP P0 P1 SP1 SP2 T0 T1 TAL LO; lia]. }
      cbv beta. intros ms' (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & sta' & m3 & -> & MU3 & WM3 & MI3 & ST3 & CR3 & CH3 & STA3).
      apply evtF_done. unfold cache_dealloc. cbv zeta. unfold init_cache, max_count. rewrite !CI. fold nf.
      replace (c_count (get_cls st c) =? max_cached c) with false by (symmetry; apply Z.eqb_neq; exact KD).
      eapply KONT.
      (* [comment removed for export] *)
      unfold cdealloc_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold nf mfa. rewrite CI. cbn [andb].
      split; [apply fp_le_refl|].
      exists false, mfa, sj, sta'.
      split; [symmetry; apply Z.eqb_neq; exact KD|].
      split; [rewrite get_cls_put_cls_eq; reflexivity|].
      split; [rewrite get_cls_put_cls_eq; unfold init_cache; rewrite CI; reflexivity|].
      split; [left; reflexivity|].
      split; [clear -MFA; lia|]. split; [clear; lia|]. split; [exact MFAM|].
      split. { unfold cd_W. cbv zeta. cbn [ic_W app]. ic_norm.
               eapply munch_trans; [eapply munch_weaken; [| exact MUN]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia)|].
               eapply munch_weaken; [| exact MU3]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia). }
      split; [eapply wmono_trans; [exact WM| exact WM3]|].
      split; [exact MI3|]. split; [exact ST3|].
      split. { intros j Hj NE. unfold arec_hdr. eapply cells_frame; [exact (RECS0 j Hj) | exact MU3 | exact WM3 |].
               cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj NE SPR CEIL LO T0 T1 HC; lia. }
      split; [exact CR3|].
      split; [eapply u32arr_addr_eq; [replace (c_count (get_cls st c) + 1 - 1) with (c_count (get_cls st c)) by (clear; lia); exact CH3| reflexivity]|].
      split; [eapply cells_frame; [exact MTX | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply cells_frame; [exact REG | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply junk_frame; [exact J72 | exact MU3 | exact WM3 | intros _; cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply u64arr_frame; [exact STATS | exact MU3 | exact WM3 | rewrite LSJ; cbn; rewrite CAE; clear -SPR CEIL LO T0 T1 HC; lia]|].
      split; [exact LSJ|]. split; [exact STA3|].
      split; [intros; discriminate|].
      split; [eapply junk_frame; [exact FJ | exact MU3 | exact WM3 | intros _; cbn; rewrite FAE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y NF MFA; lia]|].
      assert (SHF3 : 2148238848 <= shad (afreearr L c + mfa) /\ shad (afreearr L c + mfa) + shlen (536870912 - mfa) <= 17594332446208)
        by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC NF MFA AR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      split; [eapply azero_frame; [exact AZF0 | exact MU3 | exact WM3 | intros _; cbn [disjoint_from]; rewrite CAE; clear -SPR CEIL LO SP1 SP2 HC T0k T1 SHF3; lia]|].
      eapply m3_cells_frame; [exact MC0 | exact MU3 | exact WM3 |]. unfold AIMG_HI, AIMG_LO. rewrite CAE. ub TCX.
      repeat (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI TIC T0 T1 HC Y; lia |]). apply Forall_nil.
  - (* [comment removed for export] *)
    replace (if false then max_cached c else 0) with 0 by reflexivity. rewrite (sx32_lit 0) by (clear; lia).
    assert (CNT0 : c_count (get_cls st c) = 0) by (clear -CNTc; lia).
    step. if_cases KM; zify_cond KM; [| exfalso; rewrite ?unsigned_lit in KM by (clear; lia); clear -KM; lia].   (* [comment removed for export] *)
    do 9 step.                                                 (* [comment removed for export] *)
    setreg 14 (Z_to_bv 64 (acache_addr L 1 + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    setreg 15 (Z_to_bv 64 (32 * 1)) ltac:(f_equal; clear; lia).
    setreg 16 (Z_to_bv 64 (1 - 16)) ltac:(f_equal; clear; lia).
    box FR. box STA. box CH. box MTX. box REG.
    eapply evtF_cut.
    { eapply (initcache_loop2_spec RNG 31 1 L (fun j => c_count (get_cls st j))); try reflexivity.
      - clear; lia.
      - intros j Hj. pose proof (RECS0 j Hj) as Rj. cbn in Rj. exact Rj.
      - assumption.
      - exact T0.
      - atop_facts; exact T1.
      - exact RT. }
    cbv beta. intros ms' (a4' & a5' & a6' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & RECS3).
    carry FR MU2 WM2 ltac:(apply ic_W_disjoint_gen; [right; clear -SPR CEIL LO T1; lia| clear; cbn; lia| clear; lia]).
    carry STA MU2 WM2 ltac:(apply ic_W_disjoint_gen; [right; clear; lia| clear; cbn; lia| clear; lia]).
    carry CH MU2 WM2 ltac:(rewrite LCH; apply ic_W_disjoint_chunks).
    carry MTX MU2 WM2 ltac:(apply ic_W_disjoint_gen; [ub TSP; rewrite RIE; unfold acache_addr; clear -SP1 SP2 HC Y; lia| clear; cbn; lia| clear; lia]).
    carry REG MU2 WM2 ltac:(apply ic_W_disjoint_gen; [ub TSP; rewrite RIE; unfold acache_addr; clear -SP1 SP2 HC Y; lia| clear; cbn; lia| clear; lia]).
    pose proof (stk_transport_disjoint asegs _ _ m2 _ _ ST MU2 WM2 ltac:(apply ic_W_disjoint_gen; [right; clear -SPR CEIL LO T1; lia| clear; cbn; lia| clear; lia])) as ST2.
    eapply junk_frame in J72; [| exact MU2 | exact WM2 | intros _; apply ic_W_disjoint_gen; [ub TSP; rewrite RIE; unfold acache_addr; clear -SP1 SP2 HC Y; lia| clear; cbn; lia| clear; lia]].
    eapply junk_frame in FJ; [| exact MU2 | exact WM2 | intros _; apply ic_W_disjoint_gen; [ub TSP; rewrite FAE; unfold acache_addr; clear -SP1 SP2 HC Y NF MFA; lia| clear; cbn; lia| clear; lia]].
    xport STATS MU2 WM2 ltac:(rewrite LSJ; apply ic_W_disjoint_gen; [right; clear; lia| clear; cbn; lia| clear; lia]).
    assert (AZF2 : azero m2 (shad (afreearr L c + mfa)) (shlen (536870912 - mfa))).
    { eapply azero_frame; [exact AZF0 | exact MU2 | exact WM2 |]. intros _. assert (SHF3 : 2148238848 <= shad (afreearr L c + mfa) /\ shad (afreearr L c + mfa) + shlen (536870912 - mfa) <= 17594332446208)
        by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC NF MFA AR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      apply ic_W_disjoint_gen; [unfold acache_addr; clear -SHF3 T0k; lia| clear; cbn; lia| clear; lia]. }   (* [comment removed for export] *)
    assert (MC2 : m3_cells L m2).
    { eapply m3_cells_frame; [exact MC0 | exact MU2 | exact WM2 |]. unfold AIMG_HI, AIMG_LO. ub TCX. cbn [ic_W]. ic_norm. unfold acache_addr.
      repeat (apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 CXI TIC T0 T1 Y; lia |]). apply Forall_nil. }
    clear ST MI AZF0 MC0.
    pose proof (RECS3 c ltac:(clear -HC; lia)) as CR2. unfold arec_hdr in CR2. rewrite CNT0 in CR2.
    step.                                                      (* [comment removed for export] *)
    rewrite (sx32_lit (max_cached c)) by (clear -MCR; lia).
    step.                                                      (* [comment removed for export] *)
    rewrite (sx32_lit 0) by (clear; lia).
    step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by (clear -MCR; lia); [| exfalso; clear -KD MCR; lia].   (* [comment removed for export] *)
    pose proof MC2 as MC2'. (nd_pre MC2' 9%nat; intros _ _ _ _ _ _ _ ISB2 _; nd_post).
    pose proof (size_of_class_facts c ltac:(unfold K_NUM_CLASSES; clear -HC; lia)) as [SZP SZ16].
    eapply evtF_cut.
    { eapply (cd_main_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (chunks := chunks) (k0 := 0);
      try lazymatch goal with
       | |- stk _ _ _ _ => exact ST2
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => assumption
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
       | |- rw_cells _ _ 700344 _ => exact ISB2
       | |- rw_cells _ _ (acache_addr _ _) _ => exact CR2
       | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
       | |- u32arr _ _ _ _ => exact CH
       | |- length _ = _ => exact LCH
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (al_t _) _ => exact RT
       | |- iclr _ _ => exact TIC                              (* [comment removed for export] *)
       end;
      unfold K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA; change (2^32) with 4294967296; change (2^37) with 137438953472;
      first [assumption | clear -CNTc MCR KD HC SZP P0 P1 SP1 SP2 T0 T1 TAL LO; lia]. }
    cbv beta. intros ms' (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & sta' & m3 & -> & MU3 & WM3 & MI3 & ST3 & CR3 & CH3 & STA3).
    apply evtF_done. unfold cache_dealloc. cbv zeta. unfold init_cache, max_count. rewrite !CI. cbn [a_cinit set_cinit].
    change (get_cls (set_cinit true st) c) with (get_cls st c). fold nf. rewrite CNT0.
    replace (0 =? max_cached c) with false by (symmetry; apply Z.eqb_neq; clear -MCR; lia).
    eapply KONT.
    (* [comment removed for export] *)
    unfold cdealloc_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold nf mfa. rewrite CI, CNT0. cbn [andb].
    split; [apply fp_le_refl|].
    exists false, mfa, sj, sta'.
    split; [reflexivity|].
    split; [rewrite get_cls_put_cls_eq; reflexivity|].
    split; [rewrite get_cls_put_cls_eq; unfold init_cache; rewrite CI; reflexivity|].
    split; [left; reflexivity|].
    split; [clear -MFA; lia|]. split; [clear; lia|]. split; [exact MFAM|].
    split. { unfold cd_W. cbv zeta. cbn [ic_W app]. ic_norm.
             eapply munch_trans; [eapply munch_weaken; [| exact MUN]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia)|].
             eapply munch_trans; [eapply munch_weaken; [| exact MU2]; cbn [ic_W]; ic_norm; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia)|].
             eapply munch_weaken; [| exact MU3]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia). }
    split; [eapply wmono_trans; [exact WM| eapply wmono_trans; [exact WM2| exact WM3]]|].
    split; [exact MI3|]. split; [exact ST3|].
    split. { intros j Hj NE. unfold arec_hdr. eapply cells_frame; [exact (RECS3 j Hj) | exact MU3 | exact WM3 |].
             cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj NE SPR CEIL LO T0 T1 HC; lia. }
    split; [exact CR3|].
    split; [eapply u32arr_addr_eq; [exact CH3| reflexivity]|].
    split; [eapply cells_frame; [exact MTX | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
    split; [eapply cells_frame; [exact REG | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
    split; [eapply junk_frame; [exact J72 | exact MU3 | exact WM3 | intros _; cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
    split; [eapply u64arr_frame; [exact STATS | exact MU3 | exact WM3 | rewrite LSJ; cbn; rewrite CAE; clear -SPR CEIL LO T0 T1 HC; lia]|].
    split; [exact LSJ|]. split; [exact STA3|].
    split; [intros; discriminate|].
    split; [eapply junk_frame; [exact FJ | exact MU3 | exact WM3 | intros _; cbn; rewrite FAE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y NF MFA; lia]|].
    assert (SHF3 : 2148238848 <= shad (afreearr L c + mfa) /\ shad (afreearr L c + mfa) + shlen (536870912 - mfa) <= 17594332446208)
        by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC NF MFA AR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    split; [eapply azero_frame; [exact AZF2 | exact MU3 | exact WM3 | intros _; cbn [disjoint_from]; rewrite CAE; clear -SPR CEIL LO SP1 SP2 HC T0k T1 SHF3; lia]|].
    eapply m3_cells_frame; [exact MC2 | exact MU3 | exact WM3 |]. unfold AIMG_HI, AIMG_LO. rewrite CAE. ub TCX.
    repeat (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI TIC T0 T1 HC Y; lia |]). apply Forall_nil.
Qed.
End Zd2.
#[using="Type"] Lemma cdealloc_spec : forall RNG {R} (k : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c P lo : Z) (sj chunks : list word) (sta : word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in let CA := acache_addr L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let cnt := c_count r in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CDEALLOC_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 c -> a3 = Z_to_bv 64 P ->
  m3_cells L m ->
  (forall j, 1 <= j <= 31 -> arec_hdr L m j (c_count (get_cls st j)) (max_count st j) (if a_cinit st then size_of_class j else 0)) ->
  u32arr asegs m (CA + 16) chunks -> length chunks = 16%nat -> Forall (fun w : word => bv_unsigned w < 2^31) (firstn (Z.to_nat cnt) chunks) ->
  rw_cells asegs m (al_t L + 2784) [C8 sta] ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  junk_at m (RI + 72) 56 ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  junk_at m (FA + 4 * nf) (mfa - 4 * nf) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  (forall j, 1 <= j <= 31 -> 0 <= c_count (get_cls st j) <= max_count st j) ->
  0 <= nf -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 4 * (nf + max_cached c / 2) <= K_FREEARR_MAX ->
  aregion L c <= P -> P < aregion L c + K_REGION ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall stX RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      cdealloc_ret L RNG sp st c P lo chunks m stX RNG' m' ->
      implS asegs RNG' (aembed ATOP (k stX)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (cache_dealloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 cdealloc_entry) fc None m (seg_rom asegs)).
Proof. exact cdealloc_spec__body. Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MM_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.WStr.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_aensure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_agetfrom.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_arefill.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_amaybe.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_areturn.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_acdrain.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac ic_norm := repeat match goal with |- context [(?a + ?b)%Z] => is_Zlit a; is_Zlit b;
                          let v := eval vm_compute in (a + b)%Z in change (a + b)%Z with v end.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
(* [comment removed for export] *)
Local Ltac find_ivw_syn :=
  first [ apply Exists_cons_hd; cbn [fst snd];
          lazymatch goal with |- (?a <= ?b /\ ?c <= ?d)%Z => constr_eq a b; constr_eq c d end; split; apply Z.le_refl
        | apply Exists_cons_tl; find_ivw_syn ].
Local Ltac find_ivw_orig tac :=
  first [ apply Exists_cons_hd; cbn [fst snd]; split; apply Z.le_refl
        | apply Exists_cons_hd; cbn [fst snd]; solve [tac]
        | apply Exists_cons_tl; find_ivw_orig tac ].
Local Ltac find_ivw tac ::= first [ find_ivw_syn | find_ivw_orig tac ].

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition cdealloc_entry : Z := 0x363ac.
End CANSEC1.
Notation CDEALLOC_STACK := 688 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma initcache_loop2_spec : forall RNG (d : nat) (i : Z) (L : alayout) (cnt : Z -> Z)
    ra sp gp tp s0 s1 a0 a1 a2 a3 t4 t5 t6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (32 - i) -> 1 <= i <= 31 ->
  (forall j, i <= j <= 31 -> arec_hdr L m j (cnt j) 0 0) ->
  mem_inv asegs m -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) ->
  rng RNG (al_t L) 4096 ->
  evtF asegs RNG (fun ms' => exists a4' a5' a6' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp (Z_to_bv 64 1024) (Z_to_bv 64 16) (Z_to_bv 64 17) s0 s1 a0 a1 a2 a3 a4' a5' a6' (Z_to_bv 64 15)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 512) t4' t5' t6') F (Z_to_bv 64 0x36530) fc None m' (seg_rom asegs)
      /\ munch (ic_W L i d) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ (forall j, i <= j <= 31 -> arec_hdr L m' j (cnt j) (max_cached j) (size_of_class j)))
    (MS (mkR ra sp gp tp (Z_to_bv 64 1024) (Z_to_bv 64 16) (Z_to_bv 64 17) s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (acache_addr L i + 8)) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15)
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 512) t4 t5 t6)
        F (Z_to_bv 64 0x364dc) fc None m (seg_rom asegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I RECS MI T0 T1 RT; [lia|]. band_lin.   (* [comment removed for export] *)
  atop_facts.
  pose proof (RECS i ltac:(lia)) as REC. unfold arec_hdr in REC.
  assert (ACE : acache_addr L i = al_t L + 208 + i * 80) by reflexivity.
  pose proof (munch_refl [(acache_addr L i + 4, acache_addr L i + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ ?P _ =>
  assert (TAILI : forall (q : Z) (t6x : word) (mm : amem), 0 <= q <= 8 -> 2 * Z.max 1 q = max_cached i ->
    rw_cells asegs mm (acache_addr L i) [C4 (Z_to_bv 64 (cnt i)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    (forall j, i + 1 <= j <= 31 -> arec_hdr L mm j (cnt j) 0 0) -> mem_inv asegs mm -> munch [(acache_addr L i + 4, acache_addr L i + 16)]%Z m mm -> wmono asegs m mm ->
    evtF asegs RNG P
      (MS (mkR ra sp gp tp (Z_to_bv 64 1024) (Z_to_bv 64 16) (Z_to_bv 64 17) s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (acache_addr L i + 8)) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 512) (Z_to_bv 64 (size_of_class i)) (Z_to_bv 64 q) t6x)
          F (Z_to_bv 64 0x364b8) fc None mm (seg_rom asegs)))
  end.
  { intros q t6x mm Q QM RECi RECS' MI' MU' WM'. clear REC MI MU WM.
    zstep. zstep. zstep. zstep. zstep.                         (* [comment removed for export] *)
    setreg 30 (Z_to_bv 64 (max_cached i))
      ltac:(apply Z_to_bv_eqm; rewrite <- QM; clear -Q; destruct (Z.ltb_spec q 1); cbn [Z.b2z]; rewrite Z.shiftl_mul_pow2 by lia; rewrite Z.mod_small by lia;
            change (2^1) with 2; lia).
    snapshot [(acache_addr L i + 4, acache_addr L i + 16)]%Z MUs WMs.
    step. step.                                                (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    setreg 14 (Z_to_bv 64 (acache_addr L (i + 1) + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    setreg 15 (Z_to_bv 64 (32 * (i + 1))) ltac:(f_equal; clear; lia).
    setreg 16 (Z_to_bv 64 (i + 1 - 16)) ltac:(f_equal; clear; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) => assert (RECS2 : forall j, i + 1 <= j <= 31 -> arec_hdr L m2 j (cnt j) 0 0) end.
    { intros j Hj. unfold arec_hdr. eapply cells_frame; [exact (RECS' j Hj) | exact MUs | exact WMs |]. cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj; lia. }
    step. if_cases KX; zify_cond KX; rewrite ?unsigned_lit in KX by (clear -I; lia).   (* [comment removed for export] *)
    - assert (I31 : i = 31) by (clear -KX I; lia). assert (D0 : d = 0%nat) by (clear -KX I HD; lia). subst d.
      apply evtF_done. do 7 eexists. split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU'|]. split; [exact WM'|]. split; [assumption|].
      intros j Hj. assert (J : j = i) by (clear -Hj I31 I; lia). subst j. unfold arec_hdr.
      lazymatch goal with H : rw_cells asegs _ (acache_addr L i) _ |- _ => exact H end.
    - eapply evtF_mono.
      { eapply (IH (i + 1) L cnt); try eassumption; clear -KX I HD T0 T1; lia. }
      cbv beta. intros ms' (a4' & a5' & a6' & t4' & t5' & t6' & m' & -> & MU2 & WM2 & MI2 & RECS3).
      do 7 eexists. split; [reflexivity|].
      split; [cbn [ic_W]; eapply munch_cons_trans; [exact MU' | exact MU2]|].
      split; [eapply wmono_trans; [exact WM' | exact WM2]|]. split; [exact MI2|].
      intros j Hj. destruct (Z.eq_dec j i) as [->|NE].
      + unfold arec_hdr. eapply cells_frame; [| exact MU2 | exact WM2 |]; [lazymatch goal with H : rw_cells asegs _ (acache_addr L i) _ |- _ => exact H end|].
        cbn [cells_size csize Nat.add]. apply ic_W_disjoint_below. unfold acache_addr. clear -I; lia.
      + apply RECS3. clear -Hj NE; lia. }
  assert (RECS' : forall j, i + 1 <= j <= 31 -> arec_hdr L m j (cnt j) 0 0) by (intros j Hj; apply RECS; clear -Hj; lia).
  step. if_cases K31; zify_cond K31; rewrite ?unsigned_lit in K31 by (clear -I; lia).   (* [comment removed for export] *)
  { (* [comment removed for export] *)
    assert (I31 : i = 31) by (clear -K31 I; lia).
    step. step. step. step. if_lit.                            (* [comment removed for export] *)
    step. step. step.                                          (* [comment removed for export] *)
    replace (Z_to_bv 64 64) with (Z_to_bv 64 (size_of_class i) : word) by (rewrite I31; reflexivity).
    eapply (TAILI 8); [clear; lia | rewrite I31, mc_31; reflexivity | exact REC | exact RECS' | exact MI | exact MU | exact WM]. }
  zstep. setreg 30 (Z_to_bv 64 i) ltac:(f_equal; clear; lia).   (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. if_cases K17; zify_cond K17; rewrite ?unsigned_lit in K17 by (clear -I; lia).   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    setreg 30 (Z_to_bv 64 (1024 / (32 * i))) ltac:(symmetry; apply v_divuw_lit; clear -I; lia).
    assert (SZE : size_of_class i = 32 * i) by (unfold size_of_class; replace (i <=? 16) with true by (symmetry; apply Z.leb_le; clear -K17; lia); reflexivity).
    pose proof TAILI as TL. rewrite SZE in TL. clear TAILI.
    step. step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (clear -I; Z.div_mod_to_equations; nia).   (* [comment removed for export] *)
    + destruct (mc_mid i ltac:(clear -I K17 K8; assert (5 <= i) by (destruct (Z_lt_le_dec i 5); [exfalso; pose proof (proj2 (mc_le4 i ltac:(lia))); lia| lia]); lia)) as [MC Q8].
      eapply (TL (1024 / (32 * i))); [clear -Q8; lia | rewrite MC; clear -Q8; lia | exact REC | exact RECS' | exact MI | exact MU | exact WM].
    + step. step.                                              (* [comment removed for export] *)
      destruct (mc_le4 i ltac:(clear -I K8; assert (i <= 4) by (destruct (Z_lt_le_dec 4 i); [exfalso; pose proof (proj2 (mc_mid i ltac:(lia))); lia| lia]); lia)) as [MC Q8].
      eapply (TL 8); [clear; lia | rewrite MC; reflexivity | exact REC | exact RECS' | exact MI | exact MU | exact WM].
  - (* [comment removed for export] *)
    do 7 zstep.                                                (* [comment removed for export] *)
    setreg 29 (Z_to_bv 64 (size_of_class i)) ltac:(symmetry; apply size_formula2; clear -I K17 K31; lia).
    (nd_pre (mc_big i ltac:(clear -I K17 K31; lia)) 3%nat; intros MC SB Q1; nd_post).
    step.                                                      (* [comment removed for export] *)
    setreg 30 (Z_to_bv 64 (1024 / size_of_class i)) ltac:(symmetry; apply v_divuw_lit; clear -SB; lia).
    step. step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (clear -SB Q1; Z.div_mod_to_equations; nia).   (* [comment removed for export] *)
    2: { exfalso. clear -K8 Q1. lia. }
    eapply (TAILI (1024 / size_of_class i)); [clear -Q1 SB; Z.div_mod_to_equations; nia | rewrite MC; clear -Q1 SB; Z.div_mod_to_equations; nia | exact REC | exact RECS' | exact MI | exact MU | exact WM].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cdmain_post (rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : alayout) (c k0 mc csz P lo : Z) (chunks : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (sta' : word) m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (acache_addr L c, acache_addr L c + 4); (acache_addr L c + 16, acache_addr L c + 80);
              (al_t L + 2784, al_t L + 2792)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (acache_addr L c) [C4 (Z_to_bv 64 (k0 + 1)); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)]
    /\ u32arr asegs m' (acache_addr L c + 16) (upd chunks (Z.to_nat k0) (Z_to_bv 64 ((P - aregion L c) / 16)))
    /\ rw_cells asegs m' (al_t L + 2784) [C8 sta'].

Definition cd_main_spec__stmt : Prop := forall RNG (rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 : word)
    (rax t0 t1 t2 a5 a6 a7 s1x s2x s3x s4x t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (c k0 mc csz P lo : Z) (chunks : list word) (sta : word),
  stk asegs m lo (bv_unsigned sp + -48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 (al_space_beg L))] ->
  rw_cells asegs m (acache_addr L c) [C4 (Z_to_bv 64 k0); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)] ->
  u32arr asegs m (acache_addr L c + 16) chunks -> length chunks = 16%nat ->
  rw_cells asegs m (al_t L + 2784) [C8 sta] ->
  1 <= c < K_NUM_CLASSES -> 0 <= k0 < 16 -> 0 <= mc < 2^31 -> 0 <= csz < 2^63 ->
  aregion L c <= P -> P < aregion L c + K_REGION ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP ->
  sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_t L) 4096 ->
  evtF asegs RNG (cdmain_post rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc L c k0 mc csz P lo chunks m)
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1x
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 c) (Z_to_bv 64 P) (Z_to_bv 64 k0) a5 a6 a7
             s2x s3x s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x363f0) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 0).
Variable rav : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 4).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 5).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 6).
Variable s2v : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 7).
Variable s3v : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 8).
Variable s4v : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 9).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 10).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 11).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 12).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 13).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 14).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 15).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 16).
Variable rax : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 17).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 18).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 19).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 20).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 21).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 22).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 23).
Variable s1x : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 24).
Variable s2x : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 25).
Variable s3x : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 26).
Variable s4x : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 34).
Variable L : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 35).
Variable c : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 36).
Variable k0 : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 37).
Variable mc : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 38).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 39).
Variable P : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 41).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 42).
Variable sta : ltac2:(SecDietF.SzSecF.ty 'cd_main_spec__stmt 43).
#[using="Type"] Lemma cd_main_spec__body : ltac:(let T := type of (fun (h : cd_main_spec__stmt) => h RNG rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 rax t0 t1 t2 a5 a6 a7 s1x s2x s3x s4x t3 t4 t5 t6 F fc m L c k0 mc csz P lo chunks sta) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (rav, (sp, (gp, (tp, (s0v, (s1v, (s2v, (s3v, (s4v, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (rax, (t0, (t1, (t2, (a5, (a6, (a7, (s1x, (s2x, (s3x, (s4x, (t3, (t4, (t5, (t6, (F, (fc, (m, (L, (c, (k0, (mc, (csz, (P, (lo, (chunks, sta)))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI FR ISB CR CH LCH STA HC K0 MC CSZ P0 P1 SP1 SP2 T0 T1 TAL TI RIMG RTLS RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AINSTANCE, K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
  word_range sp SPR.
  assert (CAE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (acache_addr L c, acache_addr L c + 4); (acache_addr L c + 16, acache_addr L c + 80);
                          (al_t L + 2784, al_t L + 2792)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  step.                                                        (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  setreg 12 (Z_to_bv 64 (acache_addr L c + 4 * k0)) ltac:(rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by (clear; lia); rewrite Z.mod_small by (clear -K0; lia); f_equal;
      change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by (clear; lia); clear; lia).
  setreg 13 (Z_to_bv 64 ((P - aregion L c) / 16))
    ltac:(rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by (clear; lia); change (2^4) with 16; change (2^32) with 4294967296; f_equal; f_equal;
          rewrite RBE; rewrite (Z.mod_small (c * 4294967296)) by (clear -HC; lia);
          rewrite (Z.mod_small (P - c * 4294967296)) by (clear -HC P0 P1 SP1 SP2 RBE; lia);
          rewrite Z.mod_small by (clear -HC P0 P1 SP1 SP2 RBE; lia); clear; lia).
  box CH. box STA. box ISB.
  snapshot [(acache_addr L c, acache_addr L c + 4)]%Z MUc WMc.
  step.                                                        (* [comment removed for export] *)
  carry CH MUc WMc ltac:(rewrite LCH; clear; lia).
  carry STA MUc WMc ltac:(rewrite CAE; clear -HC; lia).
  carry ISB MUc WMc ltac:(rewrite CAE; clear -HC TI; lia).   (* [comment removed for export] *)
  clear MUc WMc.
  pose proof (u32arr_store_ok asegs _ (acache_addr L c + 16) _ k0 (wa (acache_addr L c + 16 + 4 * k0)) CH ltac:(rewrite LCH; clear -K0; lia) eq_refl) as SOK.
  box CR. box STA. box ISB. box FR.
  snapshot [(acache_addr L c + 16, acache_addr L c + 80)]%Z MUa WMa.
  step.                                                        (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a (le4 ?v)) _) =>
    pose proof (u32arr_write asegs mm (acache_addr L c + 16) _ k0 v CH ltac:(rewrite LCH; clear -K0; lia)) as CH2
  end.
  clear CH. store_done. try clear SOK.
  carry CR MUa WMa ltac:(clear; lia). carry STA MUa WMa ltac:(rewrite CAE; clear -HC; lia). carry ISB MUa WMa ltac:(rewrite CAE; clear -HC TI; lia).
  carry FR MUa WMa ltac:(rewrite CAE; clear -HC T1 SPR CEIL LO; lia). clear MUa WMa.
  zstep.                                                       (* [comment removed for export] *)
  assert (AMO : amo_aligned AD (Z_to_bv 64 (al_t L + 2784)) = true) by (pose proof atop_range as AR; apply amo_alignedD_intro; [clear -TI T1 AR; lia| clear -TAL; Z.div_mod_to_equations; lia]).   (* [comment removed for export] *)
  box CH2. box CR. box ISB.
  snapshot [(al_t L + 2784, al_t L + 2792)]%Z MUb WMb.
  amo_stepA AMO.                                               (* [comment removed for export] *)
  carry CH2 MUb WMb ltac:(rewrite ?upd_length, LCH, CAE; clear -HC; lia). carry CR MUb WMb ltac:(rewrite CAE; clear -HC; lia). carry ISB MUb WMb ltac:(clear -TI; lia).
  clear MUb WMb.
  do 8 step.                                                   (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  unfold cdmain_post. finish.
  all: try eassumption.
Qed.
End Zd1.
#[using="Type"] Lemma cd_main_spec : ltac:(let t := eval cbv delta [cd_main_spec__stmt] in cd_main_spec__stmt in exact t).
Proof. exact cd_main_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma get_cls_init_cache : forall st c, get_cls (init_cache st) c = get_cls st c.
Proof. intros st c. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
#[using="Type"] Lemma a_cinit_init_cache : forall st, a_cinit (init_cache st) = true.
Proof. intros st. unfold init_cache. destruct (a_cinit st) eqn:E; [exact E| reflexivity]. Qed.
#[using="Type"] Lemma max_count_init_cache : forall st c, max_count (init_cache st) c = max_cached c.
Proof. intros st c. unfold max_count. rewrite a_cinit_init_cache. reflexivity. Qed.
#[using="Type"] Lemma put_cls_put_cls : forall c x y st, put_cls c x (put_cls c y st) = put_cls c x st.
Proof. intros c x y st. unfold put_cls, set_cls. cbn. f_equal. rewrite insert_insert. destruct (decide (c = c)) as [|NE]; [reflexivity| exfalso; apply NE; reflexivity]. Qed.
#[using="Type"] Lemma get_cls_put_cls_same : forall c r st, get_cls (put_cls c r st) c = r.
Proof. intros. apply get_cls_put_cls_eq. Qed.

(* [comment removed for export] *)
Definition cd_W (L : alayout) (sp : Z) (c nf mfa mfa' : Z) : list (Z * Z) :=
  let CA := acache_addr L c in let FA := afreearr L c in let RI := aregion_info L c in
  ([(sp - 688, sp)] ++ ic_W L 1 31 ++
   [(CA, CA + 4); (CA + 16, CA + 80); (al_t L + 2784, al_t L + 2792); (al_t L + 2800, al_t L + 3168);
    (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
    (RI, RI + 8); (RI + 16, RI + 32); (RI + 72, RI + 128)])%Z.

(* [comment removed for export] *)
Definition cdealloc_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c P lo : Z) (chunks : list word) (m : amem)
    (stX : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st c in let CA := acache_addr L c in let FA := afreearr L c in let RI := aregion_info L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let mc := max_cached c in let half := mc / 2 in let cnt := c_count r in
  fp_le RNG RNG' /\
  exists (drained : bool) mfa' sj' (sta' : word),
  let nf' := if drained then nf + half else nf in
  let cnt' := if drained then cnt - half + 1 else cnt + 1 in
     (* [comment removed for export] *)
     drained = (a_cinit st && (cnt =? mc))%bool
  /\ get_cls stX c = mkAClass (c_mapped_user r) (c_allocated_user r) nf' mfa' cnt'
  /\ stX = put_cls c (get_cls stX c) (init_cache st)
  /\ (   mfa' = mfa
      \/ (drained = true /\ mfa < 4 * (nf + half) /\ mfa' = rup (4 * (nf + half)) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf' <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
     (* [comment removed for export] *)
  /\ munch (cd_W L (bv_unsigned sp) c nf mfa mfa') m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
     (* [comment removed for export] *)
  /\ (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m' j (c_count (get_cls st j)) (max_cached j) (size_of_class j))
  /\ arec_hdr L m' c cnt' (max_cached c) (size_of_class c)
  /\ u32arr asegs m' (CA + 16) (upd chunks (Z.to_nat (cnt' - 1)) (Z_to_bv 64 ((P - aregion L c) / 16)))
  /\ rw_cells asegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' (RI + 16)
       [C8 (Z_to_bv 64 nf'); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)]
  /\ junk_at m' (RI + 72) 56
  /\ u64arr asegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ rw_cells asegs m' (al_t L + 2784) [C8 sta']
  /\ (drained = true -> u32arr asegs m' (FA + 4 * nf) (firstn (Z.to_nat half) (skipn (Z.to_nat (cnt - half)) chunks)))
  /\ junk_at m' (FA + 4 * nf') (mfa' - 4 * nf')
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

Definition cdealloc_spec__stmt : Prop := forall RNG {R} (k : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c P lo : Z) (sj chunks : list word) (sta : word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in let CA := acache_addr L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let cnt := c_count r in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CDEALLOC_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 c -> a3 = Z_to_bv 64 P ->
  m3_cells L m ->
  (forall j, 1 <= j <= 31 -> arec_hdr L m j (c_count (get_cls st j)) (max_count st j) (if a_cinit st then size_of_class j else 0)) ->
  u32arr asegs m (CA + 16) chunks -> length chunks = 16%nat -> Forall (fun w : word => bv_unsigned w < 2^31) (firstn (Z.to_nat cnt) chunks) ->
  rw_cells asegs m (al_t L + 2784) [C8 sta] ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  junk_at m (RI + 72) 56 ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  junk_at m (FA + 4 * nf) (mfa - 4 * nf) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  (forall j, 1 <= j <= 31 -> 0 <= c_count (get_cls st j) <= max_count st j) ->
  0 <= nf -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 4 * (nf + max_cached c / 2) <= K_FREEARR_MAX ->
  aregion L c <= P -> P < aregion L c + K_REGION ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall stX RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      cdealloc_ret L RNG sp st c P lo chunks m stX RNG' m' ->
      implS asegs RNG' (aembed ATOP (k stX)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (cache_dealloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 cdealloc_entry) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 1).
Variable k : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 37).
Variable L : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 38).
Variable st : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 39).
Variable c : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 40).
Variable P : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 41).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 42).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 43).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 44).
Variable sta : ltac2:(SecDietF.SzSecF.ty 'cdealloc_spec__stmt 45).
Let nf := c_num_freed (get_cls st c).
Let mfa := c_mapped_free_array (get_cls st c).
#[using="nf mfa"] Lemma cdealloc_spec__body : ltac:(let T := type of (fun (h : cdealloc_spec__stmt) => h RNG R k Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c P lo sj chunks sta) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (k, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (L, (st, (c, (P, (lo, (sj, (chunks, sta)))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC RECS CH LCH CH31 STA MTX REG J72 STATS LSJ FJ AZF SBE HC CNTS NF MFA MFAM NFN P0 P1
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RTLS RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  destruct (sclr_int _ _ T0 ltac:(clear -TIC; lia) ltac:(pose proof atop_range as AR; clear -T1 AR; lia)) as (kT0 & T0k).   (* [comment removed for export] *)
  pose proof atop_range as AR.   (* [comment removed for export] *)
  unfold AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, cdealloc_entry in *.
  change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
  word_range sp SPR.
  chg (c_num_freed (get_cls st c)) nf. chg (c_mapped_free_array (get_cls st c)) mfa.
  assert (CAE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCEV].
  pose proof (CNTS c ltac:(clear -HC; lia)) as CNTc. fold nf in CNTc.
  pose proof (RECS c ltac:(clear -HC; lia)) as CR. unfold arec_hdr in CR.
  box TCX. box SCX. box TSP.
  pose proof (munch_refl [(bv_unsigned sp - 688, bv_unsigned sp)]%Z m) as MUN. pose proof (wmono_refl asegs m) as WM.
  iprefix.
  carve_frame 48%nat ST.
  box MTX. box REG. box STA. box CH. box STATS. clear CR.
  do 7 step.                                                   (* [comment removed for export] *)
  carry STATS MUN WM ltac:(rewrite LSJ; clear -SPR CEIL LO T0 T1; lia).
  carry MTX MUN WM ltac:(rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC; lia).
  carry REG MUN WM ltac:(rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC; lia).
  carry STA MUN WM ltac:(clear -SPR CEIL LO T0 T1; lia).
  carry CH MUN WM ltac:(rewrite LCH, CAE; clear -SPR CEIL LO T0 T1 HC; lia).
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RECS0 : forall j, 1 <= j <= 31 -> arec_hdr L mm j (c_count (get_cls st j)) (max_count st j) (if a_cinit st then size_of_class j else 0));
    [ intros j Hj; unfold arec_hdr; eapply cells_frame; [exact (RECS j Hj) | exact MUN | exact WM |];
      cbn [disjoint_from cells_size csize Nat.add]; unfold acache_addr; clear -Hj SPR CEIL LO T0 T1; lia |]
  end.
  clear RECS.
  eapply junk_frame in J72; [| exact MUN | exact WM | intros _; cbn [disjoint_from]; rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC; lia].
  eapply junk_frame in FJ; [| exact MUN | exact WM | intros _; cbn [disjoint_from]; rewrite FAE; clear -SPR CEIL LO SP1 SP2 HC NF MFA; lia].
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AZF0 : azero mm (shad (afreearr L c + mfa)) (shlen (536870912 - mfa)));
    [ eapply azero_frame; [exact AZF | exact MUN | exact WM |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC SPR CEIL LO MFA NF; Z.div_mod_to_equations; lia |];
    assert (MC0 : m3_cells L mm);
    [ eapply m3_cells_frame; [exact MC | exact MUN | exact WM |]; unfold AIMG_HI, AIMG_LO;
      apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 CXI TIC SPR CEIL LO T1; lia |]; apply Forall_nil |]
  end.
  clear AZF MC.
  pose proof (RECS0 c ltac:(clear -HC; lia)) as CR. unfold arec_hdr in CR.
  step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (clear -HC; lia); clear -KZ HC; lia|].   (* [comment removed for export] *)
  step. step. if_cases K32; zify_cond K32; [exfalso; rewrite ?unsigned_lit in K32 by (clear -HC; lia); clear -K32 HC; lia|].   (* [comment removed for export] *)
  step. zstep. zstep.                                          (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 (acache_addr L c)) ltac:(rewrite CAE; f_equal; clear; lia).
  step.                                                        (* [comment removed for export] *)
  unfold max_count in *.
  destruct (a_cinit st) eqn:CI.
  - (* [comment removed for export] *)
    rewrite (sx32_lit (max_cached c)) by (clear -MCR; lia).
    step. if_cases KM; zify_cond KM; [exfalso; rewrite ?unsigned_lit in KM by (clear -MCR; lia); clear -KM MCR; lia|].   (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    rewrite (sx32_lit (c_count (get_cls st c))) by (clear -CNTc MCR; lia).
    step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by (clear -CNTc MCR; lia).   (* [comment removed for export] *)
    + (* [comment removed for export] *)
      do 7 step.                                               (* [comment removed for export] *)
      step.                                                    (* [comment removed for export] *)
      apply evtF_done.
      unfold cache_dealloc. cbv zeta. unfold init_cache, max_count. rewrite !CI. fold nf.
      replace (c_count (get_cls st c) =? max_cached c) with true by (symmetry; apply Z.eqb_eq; exact KD).
      name_sp sp (-48).
      eapply cdrain_spec with (lo := lo) (L := L) (sj := sj) (chunks := chunks) (cnt := c_count (get_cls st c)) (mc := max_cached c) (csz := size_of_class c);
      try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- iclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
       | |- m3_cells _ _ => exact MC0
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (acache_addr _ _) _ => exact CR
       | |- junk_at _ (aregion_info _ _ + 72) _ => exact J72
       | |- junk_at _ _ _ => exact FJ
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ _ _ => exact CH
       | |- length _ = _ => first [exact LSJ | exact LCH]
       | |- Forall _ _ => exact CH31
       | |- azero _ _ _ => exact AZF0
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
      all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
              clear KONT; fold nf mfa; first [assumption | clear -NF MFA MFAM NFN HC SP1 SP2 SP3 CX0 CX1 T0 T1 CNTc KD MCR; lia]).
      (* [comment removed for export] *)
      intros st2 RNG' m2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' DR.
      unfold cdrain_ret in DR. cbv zeta in DR. (nd_pre DR 7%nat; intros md MU01 WM01 RR CR2 CH2 ST2; nd_post).
      pose proof RR as RR0. unfold rta_ret, K_FREEARR_MAX, K_FREEARR_MAP in RR0. cbv zeta in RR0. fold nf mfa in RR0.
      (nd_pre RR0 22%nat; intros FPLE new sj' UD NEWB NEWGE NEWM GC2 ST2E MU2 WM2 MI2 _ MTX2 REG2 J722 STATS2 LSJ2 SRC2 JR2 AZF2 MC2; nd_post).
      rewrite Hsp in *. unname_sp.
      rewrite ?unsigned_lit in MU2 by (clear -SPR CEIL LO; lia).
      rewrite ?unsigned_lit in ST2 by (clear -SPR CEIL LO; lia).
      apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RTLS. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RT.
      assert (SHF : shad (afreearr L c + mfa) + shlen (new - mfa) <= 0x10007fff8000).
      { rewrite !shad_div, !shlen_div, FAE. unfold ASHOFF. clear -SP1 SP2 HC MFA NF NEWB NEWGE MCR. Z.div_mod_to_equations. lia. }
      assert (SHB2 : 2148239360 <= shad (afreearr L c + mfa)) by (rewrite shad_div, FAE; unfold ASHOFF; clear -SP1 HC MFA NF; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      xport FR MU01 WM01 ltac:(rewrite CAE; clear -SPR CEIL LO T1 HC; lia).
      xport FR MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T0k SHB2 T1 NF MFA NEWB NEWGE SHF MCR Y RIE FAE; lia).
      xport STA MU01 WM01 ltac:(rewrite CAE; clear -SPR CEIL LO T0 T1 HC; lia).
      xport STA MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T0k SHB2 T1 NF MFA NEWB NEWGE SHF MCR Y RIE FAE; lia).
      pose proof MC2 as MC2'. (nd_pre MC2' 9%nat; intros _ _ _ _ _ _ _ ISB2 _; nd_post).
      replace (ret_pc (Z_to_bv 64 222556)) with (Z_to_bv 64 222556 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      iprefix.
      step. step. step. step.                                  (* [comment removed for export] *)
      step.                                                    (* [comment removed for export] *)
      rewrite (sx32_lit (c_count (get_cls st c) - max_cached c / 2)) by (clear -CNTc MCR KD; lia).
      step.                                                    (* [comment removed for export] *)
      pose proof (size_of_class_facts c ltac:(unfold K_NUM_CLASSES; clear -HC; lia)) as [SZP SZ16].
      eapply evtF_cut.
      { eapply (cd_main_spec RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (chunks := chunks);
        try lazymatch goal with
         | |- stk _ _ _ _ => exact ST2
         | |- ATOP <= _ => atop_facts; exact CEIL
         | |- mem_inv _ _ => assumption
         | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
         | |- rw_cells _ _ 701368 _ => exact ISB2
         | |- rw_cells _ _ (acache_addr _ _) _ => exact CR2
         | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
         | |- u32arr _ _ _ _ => exact CH2
         | |- length _ = _ => exact LCH
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
         | |- rng _ (al_t _) _ => exact RT
         | |- iclr _ _ => exact TIC                              (* [comment removed for export] *)
         end;
        unfold K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA; change (2^32) with 4294967296; change (2^37) with 137438953472;
        first [assumption | clear -CNTc MCR KD HC SZP P0 P1 SP1 SP2 T0 T1 TAL LO; lia]. }
      cbv beta. intros ms' (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & sta' & m3 & -> & MU3 & WM3 & MI3 & ST3 & CR3 & CH3 & STA3).
      apply evtF_done. cbv beta. eapply KONT.
      (* [comment removed for export] *)
      unfold cdealloc_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold nf mfa.
      split; [exact FPLE|].
      exists true, new, sj', sta'. cbn [andb].
      rewrite CI. cbn [andb].
      split; [symmetry; apply Z.eqb_eq; exact KD|].
      assert (GCX : get_cls (put_cls c (cls_set_count (c_count (get_cls st2 c) - max_cached c / 2 + 1)
                        (cls_set_num_freed (c_num_freed (get_cls st2 c) + max_cached c / 2) (get_cls st2 c))) st2) c
                    = mkAClass (c_mapped_user (get_cls st c)) (c_allocated_user (get_cls st c)) (nf + max_cached c / 2) new (c_count (get_cls st c) - max_cached c / 2 + 1)).
      { rewrite get_cls_put_cls_eq, GC2. reflexivity. }
      split; [exact GCX|].
      split. { rewrite GCX. unfold init_cache. rewrite CI. rewrite GC2. cbn [cls_set_count cls_set_num_freed c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count].
               destruct ST2E as [E|E]; rewrite E; [reflexivity|]. rewrite GC2, put_cls_put_cls. reflexivity. }
      split. { destruct UD as [E|(LT & E & FILL & R1 & R2 & BW)]; [left; exact E| right].
               split; [reflexivity|]. split; [exact LT|]. split; [exact E|]. split; [| split; [exact R1| split; [exact R2| exact BW]]].
               eapply fill_frame; [exact FILL | exact MU3 | exact WM3 |]. intros _. cbn [disjoint_from].
               clear -SPR CEIL LO SP1 SP2 HC T0 T0k SHB2 T1 NF MFA NEWB NEWGE SHF CAE. lia. }
      split; [exact NEWB|]. split; [exact NEWGE|]. split; [exact NEWM|].
      split. { unfold cd_W. cbv zeta. cbn [ic_W app]. ic_norm.
               eapply munch_trans; [eapply munch_weaken; [| exact MUN]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF NEWB NEWGE; lia)|].
               eapply munch_trans; [eapply munch_weaken; [| exact MU01]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF NEWB NEWGE; lia)|].
               eapply munch_trans; [eapply munch_weaken; [| exact MU2]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF NEWB NEWGE; lia)|].
               eapply munch_weaken; [| exact MU3]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF NEWB NEWGE; lia). }
      split; [eapply wmono_trans; [exact WM| eapply wmono_trans; [exact WM01| eapply wmono_trans; [exact WM2| exact WM3]]]|].
      split; [exact MI3|]. split; [exact ST3|].
      split. { intros j Hj NE. unfold arec_hdr.
               eapply cells_frame; [| exact MU3 | exact WM3 |].
               { eapply cells_frame; [| exact MU2 | exact WM2 |].
                 { eapply cells_frame; [exact (RECS0 j Hj) | exact MU01 | exact WM01 |].
                   cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj NE SPR CEIL LO T0 T1 HC; lia. }
                 cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. ub TSP; clear -Hj NE SPR CEIL LO T0 T0k SHB2 T1 HC SP1 SP2 RIE FAE NF MFA NEWB SHF Y; lia. }
               cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj NE SPR CEIL LO T0 T1 HC; lia. }
      split; [exact CR3|].
      split; [eapply u32arr_addr_eq; [replace (c_count (get_cls st c) - max_cached c / 2 + 1 - 1) with (c_count (get_cls st c) - max_cached c / 2) by (clear; lia); exact CH3| reflexivity]|].
      split; [eapply cells_frame; [exact MTX2 | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply cells_frame; [exact REG2 | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply junk_frame; [exact J722 | exact MU3 | exact WM3 | intros _; cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply u64arr_frame; [exact STATS2 | exact MU3 | exact WM3 | rewrite LSJ2; cbn; rewrite CAE; clear -SPR CEIL LO T0 T1 HC; lia]|].
      split; [exact LSJ2|]. split; [exact STA3|].
      split. { intros _. eapply u32arr_frame; [exact SRC2 | exact MU3 | exact WM3 |]. rewrite length_firstn, length_skipn, LCH. cbn [disjoint_from]. rewrite FAE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y NF MCR CNTc NFN; lia. }
      split; [eapply junk_frame; [exact JR2 | exact MU3 | exact WM3 | intros _; cbn; rewrite FAE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y NF MCR NEWB; lia]|].
      assert (SHF3 : 2148239360 <= shad (afreearr L c + new) /\ shad (afreearr L c + new) + shlen (536870912 - new) <= 17594332446208)
        by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC NF NEWB MCR AR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      split; [eapply azero_frame; [exact AZF2 | exact MU3 | exact WM3 | intros _; cbn [disjoint_from]; rewrite CAE; clear -SPR CEIL LO SP1 SP2 HC T0k T1 SHF3; lia]|].
      eapply m3_cells_frame; [exact MC2 | exact MU3 | exact WM3 |]. unfold AIMG_HI, AIMG_LO. rewrite CAE. ub TCX.
      repeat (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI TIC T0 T1 HC Y; lia |]). apply Forall_nil.
    + (* [comment removed for export] *)
      pose proof MC0 as MC0'. (nd_pre MC0' 9%nat; intros _ _ _ _ _ _ _ ISB0 _; nd_post).
      pose proof (size_of_class_facts c ltac:(unfold K_NUM_CLASSES; clear -HC; lia)) as [SZP SZ16].
      eapply evtF_cut.
      { eapply (cd_main_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (chunks := chunks);
        try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- ATOP <= _ => atop_facts; exact CEIL
         | |- mem_inv _ _ => assumption
         | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
         | |- rw_cells _ _ 701368 _ => exact ISB0
         | |- rw_cells _ _ (acache_addr _ _) _ => exact CR
         | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
         | |- u32arr _ _ _ _ => exact CH
         | |- length _ = _ => exact LCH
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
         | |- rng _ (al_t _) _ => exact RT
         | |- iclr _ _ => exact TIC                              (* [comment removed for export] *)
         end;
        unfold K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA; change (2^32) with 4294967296; change (2^37) with 137438953472;
        first [assumption | clear -CNTc MCR KD HC SZP P0 P1 SP1 SP2 T0 T1 TAL LO; lia]. }
      cbv beta. intros ms' (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & sta' & m3 & -> & MU3 & WM3 & MI3 & ST3 & CR3 & CH3 & STA3).
      apply evtF_done. unfold cache_dealloc. cbv zeta. unfold init_cache, max_count. rewrite !CI. fold nf.
      replace (c_count (get_cls st c) =? max_cached c) with false by (symmetry; apply Z.eqb_neq; exact KD).
      eapply KONT.
      (* [comment removed for export] *)
      unfold cdealloc_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold nf mfa. rewrite CI. cbn [andb].
      split; [apply fp_le_refl|].
      exists false, mfa, sj, sta'.
      split; [symmetry; apply Z.eqb_neq; exact KD|].
      split; [rewrite get_cls_put_cls_eq; reflexivity|].
      split; [rewrite get_cls_put_cls_eq; unfold init_cache; rewrite CI; reflexivity|].
      split; [left; reflexivity|].
      split; [clear -MFA; lia|]. split; [clear; lia|]. split; [exact MFAM|].
      split. { unfold cd_W. cbv zeta. cbn [ic_W app]. ic_norm.
               eapply munch_trans; [eapply munch_weaken; [| exact MUN]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia)|].
               eapply munch_weaken; [| exact MU3]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia). }
      split; [eapply wmono_trans; [exact WM| exact WM3]|].
      split; [exact MI3|]. split; [exact ST3|].
      split. { intros j Hj NE. unfold arec_hdr. eapply cells_frame; [exact (RECS0 j Hj) | exact MU3 | exact WM3 |].
               cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj NE SPR CEIL LO T0 T1 HC; lia. }
      split; [exact CR3|].
      split; [eapply u32arr_addr_eq; [replace (c_count (get_cls st c) + 1 - 1) with (c_count (get_cls st c)) by (clear; lia); exact CH3| reflexivity]|].
      split; [eapply cells_frame; [exact MTX | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply cells_frame; [exact REG | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply junk_frame; [exact J72 | exact MU3 | exact WM3 | intros _; cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply u64arr_frame; [exact STATS | exact MU3 | exact WM3 | rewrite LSJ; cbn; rewrite CAE; clear -SPR CEIL LO T0 T1 HC; lia]|].
      split; [exact LSJ|]. split; [exact STA3|].
      split; [intros; discriminate|].
      split; [eapply junk_frame; [exact FJ | exact MU3 | exact WM3 | intros _; cbn; rewrite FAE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y NF MFA; lia]|].
      assert (SHF3 : 2148239360 <= shad (afreearr L c + mfa) /\ shad (afreearr L c + mfa) + shlen (536870912 - mfa) <= 17594332446208)
        by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC NF MFA AR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      split; [eapply azero_frame; [exact AZF0 | exact MU3 | exact WM3 | intros _; cbn [disjoint_from]; rewrite CAE; clear -SPR CEIL LO SP1 SP2 HC T0k T1 SHF3; lia]|].
      eapply m3_cells_frame; [exact MC0 | exact MU3 | exact WM3 |]. unfold AIMG_HI, AIMG_LO. rewrite CAE. ub TCX.
      repeat (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI TIC T0 T1 HC Y; lia |]). apply Forall_nil.
  - (* [comment removed for export] *)
    replace (if false then max_cached c else 0) with 0 by reflexivity. rewrite (sx32_lit 0) by (clear; lia).
    assert (CNT0 : c_count (get_cls st c) = 0) by (clear -CNTc; lia).
    step. if_cases KM; zify_cond KM; [| exfalso; rewrite ?unsigned_lit in KM by (clear; lia); clear -KM; lia].   (* [comment removed for export] *)
    do 9 step.                                                 (* [comment removed for export] *)
    setreg 14 (Z_to_bv 64 (acache_addr L 1 + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    setreg 15 (Z_to_bv 64 (32 * 1)) ltac:(f_equal; clear; lia).
    setreg 16 (Z_to_bv 64 (1 - 16)) ltac:(f_equal; clear; lia).
    box FR. box STA. box CH. box MTX. box REG.
    eapply evtF_cut.
    { eapply (initcache_loop2_spec RNG 31 1 L (fun j => c_count (get_cls st j))); try reflexivity.
      - clear; lia.
      - intros j Hj. pose proof (RECS0 j Hj) as Rj. cbn in Rj. exact Rj.
      - assumption.
      - exact T0.
      - atop_facts; exact T1.
      - exact RT. }
    cbv beta. intros ms' (a4' & a5' & a6' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & RECS3).
    carry FR MU2 WM2 ltac:(apply ic_W_disjoint_gen; [right; clear -SPR CEIL LO T1; lia| clear; cbn; lia| clear; lia]).
    carry STA MU2 WM2 ltac:(apply ic_W_disjoint_gen; [right; clear; lia| clear; cbn; lia| clear; lia]).
    carry CH MU2 WM2 ltac:(rewrite LCH; apply ic_W_disjoint_chunks).
    carry MTX MU2 WM2 ltac:(apply ic_W_disjoint_gen; [ub TSP; rewrite RIE; unfold acache_addr; clear -SP1 SP2 HC Y; lia| clear; cbn; lia| clear; lia]).
    carry REG MU2 WM2 ltac:(apply ic_W_disjoint_gen; [ub TSP; rewrite RIE; unfold acache_addr; clear -SP1 SP2 HC Y; lia| clear; cbn; lia| clear; lia]).
    pose proof (stk_transport_disjoint asegs _ _ m2 _ _ ST MU2 WM2 ltac:(apply ic_W_disjoint_gen; [right; clear -SPR CEIL LO T1; lia| clear; cbn; lia| clear; lia])) as ST2.
    eapply junk_frame in J72; [| exact MU2 | exact WM2 | intros _; apply ic_W_disjoint_gen; [ub TSP; rewrite RIE; unfold acache_addr; clear -SP1 SP2 HC Y; lia| clear; cbn; lia| clear; lia]].
    eapply junk_frame in FJ; [| exact MU2 | exact WM2 | intros _; apply ic_W_disjoint_gen; [ub TSP; rewrite FAE; unfold acache_addr; clear -SP1 SP2 HC Y NF MFA; lia| clear; cbn; lia| clear; lia]].
    xport STATS MU2 WM2 ltac:(rewrite LSJ; apply ic_W_disjoint_gen; [right; clear; lia| clear; cbn; lia| clear; lia]).
    assert (AZF2 : azero m2 (shad (afreearr L c + mfa)) (shlen (536870912 - mfa))).
    { eapply azero_frame; [exact AZF0 | exact MU2 | exact WM2 |]. intros _. assert (SHF3 : 2148239360 <= shad (afreearr L c + mfa) /\ shad (afreearr L c + mfa) + shlen (536870912 - mfa) <= 17594332446208)
        by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC NF MFA AR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      apply ic_W_disjoint_gen; [unfold acache_addr; clear -SHF3 T0k; lia| clear; cbn; lia| clear; lia]. }   (* [comment removed for export] *)
    assert (MC2 : m3_cells L m2).
    { eapply m3_cells_frame; [exact MC0 | exact MU2 | exact WM2 |]. unfold AIMG_HI, AIMG_LO. ub TCX. cbn [ic_W]. ic_norm. unfold acache_addr.
      repeat (apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 CXI TIC T0 T1 Y; lia |]). apply Forall_nil. }
    clear ST MI AZF0 MC0.
    pose proof (RECS3 c ltac:(clear -HC; lia)) as CR2. unfold arec_hdr in CR2. rewrite CNT0 in CR2.
    step.                                                      (* [comment removed for export] *)
    rewrite (sx32_lit (max_cached c)) by (clear -MCR; lia).
    step.                                                      (* [comment removed for export] *)
    rewrite (sx32_lit 0) by (clear; lia).
    step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by (clear -MCR; lia); [| exfalso; clear -KD MCR; lia].   (* [comment removed for export] *)
    pose proof MC2 as MC2'. (nd_pre MC2' 9%nat; intros _ _ _ _ _ _ _ ISB2 _; nd_post).
    pose proof (size_of_class_facts c ltac:(unfold K_NUM_CLASSES; clear -HC; lia)) as [SZP SZ16].
    eapply evtF_cut.
    { eapply (cd_main_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (chunks := chunks) (k0 := 0);
      try lazymatch goal with
       | |- stk _ _ _ _ => exact ST2
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => assumption
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
       | |- rw_cells _ _ 701368 _ => exact ISB2
       | |- rw_cells _ _ (acache_addr _ _) _ => exact CR2
       | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
       | |- u32arr _ _ _ _ => exact CH
       | |- length _ = _ => exact LCH
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (al_t _) _ => exact RT
       | |- iclr _ _ => exact TIC                              (* [comment removed for export] *)
       end;
      unfold K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA; change (2^32) with 4294967296; change (2^37) with 137438953472;
      first [assumption | clear -CNTc MCR KD HC SZP P0 P1 SP1 SP2 T0 T1 TAL LO; lia]. }
    cbv beta. intros ms' (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & sta' & m3 & -> & MU3 & WM3 & MI3 & ST3 & CR3 & CH3 & STA3).
    apply evtF_done. unfold cache_dealloc. cbv zeta. unfold init_cache, max_count. rewrite !CI. cbn [a_cinit set_cinit].
    change (get_cls (set_cinit true st) c) with (get_cls st c). fold nf. rewrite CNT0.
    replace (0 =? max_cached c) with false by (symmetry; apply Z.eqb_neq; clear -MCR; lia).
    eapply KONT.
    (* [comment removed for export] *)
    unfold cdealloc_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold nf mfa. rewrite CI, CNT0. cbn [andb].
    split; [apply fp_le_refl|].
    exists false, mfa, sj, sta'.
    split; [reflexivity|].
    split; [rewrite get_cls_put_cls_eq; reflexivity|].
    split; [rewrite get_cls_put_cls_eq; unfold init_cache; rewrite CI; reflexivity|].
    split; [left; reflexivity|].
    split; [clear -MFA; lia|]. split; [clear; lia|]. split; [exact MFAM|].
    split. { unfold cd_W. cbv zeta. cbn [ic_W app]. ic_norm.
             eapply munch_trans; [eapply munch_weaken; [| exact MUN]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia)|].
             eapply munch_trans; [eapply munch_weaken; [| exact MU2]; cbn [ic_W]; ic_norm; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia)|].
             eapply munch_weaken; [| exact MU3]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia). }
    split; [eapply wmono_trans; [exact WM| eapply wmono_trans; [exact WM2| exact WM3]]|].
    split; [exact MI3|]. split; [exact ST3|].
    split. { intros j Hj NE. unfold arec_hdr. eapply cells_frame; [exact (RECS3 j Hj) | exact MU3 | exact WM3 |].
             cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj NE SPR CEIL LO T0 T1 HC; lia. }
    split; [exact CR3|].
    split; [eapply u32arr_addr_eq; [exact CH3| reflexivity]|].
    split; [eapply cells_frame; [exact MTX | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
    split; [eapply cells_frame; [exact REG | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
    split; [eapply junk_frame; [exact J72 | exact MU3 | exact WM3 | intros _; cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
    split; [eapply u64arr_frame; [exact STATS | exact MU3 | exact WM3 | rewrite LSJ; cbn; rewrite CAE; clear -SPR CEIL LO T0 T1 HC; lia]|].
    split; [exact LSJ|]. split; [exact STA3|].
    split; [intros; discriminate|].
    split; [eapply junk_frame; [exact FJ | exact MU3 | exact WM3 | intros _; cbn; rewrite FAE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y NF MFA; lia]|].
    assert (SHF3 : 2148239360 <= shad (afreearr L c + mfa) /\ shad (afreearr L c + mfa) + shlen (536870912 - mfa) <= 17594332446208)
        by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC NF MFA AR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    split; [eapply azero_frame; [exact AZF2 | exact MU3 | exact WM3 | intros _; cbn [disjoint_from]; rewrite CAE; clear -SPR CEIL LO SP1 SP2 HC T0k T1 SHF3; lia]|].
    eapply m3_cells_frame; [exact MC2 | exact MU3 | exact WM3 |]. unfold AIMG_HI, AIMG_LO. rewrite CAE. ub TCX.
    repeat (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI TIC T0 T1 HC Y; lia |]). apply Forall_nil.
Qed.
End Zd2.
#[using="Type"] Lemma cdealloc_spec : forall RNG {R} (k : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c P lo : Z) (sj chunks : list word) (sta : word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in let CA := acache_addr L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let cnt := c_count r in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CDEALLOC_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 c -> a3 = Z_to_bv 64 P ->
  m3_cells L m ->
  (forall j, 1 <= j <= 31 -> arec_hdr L m j (c_count (get_cls st j)) (max_count st j) (if a_cinit st then size_of_class j else 0)) ->
  u32arr asegs m (CA + 16) chunks -> length chunks = 16%nat -> Forall (fun w : word => bv_unsigned w < 2^31) (firstn (Z.to_nat cnt) chunks) ->
  rw_cells asegs m (al_t L + 2784) [C8 sta] ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  junk_at m (RI + 72) 56 ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  junk_at m (FA + 4 * nf) (mfa - 4 * nf) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  (forall j, 1 <= j <= 31 -> 0 <= c_count (get_cls st j) <= max_count st j) ->
  0 <= nf -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 4 * (nf + max_cached c / 2) <= K_FREEARR_MAX ->
  aregion L c <= P -> P < aregion L c + K_REGION ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall stX RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      cdealloc_ret L RNG sp st c P lo chunks m stX RNG' m' ->
      implS asegs RNG' (aembed ATOP (k stX)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (cache_dealloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 cdealloc_entry) fc None m (seg_rom asegs)).
Proof. exact cdealloc_spec__body. Qed.
End CANSEC2.
End TwB.
End F_acdealloc.
