(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymExec3B AsanAcct AsanPlanCore AsanPlan AsanPlanSound AsanInit AsHSTab AsMainVM. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsMainState.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AsMainSyms.
Import ListNotations. Import AX2. Import AX2S. Import AX2B. Import APC. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition K_TID : nat := 44.   (* [comment removed for export] *)
Definition K_B04 : nat := 94.   Definition K_B05 : nat := 223.  Definition K_B06 : nat := 224.  Definition K_R06 : nat := 225.
Definition K_B08 : nat := 242.  Definition K_B09 : nat := 243.  Definition K_B10 : nat := 244.  Definition K_B11 : nat := 261.
Definition K_B12 : nat := 326.  Definition K_B13 : nat := 327.  Definition K_B16 : nat := 392.
Definition K_META : nat := 409.
Definition K_B20 (g : bool) : nat := if g then 409 else 410.
(* [comment removed for export] *)
Definition K_B21 (g : bool) : nat := 455.
Definition K_B22 (g : bool) : nat := 456.
Definition K_B23 (g : bool) : nat := 457.
Definition K_B24 (g : bool) : nat := 465.
(* [comment removed for export] *)
Definition K_A1 : nat := 458.   Definition K_A2 : nat := 460.   Definition K_A3 : nat := 462.
Definition K_G1 : nat := 459.   Definition K_G2 : nat := 461.   Definition K_G3 : nat := 463.   Definition K_G4 : nat := 464.
Definition K_X (g : bool) : nat := 466.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hole_granted (h : nat) : bool := match h with 0 | 1 | 4 => true | _ => false end%nat.
(* [comment removed for export] *)
Definition hole_class (h : nat) : nat := match h with 0 | 1 | 2 | 3 => 0 | _ => 1 end%nat.

(* [comment removed for export] *)
Definition vE (E : env) (k : nat) : Z := bv_unsigned (ev E k).
Lemma uE_var : forall E k, uE E (EVar k) = vE E k.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition Xof (g : bool) (E : env) : pm_syms :=
  PMS (vE E K_TID) g
      (4096 * vE E K_B04) (4096 * vE E K_B05) (4096 * vE E K_B06) (4096 * vE E K_B08) (4096 * vE E K_B09) (4096 * vE E K_B10)
      (4096 * vE E K_B11) (4096 * vE E K_B12) (4096 * vE E K_B13) (4096 * vE E K_B16) (4096 * vE E (K_B20 g)) (4096 * vE E (K_B21 g))
      (4096 * vE E (K_B22 g)) (4096 * vE E (K_B23 g)) (4096 * vE E (K_B24 g))
      (if g then 0 else 4096 * vE E K_META)
      (4096 * vE E K_A1) (4096 * vE E K_A2) (4096 * vE E K_A3)
      (4096 * vE E K_G1) (4096 * vE E K_G2) (4096 * vE E K_G3) (4096 * vE E K_G4).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Generic.
  Variables (sp0 brk0 : word) (rdraw : EntryDraw) (argv envp : list (list byte)) (uid hw : word) (fs : Fs.Fs).
  Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis HC : cs_ok ASEGS ASAN_H AsanInit.LIMIT (SINV0 APH sp0 rdraw brk0 argv envp uid hw) (argH0 APH sp0 rdraw argv envp uid hw) fs E ch R FULL model.

  (* [comment removed for export] *)
  Lemma cs_reg_lin : forall r : Z, 0 < r < 32 ->
    getr R (Z_to_bv 5 r) = Z_to_bv 64 (lden E (lin_of (nth (Z.to_nat r) (s_regs (a_ss ch)) (ELit 0)))).
  Proof.
    intros r Hr. rewrite (co_regs _ _ _ _ _ _ _ _ _ _ _ HC (Z_to_bv 5 r)).
    rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E _)). apply eqm_Z_to_bv. apply eqm_sym.
    unfold sr_get, ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by (cbn; lia).
    destruct (bv_eqb (Z_to_bv 5 r) 0) eqn:B.
    - apply bv_eqb_eq in B. apply (f_equal bv_unsigned) in B. rewrite Z_to_bv_unsigned in B.
      unfold bv_wrap, bv_modulus in B. rewrite Z.mod_small in B by (cbn; lia). exfalso. clear -B Hr. vm_compute in B. lia.
    - apply lin_of_sound.
  Qed.

  (* [comment removed for export] *)
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Lemma cs_v0 : vE E 0 = bv_unsigned sp0 / 32768.
  Proof.
    destruct (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as [HE _]. unfold vE. rewrite (HE 0%nat) by (unfold NX0; lia).
    cbn [ev E0 vals0 nth]. pose proof (u64_range sp0). apply u_of_Z. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  Qed.
  Lemma cs_v6 : vE E 6 = (bv_unsigned sp0 mod 32768) / 4096.
  Proof.
    destruct (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as [HE _]. unfold vE. rewrite (HE 6%nat) by (unfold NX0; lia).
    cbn [ev E0 vals0 nth]. pose proof (Z.mod_pos_bound (bv_unsigned sp0) 32768). apply u_of_Z.
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  Qed.
  Lemma cs_v10 : vE E 10 = (bv_unsigned sp0 mod 4096) / 16.
  Proof.
    destruct (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as [HE _]. unfold vE. rewrite (HE 10%nat) by (unfold NX0; lia).
    cbn [ev E0 vals0 nth]. pose proof (Z.mod_pos_bound (bv_unsigned sp0) 4096). apply u_of_Z.
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  Qed.
  Lemma cs_v1 : vE E 1 = Z.of_nat (length argv).
  Proof.
    destruct (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as [HE _]. unfold vE. rewrite (HE 1%nat) by (unfold NX0; lia).
    cbn [ev E0 vals0 nth]. apply u_of_Z. destruct Hva as [? _]. lia.
  Qed.
  Lemma cs_v2 : vE E 2 = Z.of_nat (length envp).
  Proof.
    destruct (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as [HE _]. unfold vE. rewrite (HE 2%nat) by (unfold NX0; lia).
    cbn [ev E0 vals0 nth]. apply u_of_Z. destruct Hve as [? _]. lia.
  Qed.
  Lemma cs_v5 : vE E 5 = bv_unsigned brk0 / 4096.
  Proof.
    destruct (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as [HE _]. unfold vE. rewrite (HE 5%nat) by (unfold NX0; lia).
    cbn [ev E0 vals0 nth]. pose proof (u64_range brk0). apply u_of_Z. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  Qed.
  Lemma cs_v8 : vE E 8 = bv_unsigned uid.
  Proof.
    destruct (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as [HE _]. unfold vE. rewrite (HE 8%nat) by (unfold NX0; lia). reflexivity.
  Qed.
  Lemma cs_v9 : vE E 9 = bv_unsigned hw.
  Proof.
    destruct (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as [HE _]. unfold vE. rewrite (HE 9%nat) by (unfold NX0; lia). reflexivity.
  Qed.
  (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp0.
  Lemma cs_sp0 : 32768 * vE E 0 + 4096 * vE E 6 + 16 * vE E 10 = bv_unsigned sp0.
  Proof.
    rewrite cs_v0, cs_v6, cs_v10. destruct Hsp as (_ & _ & Hal).
    pose proof (Z.div_mod (bv_unsigned sp0) 32768 ltac:(lia)). pose proof (Z.div_mod (bv_unsigned sp0 mod 32768) 4096 ltac:(lia)).
    pose proof (Z.div_mod (bv_unsigned sp0 mod 4096) 16 ltac:(lia)).
    assert ((bv_unsigned sp0 mod 4096) mod 16 = 0).
    { rewrite <- (Znumtheory.Zmod_div_mod 16 4096 (bv_unsigned sp0)); [exact Hal | lia | lia | exists 256; reflexivity]. }
    assert ((bv_unsigned sp0 mod 32768) mod 4096 = bv_unsigned sp0 mod 4096).
    { rewrite <- (Znumtheory.Zmod_div_mod 4096 32768 (bv_unsigned sp0)); [reflexivity | lia | lia | exists 8; reflexivity]. }
    lia.
  Qed.
  (* [comment removed for export] *)
  Lemma cs_sp0_mod : 16 * vE E 10 = bv_unsigned sp0 mod 4096.
  Proof.
    rewrite cs_v10. destruct Hsp as (_ & _ & Hal). pose proof (Z.div_mod (bv_unsigned sp0 mod 4096) 16 ltac:(lia)).
    assert ((bv_unsigned sp0 mod 4096) mod 16 = 0).
    { rewrite <- (Znumtheory.Zmod_div_mod 16 4096 (bv_unsigned sp0)); [exact Hal | lia | lia | exists 256; reflexivity]. }
    lia.
  Qed.
  Lemma cs_brk0 : 4096 * vE E 5 = bv_unsigned brk0.
  Proof.
    rewrite cs_v5. destruct Hbrk as (_ & _ & Hal). unfold page_size in Hal.
    pose proof (Z.div_mod (bv_unsigned brk0) 4096 ltac:(lia)). lia.
  Qed.

  #[local] Notation MR := (Mr ASAN_H (argH0 APH sp0 rdraw argv envp uid hw) E ch model FULL).

  (* [comment removed for export] *)
  Lemma cs_fact : forall K, existsb (kentry_eqb K) (kn ch) = true -> kentry_ok ASEGS E MR K.
  Proof.
    intros K H. apply existsb_exists in H as [K' [Hin Heq]]. apply kentry_eqb_eq in Heq. subst K'.
    exact (proj1 (Forall_forall _ _) (co_know _ _ _ _ _ _ _ _ _ _ _ HC) K Hin).
  Qed.
  (* [comment removed for export] *)
  Lemma cs_range : forall e lo hi, existsb (kentry_eqb (KRange e lo hi)) (kn ch) = true -> lo <= uE E e <= hi.
  Proof. intros e lo hi H. pose proof (cs_fact _ H) as K. cbn [kentry_ok] in K. unfold uE. lia. Qed.
  (* [comment removed for export] *)
  Lemma cs_disj : forall b1 o1 n1 b2 o2 n2, existsb (kentry_eqb (KDisj (SA b1 o1) n1 (SA b2 o2) n2)) (kn ch) = true ->
    uE E b1 + o1 + uE E n1 <= uE E b2 + o2 \/ uE E b2 + o2 + uE E n2 <= uE E b1 + o1.
  Proof. intros b1 o1 n1 b2 o2 n2 H. pose proof (cs_fact _ H) as K. cbn [kentry_ok estart a_base a_off] in K. unfold uE. exact K. Qed.

  (* [comment removed for export] *)
  Lemma maps_match_nofog : forall ms l, no_fog ms = true -> maps_match E ms l -> l = map (amap_den E) ms.
  Proof.
    induction ms as [|m ms IH]; intros l Hnf H; cbn [maps_match] in H.
    - exact H.
    - cbn [no_fog forallb] in Hnf. apply andb_prop in Hnf as [H1 H2]. apply negb_true_iff in H1. rewrite H1 in H.
      destruct H as [l' [-> H]]. cbn [map]. f_equal. exact (IH l' H2 H).
  Qed.
  Definition lin_iv (E : env) (m : amap) : word * word :=
    (Z_to_bv 64 (lden E (lin_of (am_base m))), Z_to_bv 64 (lden E (lin_of (am_len m)))).
  Lemma amap_den_lin : forall m, amap_den E m = lin_iv E m.
  Proof.
    intros m. unfold amap_den, lin_iv. f_equal.
    - rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E _)). apply eqm_Z_to_bv. apply eqm_sym. apply lin_of_sound.
    - rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E _)). apply eqm_Z_to_bv. apply eqm_sym. apply lin_of_sound.
  Qed.
  Lemma cs_maps : no_fog (a_maps ch) = true -> vm_maps (m_vmmaps model) = map (lin_iv E) (a_maps ch).
  Proof.
    intros Hnf. rewrite (maps_match_nofog _ _ Hnf (co_maps _ _ _ _ _ _ _ _ _ _ _ HC)).
    apply map_ext. intros m. apply amap_den_lin.
  Qed.

  (* [comment removed for export] *)
  Lemma cs_noacc_lazy : forall N L, cs_ledgers ch = Some (N, L) ->
    vm_noaccess (m_vmmaps model) = sivs_den E N /\ m_vm_lazy model = sivs_den E L.
  Proof. intros N L H. destruct (cs_ledgers_sound _ _ _ _ _ _ _ _ _ _ _ N L HC H) as (A & B & _). split; assumption. Qed.

  (* [comment removed for export] *)
  Lemma cs_brk : vm_brk (m_vmmaps model) = Z_to_bv 64 (lden E (lin_of (a_brk ch))).
  Proof.
    rewrite (co_brk _ _ _ _ _ _ _ _ _ _ _ HC). rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E _)).
    apply eqm_Z_to_bv. apply eqm_sym. apply lin_of_sound.
  Qed.
  Lemma cs_fds : a_fd ch = FdStd -> m_fds model = fds_std.
  Proof. intros H. pose proof (co_fds _ _ _ _ _ _ _ _ _ _ _ HC) as F. rewrite H in F. exact F. Qed.
  Lemma cs_fs : m_fs model = fs.
  Proof. exact (co_fs _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
  Lemma cs_halted : m_halted model = None.
  Proof. exact (co_halt _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
  Lemma cs_limit : vm_limit (m_vmmaps model) = target_alloc_limit.
  Proof. exact (co_limit _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
  Lemma cs_reserved : vm_reserved (m_vmmaps model) = segments_reserved ASEGS.
  Proof. exact (co_res _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
  Lemma cs_eager : eager_used model <= a_eager ch.
  Proof. exact (co_eager _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
End Generic.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record digest : Type := DG {
  dg_pc : Z; dg_regs : list lin; dg_maps : list (lin * lin * mkind); dg_nofog : bool;
  dg_ledgers : option (list siv * list siv); dg_brk : lin; dg_fd : afd; dg_tidset : bool; dg_eager : Z;
  dg_vis : list (lin * lin); dg_ghost : list (lin * lin); dg_cls : nat; dg_kfacts : bool }.
(* [comment removed for export] *)
Definition has_fact (k : list kentry) (K : kentry) : bool := existsb (kentry_eqb K) k.
Definition e_rel06 : expr :=
  EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar K_R06)) (EAlu Instr.ALU_AND (EMd Instr.M_MUL (ELit 4096) (EVar K_B06)) (ELit 65535)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qlo (cls : nat) : Z := match cls with 0%nat => 0 | _ => 0 end.
Definition qhi (cls : nat) : Z := match cls with 0%nat => 7 | _ => 7 end.
Definition wlo (cls : nat) : Z := match cls with 0%nat => 0 | _ => 11 end.
Definition whi (cls : nat) : Z := match cls with 0%nat => 10 | _ => 255 end.
Definition kn_cls (k : list kentry) : nat :=
  if has_fact k (KRange (EVar 10) 0 10) then 0%nat else 1%nat.
Definition kn_facts (k : list kentry) (cls : nat) : bool :=
  has_fact k (KRange (EVar K_R06) 0 15) && has_fact k (KRange (EVar K_B06) 4295491576 34326181871) && has_fact k (KRange e_rel06 0 0)
  && has_fact k (KRange (EVar 6) (qlo cls) (qhi cls)) && has_fact k (KRange (EVar 10) (wlo cls) (whi cls))
  && has_fact k (KRange (EVar K_TID) 1 4194303)
  && has_fact k (KRange (EVar 0) 4294901760 4294967295).
Definition hs_digest (ch : acs) : digest :=
  DG (pc ch) (map lin_of (s_regs (a_ss ch)))
     (map (fun m => (lin_of (am_base m), lin_of (am_len m), am_kind m)) (a_maps ch)) (no_fog (a_maps ch))
     (cs_ledgers ch) (lin_of (a_brk ch)) (a_fd ch) (a_tidset ch) (a_eager ch)
     (map (fun p => (lin_of (fst p), lin_of (snd p))) (a_vis ch)) (map (fun p => (lin_of (fst p), lin_of (snd p))) (a_ghost ch))
     (kn_cls (kn ch)) (kn_facts (kn ch) (kn_cls (kn ch))).

Definition pg (k : nat) : lin := (0, [(4096, EVar k)]).            (* [comment removed for export] *)
Definition pgo (c : Z) (k : nat) : lin := (c, [(4096, EVar k)]).   (* [comment removed for export] *)
Definition lRI : lin := (137439019008, [(4096, EVar K_B06); (-4096, EVar K_R06)]).      (* [comment removed for export] *)
Definition lRI' : lin := (137439023104, [(4096, EVar K_B06); (-4096, EVar K_R06)]).    (* [comment removed for export] *)
Definition lSP (c : Z) : lin := (c, [(32768, EVar 0); (4096, EVar 6); (16, EVar 10)]).               (* [comment removed for export] *)
Definition lENVP : lin := (16, [(32768, EVar 0); (8, EVar 1); (4096, EVar 6); (16, EVar 10)]).        (* [comment removed for export] *)
Definition lv (k : nat) : lin := (0, [(1, EVar k)]).

Definition lvx (g : bool) (i : nat) : lin := lv (K_X g + i).   (* [comment removed for export] *)
Definition DG_regs (g : bool) : list lin :=
  [(0, []); (5627468, []); lSP (-48); (67584, []); (12459152, []); lvx g 0; lvx g 1; lvx g 2;
   lSP 8; lv 1; lv 1; lSP 8; lENVP; lvx g 3; lvx g 4; lvx g 5; lvx g 6; lvx g 7; (2026780, []); lENVP;
   (0, []); (0, []); (0, []); (0, []); (0, []); (0, []); (0, []); (0, []); lvx g 8; lvx g 9; lvx g 10; lvx g 11].
(* [comment removed for export] *)
Definition lMETA (g : bool) : lin := if g then pg 5 else pg K_META.
Definition DG_maps (g : bool) : list (lin * lin * mkind) :=
  [(pg (K_B24 g), (65536, []), KRW); (pg K_A3, (65536, []), KRW); (pg K_A2, (65536, []), KRW); (pg K_A1, (65536, []), KRW);
   (pg (K_B23 g), (4096, []), KRW); (pg (K_B22 g), (8388608, []), KRWLAZY); (pg (K_B21 g), (1048576, []), KRW);
   (pg (K_B20 g), (4096, []), KRW); (lMETA g, (8192, []), KRW); (pg K_B16, (11571200, []), KRW); (pg K_B12, (4096, []), KRW);
   (pg K_B11, (4096, []), KRW); (pg K_B10, (65536, []), KRW); (pg K_B09, (4096, []), KRW); (pg K_B08, (8388608, []), KNONELAZY);
   (pg K_B06, (137439023104, []), KRW); (pg K_B05, (3727360, []), KRW); (pg K_B04, (65536, []), KRW);
   ((2201439137792, []), (15392894357504, []), KRWLAZY); ((2415882240, []), (2199023255552, []), KNONELAZY); ((2147446784, []), (268435456, []), KRWLAZY)].
Definition DG_noacc (g : bool) : list siv :=
  [(lMETA g, lcat (lconst 4096) (lMETA g)); (pg K_B08, pgo 8388608 K_B08); (pg K_B06, lRI); (lRI', pgo 137439023104 K_B06); ((2415882240, []), (2201439137792, []))].
(* [comment removed for export] *)
Definition DG_lazy (g : bool) : list siv :=
  [(pg (K_B22 g), pgo 8388608 (K_B22 g)); (pg K_B08, pgo 8388608 K_B08); (pg K_B06, lRI); (lRI', pgo 137439023104 K_B06);
   ((2201439137792, []), (17594333495296, [])); ((2415882240, []), (2201439137792, [])); ((2147446784, []), (2415882240, []))].
Definition DG_vis (g : bool) : list (lin * lin) :=
  [(pg (K_B24 g), (65536, [])); (pg K_A3, (65536, [])); (pg K_A2, (65536, [])); (pg K_A1, (65536, []));
   (pg (K_B23 g), (4096, [])); (pg (K_B22 g), (8388608, [])); (pg (K_B21 g), (1048576, []));
   (pg (K_B20 g), (4096, [])); ((if g then pg 5 else pgo 4096 K_META), (if g then (8192, []) else (4096, []))); (pg K_B16, (11571200, [])); (pg K_B12, (4096, []));
   (pg K_B11, (4096, [])); (pg K_B10, (65536, [])); (pg K_B09, (4096, [])); (lRI, (4096, [])); (pg K_B05, (3727360, []));
   (pg K_B04, (65536, [])); ((65536, []), (12533760, [])); ((-8388608, [(32768, EVar 0); (4096, EVar 6)]), (140737496743936, [(-32768, EVar 0); (-4096, EVar 6)]))].
(* [comment removed for export] *)
Definition DG_ghost : list (lin * lin) :=
  [(pg K_G4, (32768, [])); (pg K_G3, (16384, [])); (pg K_G2, (8192, [])); (pg K_G1, (4096, [])); (pg K_B13, (4096, []))].
Definition DGX (g : bool) (cls : nat) : digest :=
  DG 2026780 (DG_regs g) (DG_maps g) true (Some (DG_noacc g, DG_lazy g)) (if g then pgo 8192 5 else pg 5) FdStd true
     (if g then 16838656 else 16834560) (DG_vis g) DG_ghost cls true.

Lemma HS_digest : forall h ch, HSF_asan h = Some ch -> hs_digest ch = DGX (hole_granted h) (hole_class h).
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSF_asan_table fold_right fst snd] in Hh.
  do 6 (destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|]).
  destruct Hh.
Qed.

Lemma hole_class_le : forall h ch, HSF_asan h = Some ch -> (hole_class h <= 1)%nat.
Proof. intros h ch H. unfold hole_class. destruct h as [|[|[|[|]]]]; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zz2ww (l : list (Z * Z)) : list (word * word) := map (fun p => (Z_to_bv 64 (fst p), Z_to_bv 64 (snd p))) l.

Section LedgersZ.
  Variables (sp0z brk0z : Z) (X : pm_syms).
  Let G : Z := pm_meta_map brk0z X.
  Let RI : Z := pm_region_info X.
  Let PEND : Z := ps_b06 X + 0x2000011000.
  (* [comment removed for export] *)
  Definition PM_REM : list (Z * Z) := if RI + 0x1000 <? PEND then [(RI + 0x1000, PEND - (RI + 0x1000))] else [].
  Definition PM_MAPS : list (Z * Z) :=
    [((ps_b24 X), 0x10000); ((ps_a3 X), 0x10000); ((ps_a2 X), 0x10000); ((ps_a1 X), 0x10000);
     ((ps_b23 X), 0x1000); ((ps_b22 X), 0x800000); ((ps_b21 X), 0x100000); ((ps_b20 X), 0x1000);
     (G, 0x2000); ((ps_b16 X), 0xb09000); ((ps_b12 X), 0x1000); ((ps_b11 X), 0x1000); ((ps_b10 X), 0x10000); ((ps_b09 X), 0x1000);
     ((ps_b08 X), 0x800000); ((ps_b06 X), 0x2000011000); ((ps_b05 X), 0x38e000); ((ps_b04 X), 0x10000);
     (0x2008fff7000, 0xdfff0001000); (0x8fff7000, 0x20000000000); (0x7fff7000, 0x10000000)].
  Definition PM_NOACC : list (Z * Z) :=
    [(G, 0x1000); ((ps_b08 X), 0x800000); ((ps_b06 X), RI - (ps_b06 X))] ++ PM_REM ++ [(0x8fff7000, 0x20000000000)].
End LedgersZ.
(* [comment removed for export] *)
Definition PM_LAZY (sp0z : Z) (X : pm_syms) : list (Z * Z) :=
  [((ps_b22 X), 0x800000); ((ps_b08 X), 0x800000); ((ps_b06 X), pm_region_info X - (ps_b06 X))]
  ++ PM_REM X ++
  [(0x2008fff7000, 0xdfff0001000); (0x8fff7000, 0x20000000000); (0x7fff7000, 0x10000000)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac elim_div x d :=
  let q := fresh "q" in let r := fresh "rm" in
  pose proof (Z.div_mod x d ltac:(lia)); pose proof (Z.mod_pos_bound x d ltac:(lia));
  set (q := x / d) in *; set (r := x mod d) in *; clearbody q r.

(* [comment removed for export] *)
Lemma stack_top_cls : forall sp0z v0 q w cls,
  sp0z = 32768 * v0 + 4096 * q + 16 * w -> qlo cls <= q <= qhi cls -> wlo cls <= w <= whi cls -> (cls <= 1)%nat ->
  pm_stack_top sp0z = 32768 * v0 + 4096 * q + (if Z.leb 11 w then 4096 else 0).
Proof.
  intros sp0z v0 q w cls Hsp Hq Hw Hc. unfold pm_stack_top, AsMainSyms.page_up. subst sp0z.
  assert (Hcls : cls = 0%nat \/ cls = 1%nat) by lia.
  destruct Hcls as [-> | ->]; cbn [qlo qhi wlo whi] in *;
    (destruct (Z.leb_spec 11 w); [|]; elim_div (32768 * v0 + 4096 * q + 16 * w - 160 + 4095) 4096; try nia).
Qed.

(* [comment removed for export] *)
Lemma RI_lin : forall X b06 r, ps_b06 X = b06 -> b06 mod 65536 = 4096 * r ->
  pm_region_info X = 137439019008 + b06 - 4096 * r.
Proof.
  intros X b06 r H1 H2. unfold pm_region_info, pm_space_beg. rewrite H1.
  pose proof (Z.div_mod b06 65536 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma rel06_sound : forall E, uE E e_rel06 = 0 -> 0 <= vE E K_R06 <= 15 -> 0 <= vE E K_B06 <= 2^50 ->
  (4096 * vE E K_B06) mod 65536 = 4096 * vE E K_R06.
Proof.
  intros E H HR HB. unfold uE, e_rel06 in H. cbn [edenot] in H.
  rewrite u_add64 in H. rewrite u_mul64 in H. rewrite u_and64 in H. rewrite u_mul64 in H. rewrite !u_lit64a in H.
  change (bv_unsigned (ev E K_R06)) with (vE E K_R06) in H. change (bv_unsigned (ev E K_B06)) with (vE E K_B06) in H.
  replace (-4096 mod 2 ^ 64) with (2^64 - 4096) in H by reflexivity.
  replace (4096 mod 2 ^ 64) with 4096 in H by reflexivity. replace (65535 mod 2 ^ 64) with (Z.ones 16) in H by reflexivity.
  rewrite Z.land_ones in H by lia.
  rewrite (Z.mod_small (4096 * vE E K_B06) (2 ^ 64)) in H by lia.
  elim_div ((2 ^ 64 - 4096) * vE E K_R06) (2 ^ 64).
  change (2 ^ 16) with 65536 in H.
  elim_div (4096 * vE E K_B06) 65536.
  elim_div (rm + rm0) (2^64).
  lia.
Qed.

(* [comment removed for export] *)
Ltac zzcrush := repeat (lazymatch goal with
  | |- @eq Z _ _ => unfold lMETA; unfold lcat, lconst; unfold pg, pgo, lRI, lRI'; unfold lden; cbn [fst snd tden app]; rewrite ?uE_var; lia
  | |- _ => first [reflexivity | progress f_equal] end).

Section Dens.
  Variable E : env.
  Let b06 := 4096 * vE E K_B06.
  Let r06 := vE E K_R06.

  Lemma DG_noacc_den : forall g brk0z,
    0 <= r06 <= 15 -> b06 mod 65536 = 4096 * r06 -> (g = true -> 4096 * vE E 5 = brk0z) ->
    sivs_den E (DG_noacc g) = zz2ww (PM_NOACC brk0z (Xof g E)).
  Proof.
    intros g brk0z HR REL BRK. unfold PM_NOACC, PM_REM. rewrite (RI_lin (Xof g E) b06 r06 eq_refl REL).
    cbn [ps_b06 ps_b08 Xof pm_meta_map ps_granted ps_b19r].
    unfold DG_noacc. cbn [sivs_den].
    rewrite (siv_den_full E (lMETA g, _)) by (destruct g; unfold lMETA, pg, lcat, lconst, lden; cbn [fst snd tden app]; lia).
    rewrite (siv_den_full E (pg K_B08, _)) by (unfold pg, pgo, lden; cbn [fst snd tden app]; lia).
    rewrite (siv_den_full E (pg K_B06, _)) by (unfold pg, lRI, lden; cbn [fst snd tden app]; rewrite ?uE_var; subst b06 r06; lia).
    rewrite (siv_den_full E ((2415882240, []), _)) by (unfold lden; cbn [fst snd tden app]; lia).
    unfold zz2ww. rewrite !map_app.
    assert (H4 : siv_den E (lRI', pgo 137439023104 K_B06) =
                 map (fun p : Z * Z => (Z_to_bv 64 (fst p), Z_to_bv 64 (snd p)))
                     (if 137439019008 + b06 - 4096 * r06 + 4096 <? b06 + 137439023104
                      then [(137439019008 + b06 - 4096 * r06 + 4096, b06 + 137439023104 - (137439019008 + b06 - 4096 * r06 + 4096))] else [])).
    { destruct (Z.eq_dec r06 0) as [Z0|NZ].
      - rewrite (siv_den_empty E) by (unfold lRI', pgo, lden; cbn [fst snd tden]; rewrite ?uE_var; subst b06 r06; lia).
        destruct (_ <? _) eqn:C; [apply Z.ltb_lt in C; lia | reflexivity].
      - rewrite (siv_den_full E) by (unfold lRI', pgo, lden; cbn [fst snd tden]; rewrite ?uE_var; subst b06 r06; lia).
        destruct (_ <? _) eqn:C; [| apply Z.ltb_ge in C; lia]. cbn [map fst snd]. subst b06 r06. zzcrush. }
    rewrite H4. cbn [map fst snd app]. unfold pm_meta_map, Xof; cbn [ps_granted ps_b19r].
    destruct g; [specialize (BRK eq_refl)|]; subst b06 r06; zzcrush.
  Qed.

  Lemma DG_lazy_den : forall g sp0z,
    0 <= r06 <= 15 -> b06 mod 65536 = 4096 * r06 ->
    sivs_den E (DG_lazy g) = zz2ww (PM_LAZY sp0z (Xof g E)).
  Proof.
    intros g sp0z HR REL. unfold PM_LAZY, PM_REM. rewrite (RI_lin (Xof g E) b06 r06 eq_refl REL).
    cbn [ps_b06 ps_b08 ps_b22 Xof].
    unfold DG_lazy. cbn [sivs_den].
    rewrite (siv_den_full E (pg (K_B22 g), _)) by (unfold pg, pgo, lden; cbn [fst snd tden app]; lia).
    rewrite (siv_den_full E (pg K_B08, _)) by (unfold pg, pgo, lden; cbn [fst snd tden app]; lia).
    rewrite (siv_den_full E (pg K_B06, _)) by (unfold pg, lRI, lden; cbn [fst snd tden app]; rewrite ?uE_var; subst b06 r06; lia).
    rewrite (siv_den_full E ((2415882240, []), _)) by (unfold lden; cbn [fst snd tden app]; lia).
    rewrite (siv_den_full E ((2201439137792, []), _)) by (unfold lden; cbn [fst snd tden app]; lia).
    rewrite (siv_den_full E ((2147446784, []), _)) by (unfold lden; cbn [fst snd tden app]; lia).
    unfold zz2ww. rewrite !map_app.
    assert (H4 : siv_den E (lRI', pgo 137439023104 K_B06) =
                 map (fun p : Z * Z => (Z_to_bv 64 (fst p), Z_to_bv 64 (snd p)))
                     (if 137439019008 + b06 - 4096 * r06 + 4096 <? b06 + 137439023104
                      then [(137439019008 + b06 - 4096 * r06 + 4096, b06 + 137439023104 - (137439019008 + b06 - 4096 * r06 + 4096))] else [])).
    { destruct (Z.eq_dec r06 0) as [Z0|NZ].
      - rewrite (siv_den_empty E) by (unfold lRI', pgo, lden; cbn [fst snd tden]; rewrite ?uE_var; subst b06 r06; lia).
        destruct (_ <? _) eqn:C; [apply Z.ltb_lt in C; lia | reflexivity].
      - rewrite (siv_den_full E) by (unfold lRI', pgo, lden; cbn [fst snd tden]; rewrite ?uE_var; subst b06 r06; lia).
        destruct (_ <? _) eqn:C; [| apply Z.ltb_ge in C; lia]. cbn [map fst snd]. subst b06 r06. zzcrush. }
    rewrite H4. clear H4. cbn [map fst snd app]. subst b06 r06. zzcrush.
  Qed.
End Dens.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section PMDef.
  Variables (sp0 brk0 mbase : word) (inp : ProcInput).
  Let sp0z := bv_unsigned sp0. Let brk0z := bv_unsigned brk0.
  Let argc := Z.of_nat (length (in_argv inp)).

  Record PM (X : pm_syms) (c : config) : Prop := MkPM {
    (* [comment removed for export] *)
    pm_pc    : ms_pc (cfg_ms c) = Z_to_bv 64 A_MAIN;
    pm_svc   : ms_svc_pending (cfg_ms c) = None;
    pm_resv  : ms_resv (cfg_ms c) = None;
    pm_fregs : ms_fregs (cfg_ms c) = bvmap_empty;
    pm_fcsr  : ms_fcsr (cfg_ms c) = Z_to_bv 32 0;
    pm_rom   : ms_rom (cfg_ms c) = seg_rom ASEGS;
    pm_regs  : let R := ms_regs (cfg_ms c) in
               getr R 1 = Z_to_bv 64 0x55de4c /\ getr R 2 = Z_to_bv 64 (sp0z - 0x30) /\ getr R 3 = Z_to_bv 64 0x10800 /\
               getr R 4 = Z_to_bv 64 0xbe1c90 /\ getr R 8 = Z_to_bv 64 (sp0z + 8) /\ getr R 9 = Z_to_bv 64 argc /\
               getr R 10 = Z_to_bv 64 argc /\ getr R 11 = Z_to_bv 64 (sp0z + 8) /\ getr R 12 = Z_to_bv 64 (pm_envp sp0z argc) /\
               getr R 18 = Z_to_bv 64 A_MAIN /\ getr R 19 = Z_to_bv 64 (pm_envp sp0z argc) /\
               (forall r : Z, 20 <= r <= 27 -> getr R (Z_to_bv 5 r) = Z_to_bv 64 0);
    (* [comment removed for export] *)
    pm_halted : m_halted (cfg_model c) = None;
    pm_fds    : m_fds (cfg_model c) = fds_std;
    pm_fs     : m_fs (cfg_model c) = in_fs inp;
    pm_limit  : vm_limit (m_vmmaps (cfg_model c)) = target_alloc_limit;
    pm_reserved : vm_reserved (m_vmmaps (cfg_model c)) = segments_reserved ASEGS;
    pm_topz   : TOP (cfg_model c) = pm_top sp0z;
    pm_brk    : vm_brk (m_vmmaps (cfg_model c)) = Z_to_bv 64 (if ps_granted X then brk0z + 0x2000 else brk0z);
    pm_eager  : eager_used (cfg_model c) <= 16838656;
    pm_maps   : vm_maps (m_vmmaps (cfg_model c)) = zz2ww (PM_MAPS brk0z X);
    pm_noacc  : vm_noaccess (m_vmmaps (cfg_model c)) = zz2ww (PM_NOACC brk0z X);
    pm_lazy   : m_vm_lazy (cfg_model c) = zz2ww (PM_LAZY sp0z X)
  }.
End PMDef.

Section PMOpen.
  (* [comment removed for export] *)
  Variables (sp0 brk0 : word) (rdraw : EntryDraw) (inp : ProcInput).
  Variables (h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis Vsp : valid_sp sp0.
  Hypothesis Vbrk : valid_brk ASEGS brk0.
  Hypothesis Vav : valid_argv (in_argv inp).
  Hypothesis Vev : valid_envp (in_envp inp).
  Hypothesis Hh : HSF_asan h = Some ch.
  Hypothesis HC : cs_ok ASEGS ASAN_H AsanInit.LIMIT (SINV0 APH sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
                        (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model.

  (* [comment removed for export] *)
  Lemma open_facts :
    let g := hole_granted h in let cls := hole_class h in
    hs_digest ch = DGX g cls /\ (cls <= 1)%nat
    /\ 0 <= vE E K_R06 <= 15 /\ (4096 * vE E K_B06) mod 65536 = 4096 * vE E K_R06 /\ 4295491576 <= vE E K_B06 <= 34326181871
    /\ 4294901760 <= vE E 0 <= 4294967295 /\ 1 <= vE E K_TID <= 4194303
    /\ qlo cls <= vE E 6 <= qhi cls /\ wlo cls <= vE E 10 <= whi cls
    /\ 32768 * vE E 0 + 4096 * vE E 6 + 16 * vE E 10 = bv_unsigned sp0 /\ 16 * vE E 10 = bv_unsigned sp0 mod 4096
    /\ 4096 * vE E 5 = bv_unsigned brk0 /\ vE E 1 = Z.of_nat (length (in_argv inp)) /\ vE E 2 = Z.of_nat (length (in_envp inp))
    /\ pm_stack_top (bv_unsigned sp0) = 32768 * vE E 0 + 4096 * vE E 6 + (if Z.leb 11 (vE E 10) then 4096 else 0)
    /\ TOP model = bv_unsigned sp0 - 8388608.
  Proof.
    cbv zeta. pose proof (HS_digest h ch Hh) as D.
    set (g := hole_granted h) in D |- *. set (cls := hole_class h) in D |- *.
    pose proof (hole_class_le h ch Hh : (cls <= 1)%nat) as Hcls.
    assert (Dcls : kn_cls (kn ch) = cls) by exact (f_equal dg_cls D).
    assert (Dkf : kn_facts (kn ch) cls = true) by (rewrite <- Dcls at 1; exact (f_equal dg_kfacts D)).
    unfold kn_facts in Dkf.
    apply andb_prop in Dkf as [Dkf K0]. apply andb_prop in Dkf as [Dkf KTID]. apply andb_prop in Dkf as [Dkf K10].
    apply andb_prop in Dkf as [Dkf K6]. apply andb_prop in Dkf as [Dkf KREL]. apply andb_prop in Dkf as [KR06 KB06].
    pose proof (cs_range _ _ _ _ _ _ _ _ _ _ _ _ _ HC _ _ _ KR06) as VR06. rewrite uE_var in VR06.
    pose proof (cs_range _ _ _ _ _ _ _ _ _ _ _ _ _ HC _ _ _ KB06) as VB06. rewrite uE_var in VB06.
    pose proof (cs_range _ _ _ _ _ _ _ _ _ _ _ _ _ HC _ _ _ K6) as V6. rewrite uE_var in V6.
    pose proof (cs_range _ _ _ _ _ _ _ _ _ _ _ _ _ HC _ _ _ K10) as V10. rewrite uE_var in V10.
    pose proof (cs_range _ _ _ _ _ _ _ _ _ _ _ _ _ HC _ _ _ KTID) as VTID. rewrite uE_var in VTID.
    pose proof (cs_range _ _ _ _ _ _ _ _ _ _ _ _ _ HC _ _ _ K0) as V0. rewrite uE_var in V0.
    pose proof (cs_range _ _ _ _ _ _ _ _ _ _ _ _ _ HC _ _ _ KREL) as VREL.
    pose proof (rel06_sound E ltac:(lia) VR06 ltac:(lia)) as REL.
    pose proof (cs_sp0 _ _ _ _ _ _ _ _ _ _ _ _ _ HC Vsp) as SP.
    pose proof (cs_sp0_mod _ _ _ _ _ _ _ _ _ _ _ _ _ HC Vsp) as SPM.
    pose proof (cs_brk0 _ _ _ _ _ _ _ _ _ _ _ _ _ HC Vbrk) as BRK.
    pose proof (cs_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ HC Vav) as V1.
    pose proof (cs_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ HC Vev) as V2.
    pose proof (stack_top_cls (bv_unsigned sp0) (vE E 0) (vE E 6) (vE E 10) cls ltac:(lia) V6 V10 Hcls) as STK.
    assert (TOPm : TOP model = bv_unsigned sp0 - 8388608).
    { rewrite (co_sp0 _ _ _ _ _ _ _ _ _ _ _ HC).
      pose proof (lin_of_sound E e_sp0_early) as LS.
      replace (lin_of e_sp0_early) with (lSP 0) in LS by (vm_compute; reflexivity).
      destruct LS as [qq LS]. unfold lden, lSP in LS; cbn [fst snd tden] in LS. rewrite ?uE_var in LS.
      pose proof (u64_range (edenot E e_sp0_early)). unfold AX2S.uE in LS.
      assert (V610 : 0 <= vE E 6 <= 7 /\ 0 <= vE E 10 <= 255) by (clear -V6 V10 Hcls; destruct cls as [|[|]]; cbn [qlo qhi wlo whi] in V6, V10; lia).
      lia. }
    repeat split; assumption || lia.
  Qed.

  (* [comment removed for export] *)
  Lemma PM_open : PM sp0 brk0 inp (Xof (hole_granted h) E) (cfg_of ASEGS R A_MAIN FULL model).
  Proof.
    pose proof open_facts as OF. cbv zeta in OF.
    destruct OF as (D & Hcls & VR06 & REL & VB06 & V0 & VTID & V6 & V10 & SP & SPM & BRK & V1 & V2 & STK & TOPm).
    set (g := hole_granted h) in D |- *. set (cls := hole_class h) in D, Hcls, V6, V10.
    (* [comment removed for export] *)
    assert (Dregs : map lin_of (s_regs (a_ss ch)) = DG_regs g) by exact (f_equal dg_regs D).
    assert (Dmaps : map (fun m => (lin_of (am_base m), lin_of (am_len m), am_kind m)) (a_maps ch) = DG_maps g) by exact (f_equal dg_maps D).
    assert (Dnofog : no_fog (a_maps ch) = true) by exact (f_equal dg_nofog D).
    assert (Dled : cs_ledgers ch = Some (DG_noacc g, DG_lazy g)) by exact (f_equal dg_ledgers D).
    assert (Dbrk : lin_of (a_brk ch) = (if g then pgo 8192 5 else pg 5)) by exact (f_equal dg_brk D).
    assert (Dfd : a_fd ch = FdStd) by exact (f_equal dg_fd D).
    assert (Deager : a_eager ch = (if g then 16838656 else 16834560)) by exact (f_equal dg_eager D).
    split.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - (* [comment removed for export] *)
      cbn [cfg_ms cfg_of mkst ms_regs].
      assert (RG : forall n : nat, (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = Z_to_bv 64 (lden E (nth n (DG_regs g) (0, [])))).
      { intros n Hn. rewrite (cs_reg_lin _ _ _ _ _ _ _ _ _ _ _ _ _ HC (Z.of_nat n) ltac:(lia)). rewrite <- Dregs, Nat2Z.id.
        change (0, []) with (lin_of (ELit 0)). rewrite map_nth. reflexivity. }
      Ltac reg1 RG SP V1 n := etransitivity; [exact (RG n ltac:(lia))|]; cbn [nth DG_regs]; unfold lSP, lENVP, lv, lvx; apply eqm_Z_to_bv; exists 0;
                              unfold lden, pm_envp; cbn [fst snd tden]; rewrite ?uE_var, <- ?SP, <- ?V1; lia.
      split; [reg1 RG SP V1 1%nat|]. split; [reg1 RG SP V1 2%nat|]. split; [reg1 RG SP V1 3%nat|]. split; [reg1 RG SP V1 4%nat|].
      split; [reg1 RG SP V1 8%nat|]. split; [reg1 RG SP V1 9%nat|]. split; [reg1 RG SP V1 10%nat|]. split; [reg1 RG SP V1 11%nat|].
      split; [reg1 RG SP V1 12%nat|]. split; [unfold A_MAIN; reg1 RG SP V1 18%nat|]. split; [reg1 RG SP V1 19%nat|].
      intros r Hr.
      assert (Hr2 : r = Z.of_nat 20 \/ r = Z.of_nat 21 \/ r = Z.of_nat 22 \/ r = Z.of_nat 23 \/ r = Z.of_nat 24 \/ r = Z.of_nat 25
                    \/ r = Z.of_nat 26 \/ r = Z.of_nat 27) by lia.
      destruct Hr2 as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]; (rewrite RG; [destruct g; reflexivity | lia]).
    - exact (cs_halted _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
    - exact (cs_fds _ _ _ _ _ _ _ _ _ _ _ _ _ HC Dfd).
    - exact (cs_fs _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
    - exact (cs_limit _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
    - exact (cs_reserved _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
    - (* [comment removed for export] *) cbn [cfg_model cfg_of]. unfold pm_top. exact TOPm.
    - (* [comment removed for export] *) cbn [cfg_model cfg_of]. rewrite (cs_brk _ _ _ _ _ _ _ _ _ _ _ _ _ HC), Dbrk.
      apply eqm_Z_to_bv. exists 0. unfold Xof; cbn [ps_granted]. destruct g; unfold lden, pgo, pg; cbn [fst snd tden]; rewrite ?uE_var; lia.
    - (* [comment removed for export] *) cbn [cfg_model cfg_of]. pose proof (cs_eager _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as EG. rewrite Deager in EG. destruct g; lia.
    - (* [comment removed for export] *) cbn [cfg_model cfg_of]. rewrite (cs_maps _ _ _ _ _ _ _ _ _ _ _ _ _ HC Dnofog).
      transitivity (map (fun t : lin * lin * mkind => (Z_to_bv 64 (lden E (fst (fst t))), Z_to_bv 64 (lden E (snd (fst t)))))
                       (map (fun m => (lin_of (am_base m), lin_of (am_len m), am_kind m)) (a_maps ch))).
      { rewrite map_map. apply map_ext. intros m. reflexivity. }
      rewrite Dmaps. unfold zz2ww, PM_MAPS, Xof, pm_meta_map.
      cbn [ps_b04 ps_b05 ps_b06 ps_b08 ps_b09 ps_b10 ps_b11 ps_b12 ps_b13 ps_b16 ps_b19r ps_b20 ps_b21 ps_b22 ps_b23 ps_b24 ps_granted ps_a1 ps_a2 ps_a3 ps_g1 ps_g2 ps_g3 ps_g4].
      destruct g; cbn [map fst snd DG_maps]; unfold lMETA, pg, pgo, lden; cbn [fst snd tden]; rewrite ?uE_var;
        repeat first [reflexivity | apply f_equal2]; f_equal; lia.
    - (* [comment removed for export] *) cbn [cfg_model cfg_of].
      rewrite (proj1 (cs_noacc_lazy _ _ _ _ _ _ _ _ _ _ _ _ _ HC _ _ Dled)).
      apply DG_noacc_den; [exact VR06 | exact REL | intros _; exact BRK].
    - (* [comment removed for export] *) cbn [cfg_model cfg_of].
      rewrite (proj2 (cs_noacc_lazy _ _ _ _ _ _ _ _ _ _ _ _ _ HC _ _ Dled)).
      exact (DG_lazy_den E g (bv_unsigned sp0) VR06 REL).
  Qed.
End PMOpen.

Section PMProof.
  Variables (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (c : config).
  Hypothesis P : P_main sp0 brk0 mbase rdraw inp c.

  Theorem P_main_PM : exists X, PM sp0 brk0 inp X c.
  Proof.
    pose proof (P_main_H _ _ _ _ _ _ P) as P'. destruct P' as [(Vsp & Vbrk & Vmb & Vav & Vev & Vfit & Vuid & Vhw) (h & ch & E & R & FULL & model & Hh & _ & Hc & HC)].
    exists (Xof (hole_granted h) E). rewrite Hc. exact (PM_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC).
  Qed.
End PMProof.
