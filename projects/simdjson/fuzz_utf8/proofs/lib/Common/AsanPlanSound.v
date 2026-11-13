(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by gabelogan195, 2026-11: node_spin_sound reads the SpinScan.exec_has_spin conjunct of node_spin and passes it to SpinAlg.srz_spin as its third premise. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg DivergeSim SpinAlg AgentLib AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlan.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import FPSteps AxSymExecF AxSymExecFSound AxSymRunF. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3B. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AxSymExec3C AxSymExec3E AxSymExecFB.   (* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanPlanWhileSound.   (* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanPlanLedger.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Module APS.
Import AX2. Import AX2S. Import AP.
Import APWS.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section WithFP1.
Context {fx : FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition uE (E : env) (e : expr) : Z := bv_unsigned (edenot E e).

Definition pagedown (z : Z) : Z := z / 4096 * 4096.
Definition pageup (z : Z) : Z := (z + 4095) / 4096 * 4096.

Lemma pagedown_le : forall z, pagedown z <= z.
Proof. intros z. unfold pagedown. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. Qed.
End WithFP1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section WithFP2.
Context {fx : FPState}.

Lemma pageup_ge : forall z, z <= pageup z.
Proof. intros z. unfold pageup. lia. Qed.
Lemma pagedown_mod : forall z, pagedown z mod 4096 = 0.
Proof. intros z. unfold pagedown. rewrite Z.mod_mul. reflexivity. lia. Qed.
Lemma pageup_mod : forall z, pageup z mod 4096 = 0.
Proof. intros z. unfold pageup. apply Z.mod_mul. lia. Qed.
Lemma pageup_minus_pagedown : forall a b, a <= b -> pageup b - pagedown a <= b - a + 8192.
Proof. intros a b H. unfold pageup, pagedown. lia. Qed.
End WithFP2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section WithFP3.
Context {fx : FPState}.


(* [comment removed for export] *)
Definition in_ivs (z : Z) (l : list (word * word)) : bool :=
  existsb (fun iv => (bv_unsigned (fst iv) <=? z) && (z <? bv_unsigned (fst iv) + bv_unsigned (snd iv)))%bool l.

Definition in_hull (A : atable) (z : Z) : bool := ((img_lo A <=? z) && (z <? img_hi A))%bool.

(* [comment removed for export] *)
Definition iv_disjoint (p q : word * word) : Prop :=
  bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q)
  \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p).
Inductive seps : list (word * word) -> Prop :=
| seps_nil : seps []
| seps_cons : forall p l, Forall (iv_disjoint p) l -> seps l -> seps (p :: l).

Fixpoint sum_sizes (l : list (word * word)) : Z :=
  match l with [] => 0 | iv :: r => bv_unsigned (snd iv) + sum_sizes r end.

Definition cfg_of (SEGS : list Segment) (R : bvmap 5 word) (p : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (mkst R (Z_to_bv 64 p) M (seg_rom SEGS)) model.
End WithFP3.


(* [comment removed for export] *)
Inductive sec_guard {T : Type} (x : T) : Empty_set -> Prop := .

Section Sound.
(* [comment removed for export] *)
Variable SEGS : list Segment.
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable A : atable.
Variable nx0 : nat.
(* [comment removed for export] *)
Definition nx0_min_ok : Prop := (7 <= nx0)%nat.   (* [comment removed for export] *)
Hypothesis NX0_min : nx0_min_ok.
Variable LIMIT : Z.
Variable HS : nat -> option acs.
(* [comment removed for export] *)
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).

(* [comment removed for export] *)
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
(* [comment removed for export] *)
Definition res_len_ok : Prop := length (segments_reserved SEGS) = n_res A.
Definition hull_ok : Prop := 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI.
Definition shadow_ok : Prop := 0 <= shadow_off A <= 2 ^ 47.
Hypothesis RES_len : res_len_ok.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok.
Hypothesis SHADOW_ok : shadow_ok.

(* [comment removed for export] *)
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
(* [comment removed for export] *)
Hypothesis argH_sp0 : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.

(* [comment removed for export] *)
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Hypothesis HOLES_agree : forall h E E' fs, env_agree nx0 E E' -> HOLES h E fs = HOLES h E' fs.
Hypothesis HOLES_nil : forall h E fs, HOLES h E fs [].
(* [comment removed for export] *)
Variable FS0 : Fs.Fs.

(* [comment removed for export] *)
Variable KC : nat.
(* [comment removed for export] *)
Variable xp : xparams.
(* [comment removed for export] *)
Variable GP : nat -> list Z -> (word -> option byte) -> Prop.
Hypothesis lia_guard2 : forall k : Empty_set, sec_guard GP k.
(* [comment removed for export] *)
Hypothesis XPHQ : xp_hq xp = true -> forall h1 h2, HOLES h1 = HOLES h2.
Definition gholds (E : env) (M : word -> option byte) (g : gatom) : Prop := GP (g_id g) (map (uE E) (g_args g)) M.
(* [comment removed for export] *)
Definition props_ok (E : env) (M : word -> option byte) (l : list gatom) : Prop := Forall (gholds E M) l.

Section Fixed.   (* [comment removed for export] *)
Context {fx : FPState}.

#[local] Notation CHECK := (AP.check SEGS IT A nx0 LIMIT XN XE XB HS KC xp).

#[local] Notation cfg := (cfg_of SEGS).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Wz (fd : Z) (bs : list Z) : list event := map (fun z => WriteEv (Z_to_bv 64 fd) (Z_to_bv 8 z)) bs.
(* [comment removed for export] *)
Definition piece_den (E : env) (p : spiece) : list byte :=
  match p with SPLit bs => map (Z_to_bv 8) bs | SPBlob k => eb E k end.
Definition Wp (E : env) (fd : Z) (ps : list spiece) : list event :=
  map (WriteEv (Z_to_bv 64 fd)) (flat_map (piece_den E) ps).

(* [comment removed for export] *)
Fixpoint sd (D : TSet) (E : env) (fs : Fs.Fs) (s : shape) : TSet :=
  match s with
  | SNil => t_nil
  | SExit c => t_exit (Z_to_bv 64 c) fs
  | SEmitP fd ps s' => t_emit (Wp E fd ps) (sd D E fs s')
  | SAlt2 a b => t_alt2 (sd D E fs a) (sd D E fs b)
  | SCase e mid s1 s2 => if (bv_unsigned (edenot E e) <=? mid)%Z then sd D E fs s1 else sd D E fs s2
  | SHole h => HOLES h E fs
  | SNext => D
  end.
(* [comment removed for export] *)
Fixpoint sdK (K : nat -> env -> Fs.Fs -> TSet) (D : TSet) (E : env) (fs : Fs.Fs) (s : shape) : TSet :=
  match s with
  | SNil => t_nil
  | SExit c => t_exit (Z_to_bv 64 c) fs
  | SEmitP fd ps s' => t_emit (Wp E fd ps) (sdK K D E fs s')
  | SAlt2 a b => t_alt2 (sdK K D E fs a) (sdK K D E fs b)
  | SCase e mid s1 s2 => if (bv_unsigned (edenot E e) <=? mid)%Z then sdK K D E fs s1 else sdK K D E fs s2
  | SHole h => K h E fs
  | SNext => D
  end.
Lemma sd_sdK : forall D E fs s, sd D E fs s = sdK HOLES D E fs s.
Proof. intros D E fs s. induction s; cbn [sd sdK]; rewrite ?IHs, ?IHs1, ?IHs2; reflexivity. Qed.

(* [comment removed for export] *)
Definition sh_lo (E : env) (p : expr * expr) : Z := shadow_off A + uE E (fst p) / 8.
Definition sh_hi (E : env) (p : expr * expr) : Z := shadow_off A + (uE E (fst p) + uE E (snd p)) / 8.

(* [comment removed for export] *)
Definition allow1 (E : env) (p : expr * expr) : list (Z * Z) :=
  [(pagedown (uE E (fst p)), pageup (uE E (fst p) + uE E (snd p))); (pagedown (sh_lo E p), pageup (sh_hi E p))].
Definition allowA (E : env) (cs : acs) : list (Z * Z) := flat_map (allow1 E) (a_vis cs ++ a_ghost cs).

Definition amap_den (E : env) (m : amap) : word * word := (edenot E (am_base m), edenot E (am_len m)).

(* [comment removed for export] *)
Definition in_vis (E : env) (cs : acs) (z : Z) : bool :=
  existsb (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool (a_vis cs).
Definition in_sh (E : env) (cs : acs) (z : Z) : bool :=
  existsb (fun p => (sh_lo E p <=? z) && (z <? sh_hi E p))%bool (a_vis cs).
Definition in_allow (E : env) (cs : acs) (z : Z) : bool := (in_vis E cs z || in_sh E cs z)%bool.

(* [comment removed for export] *)
Definition in_ghost (E : env) (cs : acs) (z : Z) : bool :=
  existsb (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool (a_ghost cs).

(* [comment removed for export] *)
Definition vis (E : env) (cs : acs) (model : Model) (a : word) : bool :=
  let h := m_vmmaps model in
  let z := bv_unsigned a in
  (in_hull A z
   || ((CEIL <=? z) && (alloc_top h <=? z))   (* [comment removed for export] *)
   || (in_ivs z (vm_maps h) && negb (in_ivs z (vm_noaccess h))
       && (negb (page_in_ranges (page_base a) (m_vm_lazy model)) || in_allow E cs z)))%bool.

Definition hid (E : env) (cs : acs) (model : Model) (a : word) : bool :=
  (argH E a || negb (vis E cs model a))%bool.

(* [comment removed for export] *)
Definition Mr (E : env) (cs : acs) (model : Model) (FULL : word -> option byte) : word -> option byte :=
  mrestrict (hid E cs model) FULL.

Definition fds_std : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
   (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].

(* [comment removed for export] *)
Definition CH : nat := Z.to_nat 65536.
Definition chunk (j : nat) (c : list byte) : list byte := firstn CH (skipn (CH * j) c).
Definition flen (c : list byte) : Z := Z.min (Z.of_nat (length c)) (2 ^ 26).
Definition fds3 (e : FdEntry) : list (word * FdEntry) := (Z_to_bv 64 3, e) :: fds_std.
Definition fds_ok (E : env) (f : afd) (model : Model) : Prop :=
  match f with
  | AP.FdStd => m_fds model = fds_std
  | AP.FdDir => m_fds model = fds3 State.FdDir
  | AP.FdFile k len off => exists p c,
        m_fds model = fds3 (State.FdFile p (edenot E off)) /\ fs_lookup (m_fs model) p = Some c
     /\ uE E len = flen c /\ uE E off <= uE E len
     /\ (forall j, (65536 * Z.of_nat j < 2 ^ 26)%Z -> eb E (k + j)%nat = chunk j c)
  end.

(* [comment removed for export] *)
Fixpoint maps_match (E : env) (ms : list amap) (l : list (word * word)) : Prop :=
  match ms with
  | [] => l = []
  | m :: ms' =>
      if is_fog m       (* [comment removed for export] *)
      then maps_match E ms' l
           \/ exists iv l', l = iv :: l' /\ bv_unsigned (snd iv) <= uE E (am_len m) /\ maps_match E ms' l'
      else exists l', l = amap_den E m :: l' /\ maps_match E ms' l'
  end.

(* [comment removed for export] *)
Definition hole_ok (E : env) (ylo : Z) (l : list (word * word)) (m : amap) : Prop :=
  is_hole m = true ->
  (forall iv, In iv l -> bv_unsigned (fst iv) + bv_unsigned (snd iv) <= uE E (am_base m)
                         \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned (fst iv))
  /\ (uE E (am_base m) + uE E (am_len m) <= KHI \/ ylo <= uE E (am_base m)).
Lemma holes_mono : forall E y y' l ms,
  Forall (hole_ok E y l) ms -> y' <= y -> Forall (hole_ok E y' l) ms.
Proof.
  intros E y y' l ms H Hy. apply Forall_forall. intros m Hm Hh.
  destruct (proj1 (Forall_forall _ _) H m Hm Hh) as [H1 H2]. split; [exact H1 | lia].
Qed.
(* [comment removed for export] *)
Lemma holes_sublist : forall E y l l' ms,
  Forall (hole_ok E y l) ms -> (forall iv, In iv l' -> In iv l) -> Forall (hole_ok E y l') ms.
Proof.
  intros E y l l' ms H Hs. apply Forall_forall. intros m Hm Hh.
  destruct (proj1 (Forall_forall _ _) H m Hm Hh) as [H1 H2]. split; [intros iv Hiv; apply H1; apply Hs; exact Hiv | exact H2].
Qed.
(* [comment removed for export] *)
Lemma holes_none : forall E y l ms, Forall (fun m => is_hole m = false) ms -> Forall (hole_ok E y l) ms.
Proof. intros E y l ms H. apply Forall_forall. intros m Hm Hh. pose proof (proj1 (Forall_forall _ _) H m Hm) as X. congruence. Qed.

Record cs_ok (E : env) (cs : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model) : Prop := CS_OK {
  (* [comment removed for export] *)
  co_regs  : regs_ok E (s_regs (a_ss cs)) R;
  co_log   : s_log (a_ss cs) = [];
  co_know  : know_ok SEGS E (Mr E cs model FULL) (kn cs);
  (* [comment removed for export] *)
  co_halt  : m_halted model = None;
  co_fds   : fds_ok E (a_fd cs) model;
  co_fs    : m_fs model = FS0;
  co_tid   : a_tidset cs = false -> m_tid model = None;
  co_res   : vm_reserved (m_vmmaps model) = segments_reserved SEGS;
  co_limit : vm_limit (m_vmmaps model) = LIMIT;
  (* [comment removed for export] *)
  co_maps  : maps_match E (a_maps cs) (vm_maps (m_vmmaps model));
  co_holes : Forall (hole_ok E (a_ylo cs) (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) (a_maps cs);   (* [comment removed for export] *)
  co_seps  : seps (vm_maps (m_vmmaps model));
  co_wf    : model_ivs_wf model;
  (* [comment removed for export] *)
  co_bounds : Forall (fun iv => 0 < bv_unsigned (snd iv)
                                /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
                                /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= alloc_top (m_vmmaps model)
                                /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))) (vm_maps (m_vmmaps model));
  co_lazyb : Forall (fun iv => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))
                               /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= alloc_top (m_vmmaps model)) (m_vm_lazy model);
  co_nasub : forall z, in_ivs z (vm_noaccess (m_vmmaps model)) = true -> in_ivs z (vm_maps (m_vmmaps model)) = true;
  co_none  : Forall (fun m => am_kind m = KNONE \/ am_kind m = KNONELAZY ->
               In (amap_den E m) (vm_noaccess (m_vmmaps model))) (a_maps cs);
  co_kinds : Forall (fun m => am_kind m = KRWLAZY ->
               forall a : word, bv_unsigned (edenot E (am_base m)) <= bv_unsigned a < bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) ->
                 in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false
                 /\ page_in_ranges (page_base a) (m_vm_lazy model) = true) (a_maps cs);
  co_totsz : sum_sizes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= a_totsz cs;
  co_isp   : vm_init_sp (m_vmmaps model) = edenot E e_sp0;    (* [comment removed for export] *)
  co_brk   : vm_brk (m_vmmaps model) = edenot E (a_brk cs);
  co_sbrk  : bv_unsigned (vm_start_brk (m_vmmaps model)) <= bv_unsigned (vm_brk (m_vmmaps model));
  (* [comment removed for export] *)
  co_eager : eager_used model <= a_eager cs;
  co_abytes : A_bytes (allowA E cs) <= a_abytes cs;
  co_minv  : MInv (allowA E cs) model;
  (* [comment removed for export] *)
  co_zero  : forall a : word, hid E cs model a = true ->
               in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true ->
               in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false ->
               page_in_ranges (page_base a) (m_vm_lazy model) = true ->
               in_ghost E cs (bv_unsigned a) = false ->
               FULL a = Some (Z_to_bv 8 0);
  co_sinv  : SINV E FULL;
  (* [comment removed for export] *)
  co_plain : plain A = true -> m_vm_lazy model = []
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma A_wf_allowA : forall E cs, A_wf (allowA E cs).
Proof.
  intros E cs. unfold A_wf, allowA. apply Forall_forall. intros iv Hin.
  apply in_flat_map in Hin as [p [_ Hin]]. unfold allow1 in Hin.
  pose proof (u64_range (edenot E (snd p))) as Hn. pose proof (u64_range (edenot E (fst p))) as Hb.
  destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; unfold page_size.
  - pose proof (pagedown_le (uE E (fst p))). pose proof (pageup_ge (uE E (fst p) + uE E (snd p))). unfold uE in *.
    split; [lia|]. split; [apply pagedown_mod | apply pageup_mod].
  - pose proof (pagedown_le (sh_lo E p)). pose proof (pageup_ge (sh_hi E p)). unfold sh_lo, sh_hi, uE in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    split; [lia|]. split; [apply pagedown_mod | apply pageup_mod].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma page_base_le : forall a : word, bv_unsigned (page_base a) <= bv_unsigned a
                                       /\ bv_unsigned a < bv_unsigned (page_base a) + 4096
                                       /\ bv_unsigned (page_base a) mod 4096 = 0.
Proof.
  intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by lia.
  rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_bounds : forall (a : word) l lo hi,
  Forall (fun iv => lo <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= hi) l ->
  page_in_ranges (page_base a) l = true ->
  lo <= bv_unsigned a /\ bv_unsigned a + 1 <= hi + 4095.
Proof.
  intros a l lo hi Hl Hp. unfold page_in_ranges in Hp. apply existsb_exists in Hp as [iv [Hin Hb]].
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) Hl iv Hin) as [L1 L2].
  pose proof (page_base_le a) as (P1 & P2 & P3). unfold page_size in H2. lia.
Qed.

(* [comment removed for export] *)
Lemma lazy_byte_bounds : forall (a : word) l top,
  Forall (fun iv => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))
                    /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= top) l ->
  page_in_ranges (page_base a) l = true ->
  in_hull A (bv_unsigned a) = false /\ bv_unsigned a < top.
Proof.
  intros a l top Hl Hp. unfold page_in_ranges in Hp. apply existsb_exists in Hp as [iv [Hin Hb]].
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) Hl iv Hin) as [L1 L2].
  pose proof (page_base_le a) as (P1 & P2 & P3). unfold page_size in H2. split; [|lia].
  unfold in_hull. apply andb_false_iff. destruct L1 as [L1|L1]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
Qed.

Lemma lazy_cover_cs : forall E cs R FULL model,
  cs_ok E cs R FULL model -> lazy_cover (hid E cs model) (m_vm_lazy model) (allowA E cs).
Proof.
  intros E cs R FULL model HC w Hlz Hh. unfold hid in Hh. apply orb_false_iff in Hh as [Ha Hv].
  apply negb_false_iff in Hv. unfold vis in Hv.
  pose proof (lazy_byte_bounds w _ _ (co_lazyb _ _ _ _ _ HC) Hlz) as [B1 B2].
  pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (H0 & H1 & H2 & H3).
  apply orb_prop in Hv as [Hv|Hv].
  - apply orb_prop in Hv as [Hv|Hv].
    + (* [comment removed for export] *) rewrite B1 in Hv. discriminate.
    + (* [comment removed for export] *)
      apply andb_prop in Hv as [_ Hv]. apply Z.leb_le in Hv. lia.
  - apply andb_prop in Hv as [_ Hv]. rewrite Hlz in Hv. cbn [negb orb] in Hv.
    (* [comment removed for export] *)
    pose proof (page_base_le w) as (P1 & P2 & P3).
    unfold page_allowedb, allowA. apply existsb_exists. unfold page_size.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    unfold in_allow in Hv. apply orb_prop in Hv as [Hv|Hv].
    + unfold in_vis in Hv. apply existsb_exists in Hv as [p [Hin Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
      apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
      exists (pagedown (uE E (fst p)), pageup (uE E (fst p) + uE E (snd p))). split.
      * apply in_flat_map. exists p. split; [apply in_or_app; left; exact Hin|]. left. reflexivity.
      * cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
    + unfold in_sh in Hv. apply existsb_exists in Hv as [p [Hin Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
      apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
      exists (pagedown (sh_lo E p), pageup (sh_hi E p)). split.
      * apply in_flat_map. exists p. split; [apply in_or_app; left; exact Hin|]. right. left. reflexivity.
      * cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma H_off_segments_cs : forall E cs model, H_off_segments SEGS (hid E cs model).
Proof.
  intros E cs model a Hh. unfold hid in Hh. apply orb_prop in Hh as [Ha|Hv].
  - apply SEGS_in_hull. unfold in_hull. pose proof (argH_high _ _ Ha). pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (?&?&?&?).
    unfold CEIL, KHI in *. apply andb_false_iff. right. apply Z.ltb_ge. lia.
  - apply negb_true_iff in Hv. unfold vis in Hv. apply orb_false_iff in Hv as [Hv _]. apply orb_false_iff in Hv as [Hv _].
    apply SEGS_in_hull. exact Hv.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mrestrict_munrestrict_clean : forall (H : word -> bool) FULL m',
  (forall a, H a = true -> m' a = None) ->
  mrestrict H (munrestrict H FULL m') = m'.
Proof.
  intros H FULL m' Hc. apply functional_extensionality. intros a.
  unfold mrestrict, munrestrict. destruct (H a) eqn:Ha; [symmetry; apply Hc; exact Ha | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma vis_same : forall E cs model model',
  same_but_materialized model model' -> vis E cs model' = vis E cs model.
Proof.
  intros E cs model model' Hs. pose proof (same_but_materialized_frame _ _ Hs) as Hfr.
  apply functional_extensionality. intros a. unfold vis.
  replace (m_vmmaps model') with (m_vmmaps model) by (symmetry; apply Hfr).
  replace (m_vm_lazy model') with (m_vm_lazy model) by (symmetry; apply Hfr). reflexivity.
Qed.

Lemma hid_same : forall E cs model model',
  same_but_materialized model model' -> hid E cs model' = hid E cs model.
Proof. intros. unfold hid. apply functional_extensionality. intros a. rewrite (vis_same _ _ _ _ H). reflexivity. Qed.

(* [comment removed for export] *)
Lemma vis_ext : forall E cs cs' model,
  a_vis cs' = a_vis cs -> vis E cs' model = vis E cs model.
Proof. intros E cs cs' model Ha. apply functional_extensionality. intros a. unfold vis, in_allow, in_vis, in_sh. rewrite Ha. reflexivity. Qed.
Lemma hid_ext : forall E cs cs' model,
  a_vis cs' = a_vis cs -> hid E cs' model = hid E cs model.
Proof. intros. unfold hid. apply functional_extensionality. intros a. rewrite (vis_ext _ _ _ _ H). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mvis_eq (m m' : Model) : Prop :=
  vm_maps (m_vmmaps m') = vm_maps (m_vmmaps m) /\ vm_noaccess (m_vmmaps m') = vm_noaccess (m_vmmaps m)
  /\ m_vm_lazy m' = m_vm_lazy m /\ alloc_top (m_vmmaps m') = alloc_top (m_vmmaps m).
Lemma mvis_refl : forall m, mvis_eq m m.
Proof. intros m. repeat split; reflexivity. Qed.
Lemma mvis_trans : forall m1 m2 m3, mvis_eq m1 m2 -> mvis_eq m2 m3 -> mvis_eq m1 m3.
Proof. intros m1 m2 m3 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). repeat split; congruence. Qed.
Lemma mvis_of_materialized : forall m m', same_but_materialized m m' -> mvis_eq m m'.
Proof.
  intros m m' Hs. pose proof (same_but_materialized_frame _ _ Hs) as Hfr.
  assert (E1 : m_vmmaps m' = m_vmmaps m) by apply Hfr. assert (E2 : m_vm_lazy m' = m_vm_lazy m) by apply Hfr.
  unfold mvis_eq. rewrite E1, E2. repeat split; reflexivity.
Qed.
Lemma vis_mvis : forall E cs m m', mvis_eq m m' -> vis E cs m' = vis E cs m.
Proof.
  intros E cs m m' (H1 & H2 & H3 & H4). apply functional_extensionality. intros a. unfold vis. rewrite H1, H2, H3, H4. reflexivity.
Qed.
Lemma hid_mvis : forall E cs m m', mvis_eq m m' -> hid E cs m' = hid E cs m.
Proof. intros. unfold hid. apply functional_extensionality. intros a. rewrite (vis_mvis _ _ _ _ H). reflexivity. Qed.

(* [comment removed for export] *)
Lemma cs_ok_frame : forall E cs R FULL model ss' R' FULL' model',
  cs_ok E cs R FULL model ->
  same_but_materialized model model' ->
  MInv (allowA E cs) model' ->
  regs_ok E (s_regs ss') R' -> s_log ss' = [] ->
  know_ok SEGS E (Mr E cs model FULL') (s_know ss') ->
  (forall a, hid E cs model a = true -> FULL' a = FULL a) ->
  cs_ok E (with_ss cs ss') R' FULL' model'.
Proof.
  intros E cs R FULL model ss' R' FULL' model' HC Hs Hinv HR HL HK Hhid.
  pose proof (same_but_materialized_frame _ _ Hs) as Hfr.
  assert (Evm : m_vmmaps model' = m_vmmaps model) by apply Hfr.
  assert (Elz : m_vm_lazy model' = m_vm_lazy model) by apply Hfr.
  destruct HC. constructor; cbn [with_ss a_ss a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset kn];
    rewrite ?Evm, ?Elz; try assumption.
  - unfold Mr. rewrite (hid_same _ _ _ _ Hs). exact HK.
  - replace (m_halted model') with (m_halted model) by (symmetry; apply Hfr). assumption.
  - unfold fds_ok in *. replace (m_fds model') with (m_fds model) by (symmetry; apply Hfr).
    replace (m_fs model') with (m_fs model) by (symmetry; apply Hfr). assumption.
  - replace (m_fs model') with (m_fs model) by (symmetry; apply Hfr). assumption.
  - intros Ht. replace (m_tid model') with (m_tid model) by (symmetry; apply Hfr). auto.
  - unfold model_ivs_wf in *. rewrite Evm, Elz. assumption.
  - replace (eager_used model') with (eager_used model) by (symmetry; apply Hfr). assumption.
  - intros a Hh. rewrite (hid_same _ _ _ _ Hs) in Hh. rewrite (Hhid a Hh). auto.
  - eapply SINV_frame; [|eassumption]. intros a Ha. apply Hhid. unfold hid. rewrite Ha. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma know_ok_filter : forall E M f k, know_ok SEGS E M k -> know_ok SEGS E M (List.filter f k).
Proof.
  intros E M f k HK. unfold know_ok in *. apply Forall_forall. intros K Hin.
  apply filter_In in Hin as [Hin _]. exact (proj1 (Forall_forall _ _) HK K Hin).
Qed.

Lemma cs_ok_set_kn : forall E cs R FULL model k',
  cs_ok E cs R FULL model -> know_ok SEGS E (Mr E cs model FULL) k' ->
  cs_ok E (set_kn cs k') R FULL model.
Proof.
  intros E cs R FULL model k' HC HK.
  destruct HC; constructor; cbn [set_kn with_ss a_ss a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know];
    try assumption; reflexivity.
Qed.

Lemma cs_gc_ok : forall gb E cs R FULL model, cs_ok E cs R FULL model -> cs_ok E (cs_gc gb cs) R FULL model.
Proof.
  intros gb E cs R FULL model HC. unfold cs_gc. destruct (split_lit (reg cs 2)) as [spb spk].
  apply cs_ok_set_kn; [exact HC|]. apply know_ok_filter. exact (co_know _ _ _ _ _ HC).
Qed.

Lemma mk_itab_ranges_acc_sound : forall rs t, itab_sound SEGS t -> itab_sound SEGS (mk_itab_ranges_acc SEGS rs t).
Proof.
  induction rs as [|[lo n] rs IH]; intros t Ht; cbn [mk_itab_ranges_acc]; [exact Ht|].
  apply IH. apply mk_itab_fuel_sound. exact Ht.
Qed.
Lemma mk_itab_ranges_sound : forall rs, itab_sound SEGS (mk_itab_ranges SEGS rs).
Proof.
  intros rs. unfold mk_itab_ranges. apply mk_itab_ranges_acc_sound.
  intros pc i. unfold itab_lookup. destruct pc; try discriminate. rewrite pt_get_leaf. discriminate.
Qed.

Lemma pc_set_kn : forall cs k, pc (set_kn cs k) = pc cs.
Proof. reflexivity. Qed.
Lemma pc_cs_gc : forall gb cs, pc (cs_gc gb cs) = pc cs.
Proof. intros gb cs. unfold cs_gc. destruct (split_lit (reg cs 2)); reflexivity. Qed.

Lemma drop_ixs_incl : forall ixs i k K, In K (drop_ixs ixs i k) -> In K k.
Proof.
  intros ixs i k. revert i. induction k as [|K' r IH]; intros i K Hin; cbn [drop_ixs] in Hin.
  - exact Hin.
  - destruct (existsb (Nat.eqb i) ixs).
    + right. eapply IH. exact Hin.
    + destruct Hin as [<-|Hin]; [left; reflexivity | right; eapply IH; exact Hin].
Qed.

Lemma forget_sound : forall E cs R FULL model ixs,
  cs_ok E cs R FULL model -> cs_ok E (set_kn cs (drop_ixs ixs 0 (kn cs))) R FULL model.
Proof.
  intros E cs R FULL model ixs HC. apply cs_ok_set_kn; [exact HC|].
  unfold know_ok. apply Forall_forall. intros K Hin. apply drop_ixs_incl in Hin.
  exact (proj1 (Forall_forall _ _) (co_know _ _ _ _ _ HC) K Hin).
Qed.

(* [comment removed for export] *)
Definition kfoot (E : env) (K : kentry) : option (Z * Z) :=
  match K with
  | KWord a w _ => Some (estart E a, Z.of_nat w)
  | KZero a l => Some (estart E a, elenZ E l)
  | KBlob a l _ => Some (estart E a, elenZ E l)
  | KImg lo hi => Some (lo, hi - lo)%Z
  | KWr a n => Some (estart E a, elenZ E n)
  | KFill a l _ => Some (estart E a, elenZ E l)
  | KUnk a l => Some (estart E a, elenZ E l)
  | KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ => None
  end.

Definition kfoot_apart (E : env) (K : kentry) (lo n : Z) : Prop :=
  match kfoot E K with
  | None => True
  | Some (s, l) => (s + l <= lo \/ lo + n <= s)%Z
  end.

Lemma kentry_keep_sem : forall E M M' K lo n,
  kentry_ok SEGS E M K -> kfoot_apart E K lo n ->
  (forall x : word, (bv_unsigned x < lo \/ lo + n <= bv_unsigned x)%Z -> M' x = M x) ->
  kentry_ok SEGS E M' K.
Proof.
  intros E M M' K lo n HK Hap Hout.
  assert (RD : forall (a : word) k, (bv_unsigned a + Z.of_nat k <= 2 ^ 64)%Z ->
     (bv_unsigned a + Z.of_nat k <= lo \/ lo + n <= bv_unsigned a)%Z ->
     rdn SEGS M' a k = rdn SEGS M a k).
  { intros a k Hnw Hd. apply rdn_ext; [exact Hnw|]. intros x Hx. apply Hout. lia. }
  unfold kfoot_apart, kfoot in Hap.
  destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2|[b k] nn fc|[b k] nn]; cbn [kentry_ok] in *;
    try exact HK.
  7: { (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia. }
  6: { (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia. }
  - (* [comment removed for export] *) destruct HK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|].
    rewrite RD; [exact Hrd | rewrite (flat_u E _ _ Hfl); destruct Hfl; lia | rewrite (flat_u E _ _ Hfl); lia].
  - (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as (HA & HB & HC). split; [exact HA|]. split; [exact HB|]. intros i Hi.
    rewrite Hout; [apply HC; lia|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as [Hfl Hs]. split; [exact Hfl|]. intros d m Hd0 Hdm.
    pose proof (Hs d m Hd0 Hdm) as H. destruct Hfl as (F1 & F2 & F3 & F4).
    destruct m as [|m']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia.
    unfold wview. rewrite Hout by lia. fold (wview SEGS M x).
    eapply (store_ok_all SEGS M (Datatypes.S m')); [| exact H |]; rewrite u64_lit by lia; lia.
Qed.

Lemma elenZ_lit : forall E z, (0 <= z < 2 ^ 64)%Z -> elenZ E (ELit z) = z.
Proof. intros E z Hz. unfold elenZ. cbn [edenot]. rewrite u64_lit by lia. reflexivity. Qed.

Lemma kentry_apart_b_sem : forall E M allkn K ub uk un,
  know_ok SEGS E M allkn -> kentry_apart_b allkn ub uk un K = true ->
  kfoot_apart E K (estart E (SA ub uk)) (elenZ E un).
Proof.
  intros E M allkn K ub uk un Hall Hb. unfold kfoot_apart, kfoot.
  destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2|[b k] nn fc|[b k] nn]; cbn [kentry_apart_b] in Hb;
    try exact I; try discriminate.
  7: { pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia. }
  6: { pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia. }
  - apply andb_prop in Hb as [Hw Hb]. apply Nat.leb_le in Hw.
    pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb) as Hd.
    rewrite (elenZ_lit E (Z.of_nat w)) in Hd by lia. lia.
  - pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
  - pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
  - apply andb_prop in Hb as [Hb Hap]. apply andb_prop in Hb as [Hb Hlt]. apply andb_prop in Hb as [H0 Hl].
    apply Z.leb_le in H0. apply Z.leb_le in Hl. apply Z.ltb_lt in Hlt. unfold two64 in Hlt.
    pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hap) as Hd.
    rewrite (elenZ_lit E (ihi - ilo)) in Hd by lia.
    unfold estart in Hd at 2 3. cbn [a_base a_off edenot] in Hd.
    rewrite !u64_lit in Hd by lia. lia.
  - pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
Qed.

Lemma kentry_apart_keep : forall E M M' allkn K (ub : expr) uk un,
  know_ok SEGS E M allkn -> kentry_ok SEGS E M K ->
  kentry_apart_b allkn ub uk un K = true ->
  (forall x : word, (bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + elenZ E un <= bv_unsigned x)%Z ->
                     M' x = M x) ->
  kentry_ok SEGS E M' K.
Proof.
  intros E M M' allkn K ub uk un Hall HK Hb Hout.
  eapply kentry_keep_sem; [exact HK | eapply kentry_apart_b_sem; [exact Hall | exact Hb] | exact Hout].
Qed.

Lemma know_ok_filter_apart : forall E M M' k (f : kentry -> bool) (ub : expr) uk un,
  know_ok SEGS E M k ->
  (forall K, In K k -> f K = true -> kentry_apart_b k ub uk un K = true \/ kentry_ok SEGS E M' K) ->
  (forall x : word, (bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + elenZ E un <= bv_unsigned x)%Z ->
                     M' x = M x) ->
  know_ok SEGS E M' (List.filter f k).
Proof.
  intros E M M' k f ub uk un HK Hf Hout. unfold know_ok. apply Forall_forall. intros K Hin.
  apply filter_In in Hin as [Hin Hfk].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct (Hf K Hin Hfk) as [Hap | Hdone]; [|exact Hdone].
  eapply kentry_apart_keep; eassumption.
Qed.

(* [comment removed for export] *)
Lemma kentry_apart_bp_eq : forall allkn ub uk un K,
  kentry_apart_bp allkn (mk_sprep allkn ub uk un) ub uk un K = kentry_apart_b allkn ub uk un K.
Proof.
  intros allkn ub uk un K. destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    cbn [kentry_apart_bp kentry_apart_b]; rewrite ?ranges_apart_p_eq; reflexivity.
Qed.

Lemma havoc1p_eq : forall k ub uk un K,
  havoc1p k (mk_sprep k ub uk un) ub uk un K = havoc1 k ub uk un K.
Proof. intros. unfold havoc1p, havoc1. rewrite kentry_apart_bp_eq. reflexivity. Qed.


(* [comment removed for export] *)
Lemma know_ok_havoc : forall E M M' k b o n,
  know_ok SEGS E M k ->
  (forall x : word, (bv_unsigned x < estart E (SA b o) \/ estart E (SA b o) + elenZ E n <= bv_unsigned x)%Z -> M' x = M x) ->
  mem_grows M M' ->
  know_ok SEGS E M' (kn_havoc k b o n).
Proof.
  intros E M M' k b o n HK Hout Hg. unfold kn_havoc, know_ok. cbv zeta.
  apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK.
  rewrite havoc1p_eq. unfold havoc1.
  destruct (kwr_b K || kentry_apart_b k b o n K)%bool eqn:Hf.
  - apply Forall_one. apply orb_prop in Hf as [Hw|Ha].
    + destruct K as [| | | | | |[wb wk] wn| | |]; try discriminate.
      destruct HKK as [Hfl Hs]. cbn [kentry_ok]. split; [exact Hfl|].
      intros d m Hd Hdm. eapply store_ok_mono; [exact Hg | apply Hs; assumption].
    + eapply kentry_apart_keep; eassumption.
  - destruct K as [|[kb kk] len| | | | | | |[kb kk] len fc|[kb kk] len]; try constructor.
    + eapply kzero_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kfill_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kunk_cut_sound; [exact HK | exact HKK | exact Hout].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pw_kind (mk : saddr -> expr -> kentry) (P : (word -> option byte) -> word -> Prop) : Prop :=
  forall E M a n,
    kentry_ok SEGS E M (mk a n)
    <-> (flat E a (elenZ E n) /\ forall i, (0 <= i < elenZ E n)%Z -> P M (Z_to_bv 64 (estart E a + i))).

Lemma pw_kind_zf : forall mk byteof, zf_kind SEGS mk byteof -> pw_kind mk (fun M x => byteof (M x)).
Proof. intros mk byteof H E M a n. exact (H E M a n). Qed.

Lemma pw_kind_wr : pw_kind KWr (fun M x => wview SEGS M x <> None).
Proof.
  intros E M a n. cbn [kentry_ok]. split; intros [Hfl H]; split; try exact Hfl.
  - intros i Hi. pose proof (H i 1%nat ltac:(lia) ltac:(cbn; lia)) as S1. cbn [store_ok] in S1.
    destruct (wview SEGS M (Z_to_bv 64 (estart E a + i))); [discriminate | discriminate].
  - intros d m Hd Hdm. pose proof Hfl as Hfl0. destruct Hfl as (F1 & F2 & F3 & F4).
    destruct m as [|m']; [reflexivity|]. set (m := Datatypes.S m') in *.
    assert (Hm : 1 <= Z.of_nat m) by (subst m; rewrite Nat2Z.inj_succ; lia).
    assert (Hu : bv_unsigned (Z_to_bv 64 (estart E a + d)) = estart E a + d) by (apply u_small; lia).
    apply store_ok_of_all; rewrite Hu; [lia|].
    intros x Hx. replace x with (Z_to_bv 64 (estart E a + (bv_unsigned x - estart E a))).
    + apply H. lia.
    + apply bv_eq. rewrite u_small; [lia|]. pose proof (u64_range x). lia.
Qed.

(* [comment removed for export] *)
Lemma kcut_pw_sound : forall mk P E M0 M M' allkn wb wk wn kb kk len,
  pw_kind mk P ->
  know_ok SEGS E M0 allkn ->
  kentry_ok SEGS E M (mk (SA kb kk) len) ->
  (forall x : word,
     (bv_unsigned x < estart E (SA wb wk) \/ estart E (SA wb wk) + elenZ E wn <= bv_unsigned x)%Z ->
     P M x -> P M' x) ->
  Forall (kentry_ok SEGS E M') (kcut mk allkn wb wk wn kb kk len).
Proof.
  intros mk P E M0 M M' allkn wb wk wn kb kk len Hkind Hall HK Hout.
  apply (proj1 (Hkind E M _ _)) in HK. destruct HK as [Hfl Hz].
  unfold kcut.
  set (ws := mkAlu ALU_ADD wb (ELit wk)). set (ks := mkAlu ALU_ADD kb (ELit kk)).
  assert (Uws : eqm (bv_unsigned (edenot E ws)) (estart E (SA wb wk))).
  { subst ws. rewrite mkAlu_denot. unfold estart; cbn [a_base a_off edenot].
    eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [apply eqm_refl|apply eqm_u_lit]. }
  assert (Uks : eqm (bv_unsigned (edenot E ks)) (estart E (SA kb kk))).
  { subst ks. rewrite mkAlu_denot. unfold estart; cbn [a_base a_off edenot].
    eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [apply eqm_refl|apply eqm_u_lit]. }
  pose proof Hfl as Hfl0. destruct Hfl as (F1 & F2 & F3 & F4).
  apply Forall_app; split.
  - (* [comment removed for export] *)
    destruct (lin_ge0 allkn [(kb, kk)] [(wb, wk)]); [constructor|].
    destruct (lin_ge0 allkn [(wb, wk)] [(kb, kk)]) eqn:H1; [|constructor].
    destruct (lin_ge0 allkn [(kb, kk); (len, 0%Z)] [(wb, wk)]) eqn:H2; [|constructor].
    pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H1) as A0. cbn [xt_den] in A0.
    pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H2) as B0. cbn [xt_den] in B0.
    constructor; [|constructor]. apply (proj2 (Hkind E M' _ _)).
    assert (HL : elenZ E (mkAlu ALU_SUB ws ks) = (estart E (SA wb wk) - estart E (SA kb kk))%Z).
    { unfold elenZ. rewrite mkAlu_denot.
      assert (eqm (bv_unsigned (alu64 ALU_SUB (edenot E ws) (edenot E ks))) (estart E (SA wb wk) - estart E (SA kb kk))) as [q Hq].
      { eapply eqm_trans; [apply u_sub_eqm|]. apply eqm_add; [exact Uws|]. destruct Uks as [q Hq]. exists (-q)%Z. lia. }
      pose proof (u64_range (alu64 ALU_SUB (edenot E ws) (edenot E ks))) as R.
      pose proof (u64_range (edenot E len)) as RL.
      unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia. }
    rewrite HL. split.
    + unfold flat in *. unfold estart, elenZ in *; cbn [a_base a_off] in *. lia.
    + intros i Hi. apply Hout; [|apply Hz]; unfold estart, elenZ in *; cbn [a_base a_off] in *; [|lia].
      left. rewrite u_small; lia.
  - (* [comment removed for export] *)
    destruct (lin_ge0 allkn [(kb, kk); (len, 0%Z)] [(wb, wk); (wn, 0%Z)]) eqn:H1; [|constructor].
    destruct (lin_ge0 allkn [(wb, wk); (wn, 0%Z)] [(kb, kk)]) eqn:H2; [|constructor].
    destruct (lin_ge0 allkn [(ELit 0, (two64 - 1)%Z)] [(kb, kk); (len, 0%Z)]) eqn:H3; [|constructor].
    pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H1) as A0. cbn [xt_den] in A0.
    pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H2) as B0. cbn [xt_den] in B0.
    pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H3) as C0. cbn [xt_den edenot] in C0.
    rewrite u_lit0 in C0. unfold two64 in C0.
    cbv zeta.
    set (we := mkAlu ALU_ADD ws wn).
    assert (Uwe : eqm (bv_unsigned (edenot E we)) (estart E (SA wb wk) + elenZ E wn)).
    { subst we. rewrite mkAlu_denot. eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [exact Uws|apply eqm_refl]. }
    destruct (split_lit we) as [hb ho] eqn:Hsp.
    lazymatch goal with |- Forall _ [mk ?ha0 _] => set (ha := ha0) end.
    assert (Hst : estart E ha = (estart E (SA wb wk) + elenZ E wn)%Z).
    { subst ha.
      destruct (lin_ge0 allkn [(hb, ho)] [(wb, wk); (wn, 0%Z)] && lin_ge0 allkn [(wb, wk); (wn, 0%Z)] [(hb, ho)])%bool eqn:Hh.
      - apply andb_prop in Hh as [Hh1 Hh2].
        pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall Hh1) as C1. cbn [xt_den] in C1.
        pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall Hh2) as C2. cbn [xt_den] in C2.
        unfold estart, elenZ in *; cbn [a_base a_off] in *. lia.
      - unfold estart at 1; cbn [a_base a_off]. rewrite Z.add_0_r.
        destruct Uwe as [q Hq]. pose proof (u64_range (edenot E we)).
        pose proof (u64_range (edenot E len)) as RL.
        unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia. }
    assert (HL : elenZ E (mkAlu ALU_SUB (mkAlu ALU_ADD ks len) we)
                 = (estart E (SA kb kk) + elenZ E len - (estart E (SA wb wk) + elenZ E wn))%Z).
    { unfold elenZ at 1. rewrite mkAlu_denot.
      assert (eqm (bv_unsigned (alu64 ALU_SUB (edenot E (mkAlu ALU_ADD ks len)) (edenot E we)))
                  (estart E (SA kb kk) + elenZ E len - (estart E (SA wb wk) + elenZ E wn))) as [q Hq].
      { eapply eqm_trans; [apply u_sub_eqm|]. apply eqm_add.
        - rewrite mkAlu_denot. eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [exact Uks|apply eqm_refl].
        - destruct Uwe as [q Hq]. exists (-q)%Z. lia. }
      pose proof (u64_range (alu64 ALU_SUB (edenot E (mkAlu ALU_ADD ks len)) (edenot E we))) as R.
      pose proof (u64_range (edenot E len)) as RL.
      unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia. }
    constructor; [|constructor]. apply (proj2 (Hkind E M' _ _)). rewrite HL.
    split.
    + unfold flat. rewrite Hst. pose proof (u64_range (edenot E len)) as RL.
      unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia.
    + intros i Hi. rewrite Hst.
      apply Hout.
      * right. pose proof (u64_range (edenot E len)) as RL.
        rewrite u_small; unfold flat, estart, elenZ in *; cbn [a_base a_off] in *; lia.
      * replace (estart E (SA wb wk) + elenZ E wn + i)%Z
          with (estart E (SA kb kk) + (estart E (SA wb wk) + elenZ E wn - estart E (SA kb kk) + i))%Z by lia.
        apply Hz. unfold estart, elenZ in *; cbn [a_base a_off] in *. lia.
Qed.

Lemma kwr_cut_sound : forall E M0 M M' allkn wb wk wn kb kk len,
  know_ok SEGS E M0 allkn ->
  kentry_ok SEGS E M (KWr (SA kb kk) len) ->
  (forall x : word,
     (bv_unsigned x < estart E (SA wb wk) \/ estart E (SA wb wk) + elenZ E wn <= bv_unsigned x)%Z ->
     M' x = M x) ->
  Forall (kentry_ok SEGS E M') (kwr_cut allkn wb wk wn kb kk len).
Proof.
  intros. eapply (kcut_pw_sound KWr _ E M0 M M'); [apply pw_kind_wr | eassumption | eassumption |].
  intros x Hx HP. unfold wview in *. rewrite (H1 x Hx). exact HP.
Qed.

Lemma cutout1p_eq : forall k ub uk un K,
  cutout1p k (mk_sprep k ub uk un) ub uk un K = cutout1 k ub uk un K.
Proof. intros. unfold cutout1p, cutout1. rewrite kentry_apart_bp_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma know_ok_cutout : forall E M M' k b o n,
  know_ok SEGS E M k ->
  (forall x : word, (bv_unsigned x < estart E (SA b o) \/ estart E (SA b o) + elenZ E n <= bv_unsigned x)%Z -> M' x = M x) ->
  know_ok SEGS E M' (kn_cutout k b o n).
Proof.
  intros E M M' k b o n HK Hout. unfold kn_cutout, know_ok. cbv zeta.
  apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK.
  rewrite cutout1p_eq. unfold cutout1.
  destruct (kentry_apart_b k b o n K) eqn:Hf.
  - apply Forall_one. eapply kentry_apart_keep; eassumption.
  - destruct K as [|[kb kk] len| | | | |[kb kk] len| |[kb kk] len fc|[kb kk] len]; try constructor.
    + eapply kzero_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kwr_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kfill_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kunk_cut_sound; [exact HK | exact HKK | exact Hout].
Qed.

Lemma droprange_sound : forall E cs R FULL model b n,
  cs_ok E cs R FULL model -> cs_ok E (node_droprange cs b n) R FULL model.
Proof.
  intros E cs R FULL model b n HC. unfold node_droprange. destruct (split_lit b) as [bb bk].
  apply cs_ok_set_kn; [exact HC|]. eapply know_ok_havoc; [exact (co_know _ _ _ _ _ HC) | intros; reflexivity | apply mem_grows_refl].
Qed.

Lemma bump_sound : forall E cs R FULL model m cs',
  cs_ok E cs R FULL model -> node_bump cs m = Some cs' -> cs_ok E cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model m cs' HC H. unfold node_bump in H. destruct (Nat.leb (nxt cs) m); [|discriminate]. injection H as <-.
  split; [|reflexivity].
  destruct HC; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset];
    try assumption; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mkind_eqb_eq : forall a b, mkind_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; first [reflexivity | discriminate]. Qed.
Lemma kentry_eqb_eq : forall x y, kentry_eqb x y = true -> x = y.
Proof.
  intros x y H. destruct x, y; cbn [kentry_eqb] in H; try discriminate;
  repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
    end;
  repeat match goal with
    | H : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in H
    | H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H
    | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
    | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
    end; subst; reflexivity.
Qed.
Lemma amap_eqb_eq : forall x y, amap_eqb x y = true -> x = y.
Proof.
  intros [b l k] [b' l' k'] H. unfold amap_eqb in H. cbn [am_base am_len am_kind] in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. apply mkind_eqb_eq in H3. congruence.
Qed.
Lemma pair_eqb_eq : forall x y, pair_eqb x y = true -> x = y.
Proof.
  intros [a b] [a' b'] H. unfold pair_eqb in H. cbn [fst snd] in H. apply andb_prop in H as [H1 H2].
  apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. congruence.
Qed.
Lemma afd_eqb_eq : forall x y, afd_eqb x y = true -> x = y.
Proof.
  intros [|k l o|] [|k' l' o'|] H; cbn [afd_eqb] in H; try discriminate; try reflexivity.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1. apply expr_eqb_eq in H2. apply expr_eqb_eq in H3. congruence.
Qed.
Lemma list_eqb_eq : forall {T} (eqb : T -> T -> bool), (forall x y, eqb x y = true -> x = y) ->
  forall x y, list_eqb eqb x y = true -> x = y.
Proof.
  intros T eqb Heq x. induction x as [|a x IH]; intros [|b y] H; cbn [list_eqb] in H; try discriminate; [reflexivity|].
  destruct (eqb a b) eqn:H1; [|discriminate]. rewrite (Heq _ _ H1), (IH _ H). reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kimg_in_hull (k : list kentry) : Prop :=
  Forall (fun K => match K with KImg lo hi => img_lo A <= lo /\ hi <= img_hi A | _ => True end) k.

Lemma kimg_clip_in_hull : forall k, kimg_in_hull (kimg_clip A k).
Proof.
  intros k. unfold kimg_in_hull, kimg_clip. apply Forall_forall. intros K Hin. apply filter_In in Hin as [_ Hb].
  destruct K; try exact I. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H3. lia.
Qed.

Lemma kimg_clip_incl : forall k K, In K (kimg_clip A k) -> In K k.
Proof. intros k K H. unfold kimg_clip in H. apply filter_In in H as [H _]. exact H. Qed.

Lemma kimg_in_hull_app : forall k1 k2, kimg_in_hull k1 -> kimg_in_hull k2 -> kimg_in_hull (k1 ++ k2).
Proof. intros. unfold kimg_in_hull in *. apply Forall_app. auto. Qed.

(* [comment removed for export] *)
Lemma hid_hull : forall E cs model (a : word), in_hull A (bv_unsigned a) = true -> hid E cs model a = false.
Proof.
  intros E cs model a Hh. unfold hid, vis. rewrite Hh. cbn [orb].
  destruct (argH E a) eqn:Ha; [|reflexivity]. exfalso.
  pose proof (argH_high _ _ Ha). unfold in_hull in Hh. apply andb_prop in Hh as [_ Hh]. apply Z.ltb_lt in Hh.
  pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (?&?&?&?). unfold CEIL, KHI in *. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_visible : forall (H : word -> bool) FULL (a : word) w bs,
  H_off_segments SEGS H ->
  rdn SEGS (mrestrict H FULL) a w = Some bs ->
  forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat w -> H x = false.
Proof.
  intros H FULL a w. revert a. induction w as [|w IH]; intros a bs HH Hr x Hx; [lia|].
  cbn [rdn] in Hr. unfold mrestrict in Hr at 1.
  destruct (H a) eqn:Ha.
  - (* [comment removed for export] *)
    assert (Hs : seg_rom SEGS a = None).
    { unfold seg_rom. rewrite (memory_read1_hidden SEGS H HH a Ha). reflexivity. }
    rewrite Hs in Hr. discriminate.
  - destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
    + assert (x = a) by (apply bv_eq; exact Heq). subst x. exact Ha.
    + fold (mrestrict H FULL) in Hr.
      destruct (match FULL a with Some b => Some b | None => seg_rom SEGS a end) as [b|]; [|discriminate].
      destruct (rdn SEGS (mrestrict H FULL) (a + 1)%bv w) as [rest|] eqn:Hr2; [|discriminate].
      pose proof (u64_range x).
      assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
      eapply (IH (a + 1)%bv rest HH Hr2). rewrite Hu1. lia.
Qed.

(* [comment removed for export] *)
Lemma know_ok_unhide : forall E (H1 H2 : word -> bool) FULL k,
  H_off_segments SEGS H1 ->
  kimg_in_hull k ->
  (forall a, H2 a = true -> H1 a = true) ->
  (forall a : word, in_hull A (bv_unsigned a) = true -> H1 a = false) ->
  know_ok SEGS E (mrestrict H1 FULL) k -> know_ok SEGS E (mrestrict H2 FULL) k.
Proof.
  intros E H1 H2 FULL k HH1 Hki Hsub Hhull HK.
  assert (AG : forall a, H1 a = false -> mrestrict H2 FULL a = mrestrict H1 FULL a).
  { intros a Ha. unfold mrestrict. rewrite Ha. destruct (H2 a) eqn:Ha2; [|reflexivity].
    rewrite (Hsub a Ha2) in Ha. discriminate. }
  assert (GR : mem_grows (mrestrict H1 FULL) (mrestrict H2 FULL)).
  { intros x Hx. unfold mrestrict in *. destruct (H1 x) eqn:H1x; [exfalso; apply Hx; reflexivity|].
    destruct (H2 x) eqn:H2x; [rewrite (Hsub x H2x) in H1x; discriminate | exact Hx]. }
  unfold know_ok in *. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  pose proof (proj1 (Forall_forall _ _) Hki K Hin) as HKi.
  destruct K as [a w v|a n|a n kb|lo hi|e m|e lo hi|a n|a1 n1 a2 n2|a n fc|a n]; cbn [kentry_ok] in *; try exact HKK.
  7: { (* [comment removed for export] *) destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    pose proof (Hz i Hi) as Hzi. rewrite AG; [exact Hzi|].
    unfold mrestrict in Hzi |- *. destruct (H1 _); [exfalso; apply Hzi; reflexivity | reflexivity]. }
  - (* [comment removed for export] *) destruct HKK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|].
    rewrite <- Hrd. apply rdn_ext.
    + rewrite (flat_u E _ _ Hfl). destruct Hfl as (?&?&?&?). lia.
    + intros x Hx. apply AG. eapply rdn_visible; [exact HH1 | exact Hrd | exact Hx].
  - (* [comment removed for export] *) destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    pose proof (Hz i Hi) as Hzi. rewrite AG; [exact Hzi|].
    unfold mrestrict in Hzi. destruct (H1 _); [discriminate | reflexivity].
  - (* [comment removed for export] *) destruct HKK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
    pose proof (Hz i Hi) as Hzi. rewrite AG; [exact Hzi|].
    unfold mrestrict in Hzi. destruct (H1 _); [discriminate | reflexivity].
  - (* [comment removed for export] *) destruct HKK as (HA & HB & HC). split; [exact HA|]. split; [exact HB|]. intros i Hi.
    assert (Hh : in_hull A (bv_unsigned (Z_to_bv 64 i)) = true).
    { unfold in_hull. rewrite u64_lit by lia. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    rewrite AG; [apply HC; exact Hi | apply Hhull; exact Hh].
  - (* [comment removed for export] *) destruct HKK as [Hfl Hs]. split; [exact Hfl|]. intros d m Hd Hdm.
    eapply store_ok_mono; [exact GR | apply Hs; assumption].
  - (* [comment removed for export] *) destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    pose proof (Hz i Hi) as Hzi. rewrite AG; [exact Hzi|].
    unfold mrestrict in Hzi. destruct (H1 _); [discriminate | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma vis_mono : forall E cs cs' model a,
  (forall z, in_allow E cs z = true -> in_allow E cs' z = true) ->
  vis E cs model a = true -> vis E cs' model a = true.
Proof.
  intros E cs cs' model a Hm H. unfold vis in *.
  apply orb_true_iff in H. apply orb_true_iff. destruct H as [H|H]; [left; exact H|]. right.
  apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split; [exact H1|].
  apply orb_true_iff in H2. apply orb_true_iff. destruct H2 as [H2|H2]; [left; exact H2|]. right. apply Hm. exact H2.
Qed.

Lemma in_allow_cons : forall E cs p ss tot ylo eg gh ab brk fd tid z,
  in_allow E cs z = true -> in_allow E (ACS ss (a_maps cs) tot ylo eg (p :: a_vis cs) gh ab brk fd tid) z = true.
Proof.
  intros. unfold in_allow, in_vis, in_sh in *. cbn [a_vis existsb].
  apply orb_true_iff in H. apply orb_true_iff.
  destruct H as [H|H]; [left|right]; apply orb_true_iff; right; exact H.
Qed.

Lemma hid_cons_sub : forall E cs p model a ss tot ylo eg gh ab brk fd tid,
  hid E (ACS ss (a_maps cs) tot ylo eg (p :: a_vis cs) gh ab brk fd tid) model a = true -> hid E cs model a = true.
Proof.
  intros E cs p model a ss tot ylo eg gh ab brk fd tid H. unfold hid in *.
  apply orb_true_iff in H. apply orb_true_iff. destruct H as [H|H]; [left; exact H|]. right.
  apply negb_true_iff in H. apply negb_true_iff.
  destruct (vis E cs model a) eqn:Hv; [|reflexivity].
  rewrite (vis_mono E cs _ model a (fun z Hz => in_allow_cons E cs p ss tot ylo eg gh ab brk fd tid z Hz) Hv) in H. discriminate.
Qed.

Lemma A_bytes_app : forall l1 l2, A_bytes (l1 ++ l2) = A_bytes l1 + A_bytes l2.
Proof. intros l1 l2. induction l1; cbn [A_bytes app]; [lia|]. rewrite IHl1. lia. Qed.

Lemma page_allowedb_app_r : forall l1 l2 p, page_allowedb l2 p = true -> page_allowedb (l1 ++ l2) p = true.
Proof. intros. unfold page_allowedb in *. rewrite existsb_app, H. apply orb_true_r. Qed.

Lemma MInv_app : forall l1 l2 m, MInv l2 m -> eager_used m + A_bytes (l1 ++ l2) <= vm_limit (m_vmmaps m) -> MInv (l1 ++ l2) m.
Proof.
  intros l1 l2 m [N1 N2 N3 N4 N5] Hb. constructor; try assumption.
  intros p Hp. apply page_allowedb_app_r. apply N3. exact Hp.
Qed.

Lemma in_ivs_true : forall z l, in_ivs z l = true <-> exists iv, In iv l /\ bv_unsigned (fst iv) <= z < bv_unsigned (fst iv) + bv_unsigned (snd iv).
Proof.
  intros z l. unfold in_ivs. rewrite existsb_exists. split.
  - intros [iv [Hin Hb]]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. eauto.
  - intros [iv [Hin Hb]]. exists iv. split; [exact Hin|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma split_lit_denot : forall E e b k, split_lit e = (b, k) ->
  edenot E e = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
Proof.
  intros E e b k H.
  assert (G : forall e' : expr, edenot E e' = Z_to_bv 64 (bv_unsigned (edenot E e') + 0)).
  { intros e'. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
  unfold split_lit in H.
  destruct e; try (injection H as <- <-; apply G).
  - injection H as <- <-. cbn [edenot]. rewrite u64_lit by (unfold two64; lia). rewrite Z.add_0_l. reflexivity.
  - lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; apply G).
    lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; apply G).
    injection H as <- <-. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma flat_x_sound : forall E M k b off n,
  know_ok SEGS E M k -> flat_x k b off n = true ->
  0 <= estart E (SA b off) /\ estart E (SA b off) + bv_unsigned (edenot E n) <= 2 ^ 64 /\ 0 < bv_unsigned (edenot E n).
Proof.
  intros E M k b off n HK H. unfold flat_x in H.
  destruct (base_range k b) as [[lo hi]|] eqn:Hb; [|discriminate].
  destruct (xlo k n) as [nl|] eqn:Hnl; [|discriminate]. destruct (xhi k n) as [nh|] eqn:Hnh; [|discriminate].
  apply andb_prop in H as [H Hn]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in Hn. unfold two64 in H2.
  pose proof (base_range_sound SEGS E M k b lo hi HK Hb). pose proof (xlo_sound SEGS E M k n nl HK Hnl). pose proof (xhi_sound SEGS E M k n nh HK Hnh).
  unfold estart. cbn [a_base a_off]. lia.
Qed.

(* [comment removed for export] *)
Lemma on_stack_side_sound : forall E M k b off,
  know_ok SEGS E M k -> on_stack_side k b off = true ->
  uE E e_sp0 - STK_BELOW <= estart E (SA b off).
Proof.
  intros E M k b off HK H. unfold on_stack_side in H. unfold estart; cbn [a_base a_off].
  destruct (expr_eqb b e_sp0) eqn:Eb.
  - apply expr_eqb_eq in Eb. subst b. apply Z.leb_le in H. unfold uE. lia.
  - destruct (shares_var b e_sp0); [|discriminate].
    pose proof (lin_ge0_sound SEGS E M k _ _ HK H) as L. cbn [xt_den] in L. unfold uE. lia.
Qed.
Lemma stack_side_start : forall E, estart E stack_side = uE E e_sp0 - STK_BELOW.
Proof. intros E. reflexivity. Qed.
Lemma hull_side_start : forall E, estart E (hull_side A) = img_lo A.
Proof. intros E. unfold estart, hull_side. cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia. Qed.
Lemma lit_side_start : forall E mb, estart E (lit_side mb) = bv_unsigned (edenot E mb).
Proof.
  intros E mb. unfold lit_side. destruct mb as [z| | | | | | |]; try (unfold estart; cbn [a_base a_off]; lia).
  destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:Hz; unfold estart; cbn [a_base a_off edenot]; [|lia].
  apply andb_prop in Hz as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in H2.
  rewrite !u64_lit by lia. lia.
Qed.

Lemma u_of_split : forall E e b k, split_lit e = (b, k) ->
  0 <= estart E (SA b k) < 2 ^ 64 -> bv_unsigned (edenot E e) = estart E (SA b k).
Proof.
  intros E e b k Hs Hr. rewrite (split_lit_denot E e b k Hs). unfold estart in *. cbn [a_base a_off] in *.
  apply u64_lit. lia.
Qed.

Lemma pageup_pagedown_gap : forall a b, a <= b -> pageup b - pagedown a <= b - a + 8190.
Proof.
  intros a b H. unfold pageup, pagedown.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
Lemma maps_match_exact : forall E ms l,
  no_fog ms = true -> (maps_match E ms l <-> l = map (amap_den E) ms).
Proof.
  intros E ms. induction ms as [|m ms IH]; intros l Hnf; cbn [maps_match map].
  - tauto.
  - cbn [no_fog forallb] in Hnf. apply andb_prop in Hnf as [Hm Hr]. apply negb_true_iff in Hm. rewrite Hm.
    split.
    + intros (l' & -> & Hm'). f_equal. apply (proj1 (IH l' Hr)). exact Hm'.
    + intros ->. exists (map (amap_den E) ms). split; [reflexivity|]. apply (proj2 (IH _ Hr)). reflexivity.
Qed.

Lemma maps_match_In : forall E ms l m,
  maps_match E ms l -> In m ms -> is_fog m = false -> In (amap_den E m) l.
Proof.
  intros E ms. induction ms as [|m0 ms IH]; intros l m HM Hin Hf; [destruct Hin|].
  cbn [maps_match] in HM. destruct Hin as [<-|Hin].
  - rewrite Hf in HM. destruct HM as (l' & -> & _). left. reflexivity.
  - destruct (is_fog m0).
    + destruct HM as [HM|(iv & l' & -> & _ & HM)]; [exact (IH _ _ HM Hin Hf) | right; exact (IH _ _ HM Hin Hf)].
    + destruct HM as (l' & -> & HM). right. exact (IH _ _ HM Hin Hf).
Qed.

Lemma in_ivs_maps_match : forall E ms l m z,
  maps_match E ms l -> In m ms -> is_fog m = false ->
  bv_unsigned (edenot E (am_base m)) <= z < bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) ->
  in_ivs z l = true.
Proof.
  intros E ms l m z HM Hin Hf Hz. apply (proj2 (in_ivs_true z _)). exists (amap_den E m).
  split; [exact (maps_match_In E ms l m HM Hin Hf) | exact Hz].
Qed.

Lemma maps_match_cons : forall E ms l b n k,
  is_tok_kind k = false -> maps_match E ms l ->
  maps_match E (AM b n k :: ms) ((edenot E b, edenot E n) :: l).
Proof.
  intros E ms l b n k Hk HM. cbn [maps_match]. unfold is_fog. cbn [am_kind]. rewrite Hk. exists l. split; [reflexivity | exact HM].
Qed.

Lemma maps_match_length : forall E ms l, maps_match E ms l -> (length l <= length ms)%nat.
Proof.
  intros E ms. induction ms as [|m ms IH]; intros l HM; cbn [maps_match] in HM.
  - subst l. cbn. lia.
  - cbn [length]. destruct (is_fog m).
    + destruct HM as [HM|(iv & l' & -> & _ & HM)]; [pose proof (IH _ HM); lia | cbn; pose proof (IH _ HM); lia].
    + destruct HM as (l' & -> & HM). cbn. pose proof (IH _ HM). lia.
Qed.

(* [comment removed for export] *)
Lemma maps_match_elem : forall E ms l iv,
  maps_match E ms l -> In iv l ->
  exists m, In m ms /\ ((is_fog m = false /\ iv = amap_den E m) \/ (is_fog m = true /\ bv_unsigned (snd iv) <= uE E (am_len m))).
Proof.
  intros E ms. induction ms as [|m ms IH]; intros l iv HM Hin; cbn [maps_match] in HM.
  - subst l. destruct Hin.
  - destruct (is_fog m) eqn:Hf.
    + destruct HM as [HM|(iv0 & l' & -> & Hsz & HM)].
      * destruct (IH _ _ HM Hin) as (m' & Hm' & H'). exists m'. split; [right; exact Hm' | exact H'].
      * destruct Hin as [<-|Hin].
        -- exists m. split; [left; reflexivity|]. right. split; [exact Hf | exact Hsz].
        -- destruct (IH _ _ HM Hin) as (m' & Hm' & H'). exists m'. split; [right; exact Hm' | exact H'].
    + destruct HM as (l' & -> & HM). destruct Hin as [<-|Hin].
      * exists m. split; [left; reflexivity|]. left. split; [exact Hf | reflexivity].
      * destruct (IH _ _ HM Hin) as (m' & Hm' & H'). exists m'. split; [right; exact Hm' | exact H'].
Qed.

(* [comment removed for export] *)
Lemma maps_match_rekind : forall E ms l (f : amap -> amap),
  (forall m, am_base (f m) = am_base m /\ am_len (f m) = am_len m /\ is_fog (f m) = is_fog m) ->
  maps_match E ms l -> maps_match E (map f ms) l.
Proof.
  intros E ms. induction ms as [|m ms IH]; intros l f Hf HM; cbn [maps_match map] in *; [exact HM|].
  destruct (Hf m) as (Hb & Hn & Hk). rewrite Hk. unfold uE, amap_den in *. rewrite Hb, Hn.
  destruct (is_fog m).
  - destruct HM as [HM|(iv & l' & -> & Hsz & HM)]; [left; exact (IH _ f Hf HM) | right].
    exists iv, l'. split; [reflexivity|]. split; [exact Hsz | exact (IH _ f Hf HM)].
  - destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | exact (IH _ f Hf HM)].
Qed.

(* [comment removed for export] *)
Lemma filter_all_true : forall {T} (f : T -> bool) l, (forall x, In x l -> f x = true) -> List.filter f l = l.
Proof.
  intros T f l H. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite (H x (or_introl eq_refl)).
  rewrite IH by (intros y Hy; apply H; right; exact Hy). reflexivity.
Qed.

Lemma aluop_eqb_refl' : forall o, aluop_eqb o o = true.
Proof. intros []; reflexivity. Qed.
Lemma mulop_eqb_refl' : forall o, mulop_eqb o o = true.
Proof. intros []; reflexivity. Qed.
Lemma expr_eqb_refl' : forall e, expr_eqb e e = true.
Proof.
  induction e; cbn; rewrite ?aluop_eqb_refl', ?mulop_eqb_refl', ?IHe1, ?IHe2, ?IHe, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.
Lemma amap_eqb_refl' : forall m, amap_eqb m m = true.
Proof. intros [b l k]. unfold amap_eqb. cbn. rewrite !expr_eqb_refl'. destruct k; reflexivity. Qed.

Lemma map_remove_notin' : forall l (a : word),
  (forall b sz, In (b, sz) l -> b <> a) -> map_remove l a = l.
Proof.
  induction l as [|[b sz] l IH]; intros a H; [reflexivity|].
  unfold map_remove in *. cbn [List.filter fst]. rewrite (bv_eqb_neq b a) by (apply (H b sz); left; reflexivity). cbn [negb].
  f_equal. apply IH. intros b' s' Hin. apply (H b' s'). right. exact Hin.
Qed.

Lemma maps_match_remove : forall E ms l m,
  maps_match E ms l -> In m ms -> is_fog m = false ->
  List.NoDup l ->
  (forall iv, In iv l -> fst iv = edenot E (am_base m) -> iv = amap_den E m) ->
  maps_match E (List.filter (fun m' => negb (amap_eqb m' m)) ms) (map_remove l (edenot E (am_base m))).
Proof.
  intros E ms. induction ms as [|m0 ms IH]; intros l m HM Hin Hf Hnd Huniq; [destruct Hin|].
  cbn [maps_match] in HM. cbn [List.filter].
  destruct (amap_eqb m0 m) eqn:Heq.
  - (* [comment removed for export] *)
    apply amap_eqb_eq in Heq. subst m0.
    rewrite Hf in HM. destruct HM as (l' & -> & HM). cbn [negb].
    unfold map_remove. cbn [List.filter amap_den fst]. rewrite bv_eqb_refl. cbn [negb].
    inversion Hnd as [|x l0 Hnotin Hnd']; subst.
    assert (Hnotin' : ~ In m ms).
    { intros Hm. apply Hnotin. exact (maps_match_In E ms l' m HM Hm Hf). }
    rewrite (filter_all_true (fun m' => negb (amap_eqb m' m)) ms).
    2:{ intros x Hx. destruct (amap_eqb x m) eqn:Ex; [|reflexivity]. apply amap_eqb_eq in Ex. subst x. exfalso. exact (Hnotin' Hx). }
    fold (map_remove l' (edenot E (am_base m))). rewrite map_remove_notin'; [exact HM|].
    intros b sz Hbs Hb. apply Hnotin. rewrite <- (Huniq (b, sz) (or_intror Hbs) Hb). exact Hbs.
  - (* [comment removed for export] *)
    destruct Hin as [->|Hin]; [rewrite amap_eqb_refl' in Heq; discriminate|].
    cbn [negb maps_match].
    destruct (is_fog m0) eqn:Hf0.
    + destruct HM as [HM|(iv & l' & -> & Hsz & HM)].
      * left. exact (IH _ _ HM Hin Hf Hnd Huniq).
      * inversion Hnd as [|x l0 Hnotin Hnd']; subst.
        assert (Hne : bv_eqb (fst iv) (edenot E (am_base m)) = false).
        { apply bv_eqb_neq. intros Hb. apply Hnotin. rewrite (Huniq iv (or_introl eq_refl) Hb).
          exact (maps_match_In E ms l' m HM Hin Hf). }
        unfold map_remove. cbn [List.filter]. rewrite Hne. cbn [negb]. fold (map_remove l' (edenot E (am_base m))).
        right. exists iv, (map_remove l' (edenot E (am_base m))). split; [reflexivity|]. split; [exact Hsz|].
        apply (IH _ _ HM Hin Hf Hnd'). intros x Hx. apply Huniq. right. exact Hx.
    + destruct HM as (l' & -> & HM).
      inversion Hnd as [|x l0 Hnotin Hnd']; subst.
      assert (Hne : bv_eqb (fst (amap_den E m0)) (edenot E (am_base m)) = false).
      { apply bv_eqb_neq. intros Hb. apply Hnotin. rewrite (Huniq _ (or_introl eq_refl) Hb).
        exact (maps_match_In E ms l' m HM Hin Hf). }
      unfold map_remove. cbn [List.filter]. rewrite Hne. cbn [negb]. fold (map_remove l' (edenot E (am_base m))).
      exists (map_remove l' (edenot E (am_base m))). split; [reflexivity|].
      apply (IH _ _ HM Hin Hf Hnd'). intros x Hx. apply Huniq. right. exact Hx.
Qed.

Lemma in_ivs_map_den : forall E ms m z,
  In m ms ->
  bv_unsigned (edenot E (am_base m)) <= z < bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) ->
  in_ivs z (map (amap_den E) ms) = true.
Proof.
  intros E ms m z Hin Hz. apply (proj2 (in_ivs_true z _)). exists (amap_den E m). split; [apply in_map; exact Hin | exact Hz].
Qed.

Lemma existsb_false_forall : forall {T} (f : T -> bool) l, (forall x, In x l -> f x = false) -> existsb f l = false.
Proof.
  intros T f l H. induction l as [|x l IH]; [reflexivity|]. cbn [existsb].
  rewrite (H x (or_introl eq_refl)). cbn [orb]. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lit_lazy_iv_sem : forall E m b l, lit_lazy_iv m = Some (b, l) ->
  is_fog m = false /\ (am_kind m = KRWLAZY \/ am_kind m = KNONELAZY)
  /\ uE E (am_base m) = b /\ uE E (am_len m) = l /\ 0 <= b /\ 0 < l /\ b + l < two64.
Proof.
  intros E m b l H. unfold lit_lazy_iv in H.
  destruct (am_kind m) eqn:Hk; try discriminate;
    destruct (am_base m) as [zb| | | | | | |] eqn:Hb; try discriminate; destruct (am_len m) as [zl| | | | | | |] eqn:Hl; try discriminate;
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end; injection H as <- <-;
    apply andb_prop in Hc as [Hc H3]; apply andb_prop in Hc as [H1 H2];
    apply Z.leb_le in H1; apply Z.ltb_lt in H2; apply Z.ltb_lt in H3; unfold two64 in *;
    (split; [unfold is_fog, is_tok_kind; rewrite Hk; reflexivity|]); (split; [auto|]);
    unfold uE; cbn [edenot]; rewrite !u64_lit by lia; repeat split; lia.
Qed.

Lemma lit_rwlazy_cover_sound : forall E ms lo hi z,
  lit_rwlazy_cover ms lo hi = true -> lo <= z < hi ->
  exists m, In m ms /\ is_fog m = false /\ am_kind m = KRWLAZY
            /\ uE E (am_base m) <= z < uE E (am_base m) + uE E (am_len m).
Proof.
  intros E ms lo hi z H Hz. unfold lit_rwlazy_cover in H. apply existsb_exists in H as [m [Hin Hm]].
  destruct (am_kind m) eqn:Hk; try discriminate.
  destruct (lit_lazy_iv m) as [[b l]|] eqn:Hl; [|discriminate].
  apply andb_prop in Hm as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  destruct (lit_lazy_iv_sem E m b l Hl) as (F1 & _ & F3 & F4 & _).
  exists m. rewrite F3, F4. repeat split; try assumption. all: lia.
Qed.

(* [comment removed for export] *)
Lemma shadow_of_denot : forall E M k b n sb sk sn,
  know_ok SEGS E M k -> shadow_of A k b n = (sb, sk, sn) ->
  uE E b / 8 + shadow_off A < 2 ^ 64 -> 0 <= estart E (SA sb sk) < 2 ^ 64 ->
  estart E (SA sb sk) = shadow_off A + uE E b / 8 /\ elenZ E sn = uE E n / 8.
Proof.
  intros E M k b n sb sk sn HK Hsh Hnw Hfl. unfold estart in Hfl. cbn [a_base a_off] in Hfl. unfold shadow_of in Hsh.
  destruct (split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hss. injection Hsh as -> -> <-.
  pose proof SHADOW_ok as SO. unfold shadow_ok in SO. pose proof (u64_range (edenot E b)) as Rb.
  split.
  - pose proof (split_lit_denot E _ sb sk Hss) as D. unfold eadd in D. rewrite mkAlu_denot in D. cbn [edenot] in D.
    apply (f_equal bv_unsigned) in D. rewrite u_add64 in D.
    rewrite (mkSrl_denot SEGS E _ k b 3 (Z_to_bv 64 3) HK) in D by (rewrite u64_lit by lia; reflexivity).
    rewrite u_srl64 in D. unfold estart. cbn [a_base a_off]. unfold uE in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite !u64_lit in D by lia. change (2 ^ (3 mod 64)) with 8 in D.
    rewrite (Z.mod_small (bv_unsigned (edenot E b) / 8 + shadow_off A)) in D by lia. lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - unfold elenZ, uE. rewrite (mkSrl_denot SEGS E _ k n 3 (Z_to_bv 64 3) HK) by (rewrite u64_lit by lia; reflexivity).
    rewrite u_srl64. rewrite u64_lit by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma band_host_sound : forall E cs R FULL model b bb bk n sb sk sn,
  cs_ok E cs R FULL model -> split_lit b = (bb, bk) -> shadow_of A (kn cs) b n = (sb, sk, sn) ->
  band_host A (kn cs) (a_maps cs) bb bk n sb sk sn = true ->
  forall z, estart E (SA sb sk) <= z < estart E (SA sb sk) + elenZ E sn ->
    exists m, In m (a_maps cs) /\ is_fog m = false /\ am_kind m = KRWLAZY
              /\ uE E (am_base m) <= z < uE E (am_base m) + uE E (am_len m).
Proof.
  intros E cs R FULL model b bb bk n sb sk sn HC Hsplit Hsh H z Hz.
  pose proof (co_know _ _ _ _ _ HC) as HK.
  unfold band_host in H. destruct (shadow_band A (a_maps cs)) as [[L0 L3]|] eqn:HB; [|discriminate].
  destruct (base_range (kn cs) bb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
  destruct (xhi (kn cs) n) as [nh|] eqn:Hnh; [|discriminate].
  apply andb_prop in H as [H Hhi]. apply andb_prop in H as [H Hlo]. apply andb_prop in H as [H Hap].
  apply andb_prop in H as [H Hfl]. apply andb_prop in H as [H Htop]. apply andb_prop in H as [H Hpos]. apply andb_prop in H as [H H64].
  apply andb_prop in H as [H H03]. apply andb_prop in H as [H H0]. apply andb_prop in H as [H8a H8b].
  apply Z.eqb_eq in H8a. apply Z.eqb_eq in H8b. apply Z.ltb_lt in H0. apply Z.ltb_lt in H03. apply Z.ltb_lt in H64.
  apply Z.leb_le in Hpos. apply Z.leb_le in Htop.
  pose proof (base_range_sound SEGS E _ (kn cs) bb blo bhi HK Hbr) as [Rb1 Rb2].
  pose proof (xhi_sound SEGS E _ (kn cs) n nh HK Hnh) as Rn. pose proof (u64_range (edenot E n)) as Rn0.
  assert (Ub : uE E b = estart E (SA bb bk)).
  { unfold uE. apply (u_of_split E b bb bk Hsplit). unfold estart. cbn [a_base a_off]. unfold ATOP_MAX in Htop. lia. }
  unfold estart in Ub. cbn [a_base a_off] in Ub.
  pose proof SHADOW_ok as SO. unfold shadow_ok in SO.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  destruct (flat_x_sound E _ (kn cs) sb sk sn HK Hfl) as (Fs1 & Fs2 & Fs3).
  destruct (shadow_of_denot E _ (kn cs) b n sb sk sn HK Hsh ltac:(unfold ATOP_MAX in Htop; lia) ltac:(lia)) as [HS0 Hsn].
  rewrite HS0, Hsn in Hz.
  pose proof (ranges_apart_x_sound SEGS E _ (kn cs) _ _ _ _ _ _ HK Hap) as AP.
  unfold estart, elenZ in AP. cbn [a_base a_off edenot] in AP. rewrite !u64_lit in AP by (unfold two64 in H64; lia).
  rewrite <- Ub in AP. unfold uE in *.
  destruct AP as [AP|AP].
  - (* [comment removed for export] *)
    destruct (lit_rwlazy_cover_sound E (a_maps cs) _ _ z Hhi) as (m & Hm); [|exists m; exact Hm].
    unfold ATOP_MAX in *. split; [|lia].
    assert (L3 / 8 <= bv_unsigned (edenot E b) / 8) by (apply Z.div_le_mono; lia). lia.
  - (* [comment removed for export] *)
    destruct (lit_rwlazy_cover_sound E (a_maps cs) _ _ z Hlo) as (m & Hm); [|exists m; exact Hm].
    split; [lia|].
    assert (bv_unsigned (edenot E b) / 8 + bv_unsigned (edenot E n) / 8 <= L0 / 8) by lia. lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
Lemma shadow_host_sound : forall E cs R FULL model b n sb sk sn,
  cs_ok E cs R FULL model -> shadow_of A (kn cs) b n = (sb, sk, sn) ->
  shadow_host A (kn cs) (a_maps cs) b n = true ->
  forall z, estart E (SA sb sk) <= z < estart E (SA sb sk) + elenZ E sn ->
    exists m, In m (a_maps cs) /\ is_fog m = false /\ am_kind m = KRWLAZY
              /\ uE E (am_base m) <= z < uE E (am_base m) + uE E (am_len m).
Proof.
  intros E cs R FULL model b n sb sk sn HC Hsh H z Hz. pose proof (co_know _ _ _ _ _ HC) as HK.
  unfold shadow_host in H. rewrite Hsh in H.
  destruct (find_containing (kn cs) (a_maps cs) [KRWLAZY] sb sk sn) as [m|] eqn:Hf.
  - unfold find_containing in Hf. apply find_some in Hf as [Hmin Hmb]. apply andb_prop in Hmb as [Hkind Hins].
    apply andb_prop in Hkind as [Hnf Hkind]. apply negb_true_iff in Hnf.
    cbn [existsb] in Hkind. rewrite orb_false_r in Hkind. apply mkind_eqb_eq in Hkind.
    pose proof (xinside_sound SEGS E _ (kn cs) sb sk sn (am_base m) 0 (am_len m) HK Hins) as [I1 I2].
    unfold estart, elenZ in I1, I2. cbn [a_base a_off] in I1, I2. unfold estart in Hz. cbn [a_base a_off] in Hz.
    exists m. unfold uE, elenZ in *. repeat split; try assumption; lia.
  - destruct (plain A); [discriminate|]. destruct (split_lit b) as [bb bk] eqn:Hsplit.
    exact (band_host_sound E cs R FULL model b bb bk n sb sk sn HC Hsplit Hsh H z Hz).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pow2_divide_4096 : forall k e E M, know_ok SEGS E M k -> (12 <=? ealign k e) = true -> (4096 | bv_unsigned (edenot E e)).
Proof.
  intros k e E M HK H. apply Z.leb_le in H. destruct (ealign_sound SEGS E M k e HK) as [_ D].
  eapply Z.divide_trans; [|exact D]. change 4096 with (2 ^ 12). apply pow2_divide_le. lia.
Qed.
(* [comment removed for export] *)
Lemma ends_below_stack_sound : forall E M k bb bk n,
  know_ok SEGS E M k -> ends_below_stack k bb bk n = true ->
  0 <= estart E (SA bb bk) ->
  estart E (SA bb bk) + elenZ E n <= uE E e_sp0 - STK_BELOW.
Proof.
  intros E M k bb bk n HK H Hfl. unfold ends_below_stack in H.
  destruct (base_range k bb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
  destruct (xhi k n) as [nh|] eqn:Hnh; [|discriminate].
  destruct (xlo k e_sp0) as [slo|] eqn:Hslo; [|discriminate].
  destruct (Z.ltb (bhi + bk + nh) (slo - STK_BELOW + STK_LEN)) eqn:Ht; [|discriminate]. apply Z.ltb_lt in Ht.
  pose proof (base_range_sound SEGS E M k bb blo bhi HK Hbr) as [_ Bh]. pose proof (xhi_sound SEGS E M k n nh HK Hnh) as Nh.
  pose proof (xlo_sound SEGS E M k e_sp0 slo HK Hslo) as Sl.
  apply existsb_exists in H as [K [HinK HK1]]. unfold is_f3_for in HK1.
  destruct K as [| | | | | | |[sb so] [sl| | | | | | |] [c2 o2] n2| |]; try discriminate.
  destruct (expr_eqb sb e_sp0 && Z.eqb so (- STK_BELOW) && Z.eqb sl STK_LEN)%bool eqn:Hm; [|discriminate].
  apply andb_prop in Hm as [Hm Hsl]. apply andb_prop in Hm as [Hsb Hso].
  apply expr_eqb_eq in Hsb. apply Z.eqb_eq in Hso. apply Z.eqb_eq in Hsl. subst sb so sl.
  pose proof (sub_itv_x_sound SEGS E M k bb bk n (SA c2 o2) n2 HK HK1) as [S1 S2].
  pose proof (proj1 (Forall_forall _ _) HK _ HinK) as KK. cbn [kentry_ok] in KK.
  pose proof (u64_range (edenot E n)) as Rn. pose proof (u64_range (edenot E n2)) as Rn2.
  unfold estart, elenZ, uE in *. cbn [a_base a_off] in *. rewrite edenot_lit, u64_lit in KK by (unfold STK_LEN; lia).
  unfold STK_BELOW, STK_LEN in *. lia.
Qed.
(* [comment removed for export] *)
Lemma foot_apart_sound : forall E M k bb bk n pbase,
  know_ok SEGS E M k -> foot_apart A k bb bk n pbase = true ->
  0 <= estart E (SA bb bk) < 2 ^ 64 ->
  estart E (SA bb bk) + elenZ E n <= uE E pbase.
Proof.
  intros E M k bb bk n pbase HK H Hfl. unfold foot_apart in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  destruct (ends_below_stack k bb bk n) eqn:HE; [|discriminate]. rename H into L2.
  apply andb_prop in Hc as [Hc A3]. apply andb_prop in Hc as [Hc A2]. apply andb_prop in Hc as [_ A1].
  pose proof (pow2_divide_4096 k _ E M HK A1) as D1. pose proof (pow2_divide_4096 k _ E M HK A2) as D2.
  pose proof (pow2_divide_4096 k _ E M HK A3) as D3.
  pose proof (ends_below_stack_sound E M k bb bk n HK HE ltac:(lia)) as G1. pose proof (lin_ge0_sound SEGS E M k _ _ HK L2) as G2.
  cbn [xt_den] in G2.
  assert (U : bv_unsigned (edenot E (eaddz bb bk)) = estart E (SA bb bk)).
  { unfold eaddz. rewrite mkAlu_denot, u_add64, edenot_lit, u_lit64. unfold estart in *; cbn [a_base a_off] in *. unfold two64.
    pose proof (u64_range (edenot E bb)) as Rbb.
    assert (K1 : (bk mod 2 ^ 64 = bk /\ 0 <= bk) \/ (bk mod 2 ^ 64 = bk + 2 ^ 64 /\ bk < 0)).
    { destruct (Z_lt_le_dec bk 0) as [Hn|Hp].
      - right. split; [|lia]. rewrite <- (Z.mod_add bk 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
      - left. split; [|lia]. apply Z.mod_small. lia. }
    destruct K1 as [[-> Hk]|[-> Hk]]; [apply Z.mod_small; lia|].
    rewrite Z.add_assoc. rewrite <- (Z.mod_add _ (-1) (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
  rewrite U in D1. unfold estart, elenZ, uE in *. cbn [a_base a_off] in *.
  destruct D1 as [q1 Q1]. destruct D2 as [q2 Q2]. destruct D3 as [q3 Q3]. unfold STK_BELOW in *. lia.
Qed.

Lemma vis_add_sound : forall E cs b n k cs2 R FULL model,
  vis_add A LIMIT cs b n k = Some cs2 ->
  cs_ok E cs R FULL model ->
  know_ok SEGS E (Mr E cs2 model FULL) k ->
  cs_ok E cs2 R FULL model.
Proof.
  intros E cs b n k cs2 R FULL model Hv HC HKk.
  rewrite vis_add_eq in Hv. (* [comment removed for export] *) unfold vis_add_ref in Hv.
  destruct (split_lit b) as [bb bk] eqn:Hsplit.
  destruct (shadow_of A (kn cs) b n) as [[sb sk] sn] eqn:Hsh.
  destruct (xhi (kn cs) n) as [nhi|] eqn:Hnhi; [|discriminate].
  match type of Hv with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection Hv as <-.
  apply andb_prop in Hc as [Hc Hbudget]. apply andb_prop in Hc as [Hc Hapg]. apply andb_prop in Hc as [Hc Hapart]. apply andb_prop in Hc as [Hc Hvn].
  apply andb_prop in Hc as [Hc Hvb]. apply andb_prop in Hc as [Hc Hflat]. apply andb_prop in Hc as [Halb Haln].
  apply Z.leb_le in Hbudget.
  pose proof (co_know _ _ _ _ _ HC) as HK.
  pose proof (xhi_sound SEGS E _ (kn cs) n nhi HK Hnhi) as Hnhi'.
  destruct (flat_x_sound E _ (kn cs) bb bk n HK Hflat) as (Fb1 & Fb2 & Fb3).
  pose proof (u_of_split E b bb bk Hsplit ltac:(lia)) as Ub.
  set (cs2 := ACS _ _ _ _ _ _ _ _ _ _ _).
  (* [comment removed for export] *)
  assert (SUB : forall a, hid E cs2 model a = true -> hid E cs model a = true).
  { intros a. apply hid_cons_sub. }
  (* [comment removed for export] *)
  assert (HA : allowA E cs2 = allow1 E (b, n) ++ allowA E cs) by reflexivity.
  assert (Hcost : A_bytes (allow1 E (b, n)) <= vis_cost nhi).
  { unfold allow1, vis_cost. cbn [A_bytes fst snd]. unfold sh_lo, sh_hi. cbn [fst snd].
    pose proof (u64_range (edenot E b)) as Rb. pose proof (u64_range (edenot E n)) as Rn. unfold uE in *.
    pose proof (pageup_pagedown_gap (bv_unsigned (edenot E b)) (bv_unsigned (edenot E b) + bv_unsigned (edenot E n)) ltac:(lia)) as G1.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    pose proof (pageup_pagedown_gap (shadow_off A + bv_unsigned (edenot E b) / 8)
                  (shadow_off A + (bv_unsigned (edenot E b) + bv_unsigned (edenot E n)) / 8) ltac:(lia)) as G2.
    assert (G3 : (bv_unsigned (edenot E b) + bv_unsigned (edenot E n)) / 8 - bv_unsigned (edenot E b) / 8 <= nhi / 8 + 1) by lia.
    lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  (* [comment removed for export] *)
  assert (HKsh : know_ok SEGS E (Mr E cs2 model FULL) (shadow_facts A (kn cs) (a_maps cs) b n)).
  { unfold shadow_facts. rewrite Hsh.
    destruct (shadow_host A (kn cs) (a_maps cs) b n) eqn:Hhost; [|constructor].
    pose proof (shadow_host_sound E cs R FULL model b n sb sk sn HC Hsh Hhost) as HOST.
    set (S0 := estart E (SA sb sk)) in *.
    pose proof SHADOW_ok as SO. unfold shadow_ok in SO. pose proof (u64_range (edenot E b)) as Rb.
    pose proof (u64_range (edenot E n)) as Rn. pose proof (u64_range (edenot E sn)) as Rsn.
    (* [comment removed for export] *)
    assert (Haln8 : (8 | bv_unsigned (edenot E n))).
    { pose proof (ealign_sound SEGS E _ (kn cs) n HK) as [EA1 EA2]. apply Z.leb_le in Haln.
      eapply Z.divide_trans; [|exact EA2]. change 8 with (2 ^ 3). apply pow2_divide_le. lia. }
    (* [comment removed for export] *)
    assert (Hne : 0 < elenZ E sn /\ S0 = shadow_off A + bv_unsigned (edenot E b) / 8 /\ elenZ E sn = bv_unsigned (edenot E n) / 8
                  /\ 0 <= S0 /\ S0 + elenZ E sn < 2 ^ 64).
    { (* [comment removed for export] *)
      assert (Usn : elenZ E sn = bv_unsigned (edenot E n) / 8).
      { unfold shadow_of in Hsh. destruct (split_lit (eadd (mkSrl (kn cs) b 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hss.
        injection Hsh as E1 E2 E3. rewrite <- E3. unfold elenZ.
        rewrite (mkSrl_denot SEGS E _ (kn cs) n 3 (Z_to_bv 64 3) HK) by (rewrite u64_lit by lia; reflexivity).
        rewrite u_srl64. rewrite u64_lit by lia. reflexivity. }
      assert (Hpos : 0 < elenZ E sn).
      { rewrite Usn. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
      destruct (HOST S0 ltac:(lia)) as (m0 & Hm0 & Hnf0 & Hk0 & Hz0).
      assert (Hmv0 : In (amap_den E m0) (vm_maps (m_vmmaps model))) by (eapply maps_match_In; [exact (co_maps _ _ _ _ _ HC) | exact Hm0 | exact Hnf0]).
      pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ HC) _ Hmv0) as (_ & _ & _ & BT0 & _). cbn [amap_den fst snd] in BT0.
      pose proof (alloc_top_lt (m_vmmaps model)) as ATL. unfold two_pow_64 in ATL. unfold uE in Hz0.
      destruct (HOST (S0 + elenZ E sn - 1) ltac:(lia)) as (m1 & Hm1 & Hnf1 & Hk1 & Hz1).
      assert (Hmv1 : In (amap_den E m1) (vm_maps (m_vmmaps model))) by (eapply maps_match_In; [exact (co_maps _ _ _ _ _ HC) | exact Hm1 | exact Hnf1]).
      pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ HC) _ Hmv1) as (_ & _ & _ & BT1 & _). cbn [amap_den fst snd] in BT1.
      unfold uE in Hz1.
      destruct (shadow_of_denot E _ (kn cs) b n sb sk sn HK Hsh) as [HS0 _].
      { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). unfold uE. lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
      { fold S0. pose proof (u64_range (edenot E (am_base m0))). lia. }
      fold S0 in HS0. unfold uE in HS0. pose proof (u64_range (edenot E (am_base m0))). repeat split; try lia. }
    destruct Hne as (Hpos & HS0 & Usn & F0 & F1).
    (* [comment removed for export] *)
    assert (BYTE : forall i, 0 <= i < elenZ E sn -> Mr E cs2 model FULL (Z_to_bv 64 (S0 + i)) = Some (Z_to_bv 8 0)).
    { intros i Hi.
      destruct (HOST (S0 + i) ltac:(lia)) as (m & Hmin & Hnf & Hkind & Zin). unfold uE in Zin.
      set (z := S0 + i) in *.
      assert (Hmv : In (amap_den E m) (vm_maps (m_vmmaps model))) by (eapply maps_match_In; [exact (co_maps _ _ _ _ _ HC) | exact Hmin | exact Hnf]).
      pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ HC) _ Hmv) as (B1 & B2 & B3 & BT & BH). cbn [amap_den fst snd] in B1, B2, B3, BT, BH.
      pose proof (alloc_top_lt (m_vmmaps model)) as ATL. unfold two_pow_64 in ATL.
      assert (Hz : 0 <= z < 2 ^ 64) by lia.
      set (a := Z_to_bv 64 z). assert (Ua : bv_unsigned a = z) by (unfold a; apply u64_lit; exact Hz).
      assert (Hm1 : in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true).
      { eapply in_ivs_maps_match; [exact (co_maps _ _ _ _ _ HC) | exact Hmin | exact Hnf |]. rewrite Ua. exact Zin. }
      destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ HC) m Hmin Hkind a ltac:(rewrite Ua; exact Zin)) as [Hna Hlz].
      (* [comment removed for export] *)
      assert (NP : plain A = false).
      { destruct (plain A) eqn:EP; [|reflexivity]. exfalso. rewrite (co_plain _ _ _ _ _ HC EP) in Hlz. cbn in Hlz. discriminate. }
      rewrite NP in Hapart, Hapg. cbn [orb] in Hapart, Hapg.
      assert (Hargh : argH E a = false).
      { destruct (argH E a) eqn:Ha; [|reflexivity]. exfalso. pose proof (argH_high _ _ Ha).
        (* [comment removed for export] *)
        pose proof (co_isp _ _ _ _ _ HC) as ISP. pose proof (argH_sp0 _ _ _ (co_sinv _ _ _ _ _ HC) Ha) as SP.
        unfold alloc_top, stack_max_size in BT. rewrite ISP in BT. unfold uE in SP. lia. }
      assert (Hvis2 : hid E cs2 model a = false).
      { unfold hid. rewrite Hargh. cbn [orb]. apply negb_false_iff. unfold vis.
        rewrite Hm1, Hna, Hlz. cbn [negb andb].
        assert (Hsh2 : in_sh E cs2 (bv_unsigned a) = true).
        { unfold in_sh. cbn [cs2 a_vis existsb]. unfold sh_lo, sh_hi. cbn [fst snd]. unfold uE.
          rewrite Ua. apply orb_true_iff. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt].
          - lia.
          - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
            Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
        unfold in_allow. rewrite Hsh2. rewrite !orb_true_r. reflexivity. }
      assert (Hhid1 : hid E cs model a = true).
      { unfold hid. rewrite Hargh. cbn [orb]. apply negb_true_iff. unfold vis.
        rewrite Hm1, Hna, Hlz. cbn [negb andb].
        assert (Hh : in_hull A (bv_unsigned a) = false).
        { unfold in_hull. rewrite Ua. apply andb_false_iff. destruct BH as [BH|BH]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia. }
        assert (Hc : ((CEIL <=? bv_unsigned a) && (alloc_top (m_vmmaps model) <=? bv_unsigned a))%bool = false).
        { apply andb_false_iff. right. apply Z.leb_gt. rewrite Ua. lia. }
        rewrite Hh, Hc. cbn [orb].
        (* [comment removed for export] *)
        assert (Hold : in_allow E cs (bv_unsigned a) = false).
        { unfold in_allow. apply orb_false_iff.
          assert (P : forall p, In p (a_vis cs) ->
                    ((uE E (fst p) <=? bv_unsigned a) && (bv_unsigned a <? uE E (fst p) + uE E (snd p)))%bool = false
                    /\ ((sh_lo E p <=? bv_unsigned a) && (bv_unsigned a <? sh_hi E p))%bool = false).
          { intros p Hp. pose proof (proj1 (forallb_forall _ _) Hapart p Hp) as Hpp. cbv beta in Hpp.
            destruct (split_lit (fst p)) as [pb pk] eqn:Hps.
            apply andb_prop in Hpp as [Hpp Hap2]. apply andb_prop in Hpp as [Hpf Hap1].
            destruct (flat_x_sound E _ (kn cs) pb pk (snd p) HK Hpf) as (Fp1 & Fp2 & Fp3).
            pose proof (u_of_split E (fst p) pb pk Hps ltac:(lia)) as Up.
            (* [comment removed for export] *)
            assert (A1 : estart E (SA bb bk) + elenZ E n <= estart E (SA pb pk) \/ estart E (SA pb pk) + elenZ E (snd p) <= estart E (SA bb bk)).
            { apply orb_prop in Hap1 as [Hap1|Hap1].
              - exact (ranges_apart_x_sound SEGS E _ (kn cs) _ _ _ _ _ _ HK Hap1).
              - left. pose proof (u64_range (edenot E b)) as Rb0. pose proof (foot_apart_sound E _ (kn cs) bb bk n (fst p) HK Hap1 ltac:(first [rewrite Ub in Rb0 | rewrite <- Ub in Rb0]; exact Rb0)) as FA.
                unfold uE in FA. rewrite Up in FA. unfold estart; cbn [a_base a_off]. unfold estart in FA; cbn [a_base a_off] in FA. lia. }
            pose proof (ranges_apart_x_sound SEGS E _ (kn cs) _ _ _ _ _ _ HK Hap2) as A2.
            fold S0 in A2. unfold elenZ in A1, A2 |- *. pose proof Usn as U'. unfold elenZ in U'. rewrite ?U' in A2. rewrite ?U' in Hi.
            unfold sh_lo, sh_hi, uE. rewrite Up, Ua. rewrite <- Ub in A1.
            Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
            split; apply andb_false_iff.
            - destruct A2 as [A2|A2]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
            - destruct A1 as [A1|A1]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
            Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
          unfold in_vis, in_sh. split; apply existsb_false_forall; intros p Hp; [exact (proj1 (P p Hp)) | exact (proj2 (P p Hp))]. }
        rewrite Hold. reflexivity. }
      assert (Hgh : in_ghost E cs (bv_unsigned a) = false).
      { unfold in_ghost. apply existsb_false_forall. intros p Hp.
        pose proof (proj1 (forallb_forall _ _) Hapg p Hp) as Hpp. cbv beta in Hpp.
        destruct (split_lit (fst p)) as [pb pk] eqn:Hps.
        apply andb_prop in Hpp as [Hpf Hap2].
        destruct (flat_x_sound E _ (kn cs) pb pk (snd p) HK Hpf) as (Fp1 & Fp2 & Fp3).
        pose proof (u_of_split E (fst p) pb pk Hps ltac:(lia)) as Up.
        pose proof (ranges_apart_x_sound SEGS E _ (kn cs) _ _ _ _ _ _ HK Hap2) as A2.
        fold S0 in A2. unfold elenZ in A2 |- *. pose proof Usn as U'. unfold elenZ in U'. rewrite ?U' in A2. rewrite ?U' in Hi.
        unfold uE. rewrite Up, Ua.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        apply andb_false_iff. destruct A2 as [A2|A2]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
      unfold Mr, mrestrict. rewrite Hvis2.
      apply (co_zero _ _ _ _ _ HC a Hhid1 Hm1 Hna Hlz Hgh). }
    assert (Hfl : flat E (SA sb sk) (elenZ E sn)).
    { unfold flat. fold S0. lia. }
    constructor; [|constructor; [|constructor]].
    - (* [comment removed for export] *) cbn [kentry_ok]. split; [exact Hfl|]. intros d w Hd Hdw.
      pose proof Hfl as (Fl1 & Fl2 & Fl3 & Fl4). fold S0 in Fl1, Fl2, Fl3, Fl4. fold S0.
      assert (ES1 : S0 = estart E (SA sb sk)) by reflexivity.
      destruct w as [|w']; [reflexivity|].
      apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
      intros x Hx. rewrite u64_lit in Hx by lia.
      unfold wview. replace x with (Z_to_bv 64 (S0 + (bv_unsigned x - S0))) by (apply bv_eq; rewrite u64_lit; pose proof (u64_range x); lia).
      rewrite (BYTE (bv_unsigned x - S0)) by lia. discriminate.
    - (* [comment removed for export] *) cbn [kentry_ok]. split; [exact Hfl|]. intros i Hi. fold S0. apply BYTE. exact Hi. }
  destruct HC. constructor; cbn [cs2 a_ss a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know];
    try assumption; try reflexivity.
  - (* [comment removed for export] *)
    apply Forall_app. split; [exact HKsh | exact HKk].
  - (* [comment removed for export] *) rewrite HA, A_bytes_app. lia.
  - (* [comment removed for export] *) rewrite HA. apply MInv_app; [exact co_minv0|]. rewrite A_bytes_app, co_limit0. lia.
  - (* [comment removed for export] *) intros a Ha. apply co_zero0. apply SUB. exact Ha.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ext1 (E : env) (v : nat) (a : word) : env :=
  Env (fun n => if Nat.eqb n v then a else ev E n) (eb E).

Lemma ext1_agree : forall E v a, env_agree v E (ext1 E v a).
Proof.
  intros E v a. split; [|reflexivity]. intros n Hn. cbn [ext1 ev].
  destruct (Nat.eqb_spec n v); [lia | reflexivity].
Qed.
Lemma ext1_at : forall E v a, ev (ext1 E v a) v = a.
Proof. intros. cbn [ext1 ev]. rewrite Nat.eqb_refl. reflexivity. Qed.
Lemma env_agree_le : forall b b' E E', env_agree b' E E' -> (b <= b')%nat -> env_agree b E E'.
Proof. intros b b' E E' [H1 H2] Hle. split; [|exact H2]. intros n Hn. apply H1. lia. Qed.
Lemma env_agree_refl : forall b E, env_agree b E E.
Proof. intros. split; [intros; reflexivity | reflexivity]. Qed.
Lemma env_agree_trans : forall b E1 E2 E3, env_agree b E1 E2 -> env_agree b E2 E3 -> env_agree b E1 E3.
Proof. intros b E1 E2 E3 [A1 B1] [A2 B2]. split; [intros n Hn; rewrite A1 by lia; apply A2; lia | congruence]. Qed.

(* [comment removed for export] *)
Lemma expr_vars_lt_eq : forall b e, AP.expr_vars_lt b e = AxSymRun3.expr_vars_lt b e.
Proof. intros b e. induction e; cbn; try rewrite IHe1, IHe2; try rewrite IHe; reflexivity. Qed.
Lemma kentry_vars_lt_eq : forall b K, AP.kentry_vars_lt b K = AxSymRun3.kentry_vars_lt b K.
Proof.
  intros b K. destruct K as [[? ?] | [? ?] | [? ?] | | | | [? ?] | [? ?] ? [? ?] ?| [? ?] ? ?| [? ?] ?];
    cbn -[AP.expr_vars_lt AxSymRun3.expr_vars_lt]; unfold AP.saddr_vars_lt, AxSymRun3.saddr_vars_lt; cbn [a_base];
    rewrite ?expr_vars_lt_eq; reflexivity.
Qed.
Lemma kn_vars_lt_eq : forall b k, AP.kn_vars_lt b k = AxSymRun3.kn_vars_lt b k.
Proof. intros b k. induction k; cbn [AP.kn_vars_lt AxSymRun3.kn_vars_lt]; [reflexivity|]. rewrite kentry_vars_lt_eq, IHk. reflexivity. Qed.
Lemma sr_vars_lt_eq : forall b sr, AP.sr_vars_lt b sr = AxSymRun3.sr_vars_lt b sr.
Proof. intros b sr. induction sr; cbn [AP.sr_vars_lt AxSymRun3.sr_vars_lt]; [reflexivity|]. rewrite expr_vars_lt_eq, IHsr. reflexivity. Qed.

Lemma edenot_agree' : forall b E E' e, env_agree b E E' -> AP.expr_vars_lt b e = true -> edenot E e = edenot E' e.
Proof. intros. eapply edenot_agree; [eassumption | rewrite <- expr_vars_lt_eq; assumption]. Qed.
(* [comment removed for export] *)
Lemma e_sp0_vars : AP.expr_vars_lt nx0 e_sp0 = true.
Proof.   (* [comment removed for export] *)
  pose proof NX0_min as H. unfold nx0_min_ok in H.
  change (AP.expr_vars_lt nx0 e_sp0) with (Nat.ltb V_S1 nx0 && Nat.ltb V_S2 nx0)%bool.
  unfold V_S1, V_S2. rewrite !(proj2 (Nat.ltb_lt _ _)) by lia. reflexivity.
Qed.
Lemma e_sp0_agree : forall b E E', env_agree b E E' -> (nx0 <= b)%nat -> edenot E' e_sp0 = edenot E e_sp0.
Proof. intros b E E' Hag Hle. symmetry. exact (edenot_agree' nx0 E E' e_sp0 (env_agree_le _ _ _ _ Hag Hle) e_sp0_vars). Qed.
Lemma know_ok_agree' : forall b E E' M k, env_agree b E E' -> AP.kn_vars_lt b k = true -> know_ok SEGS E M k -> know_ok SEGS E' M k.
Proof. intros. eapply know_ok_agree; [eassumption | rewrite <- kn_vars_lt_eq; eassumption | assumption]. Qed.
Lemma regs_ok_agree' : forall b E E' sr R, env_agree b E E' -> AP.sr_vars_lt b sr = true -> regs_ok E sr R -> regs_ok E' sr R.
Proof. intros. eapply regs_ok_agree; [eassumption | rewrite <- sr_vars_lt_eq; eassumption | assumption]. Qed.

(* [comment removed for export] *)

Lemma sd_agree : forall D E E' fs s,
  env_agree nx0 E E' -> shape_vars_lt nx0 s = true -> sd D E fs s = sd D E' fs s.
Proof.
  intros D E E' fs s Hag. induction s; cbn [shape_vars_lt sd]; intros H; try reflexivity.
  - rewrite IHs by exact H. unfold Wp. replace (flat_map (piece_den E') ps) with (flat_map (piece_den E) ps); [reflexivity|].
    apply flat_map_ext. intros [bs|k]; cbn [piece_den]; [reflexivity|]. destruct Hag as [_ Heb]. rewrite Heb. reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite IHs1, IHs2 by assumption. reflexivity.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    rewrite IHs1, IHs2 by assumption. rewrite (edenot_agree' nx0 E E' e Hag H1). reflexivity.
  - apply HOLES_agree. exact Hag.
Qed.

Lemma t_exit_has_nil : forall code fs, t_exit code fs [].
Proof. intros. unfold t_exit. apply t_emit_has_nil. Qed.
Lemma sd_has_nil : forall D E fs s, D [] -> sd D E fs s [].
Proof.
  intros D E fs s HD. induction s; cbn [sd].
  - reflexivity.
  - apply t_exit_has_nil.
  - apply t_emit_has_nil.
  - left. exact IHs1.
  - destruct (_ <=? _)%Z; assumption.
  - apply HOLES_nil.
  - exact HD.
Qed.
Lemma t_alt2_nil_l : forall T : TSet, T [] -> t_eq (t_alt2 t_nil T) T.
Proof. intros T HT tr. unfold t_alt2, t_nil. split; [intros [->|H]; assumption | intros H; right; exact H]. Qed.
Lemma t_alt2_nil_r : forall T : TSet, T [] -> t_eq (t_alt2 T t_nil) T.
Proof. intros T HT tr. unfold t_alt2, t_nil. split; [intros [H| ->]; assumption | intros H; left; exact H]. Qed.

(* [comment removed for export] *)
Lemma t_eq_alt2 : forall TA TA' TB TB' : TSet, t_eq TA TA' -> t_eq TB TB' -> t_eq (t_alt2 TA TB) (t_alt2 TA' TB').
Proof. intros TA TA' TB TB' HA HB tr. unfold t_alt2. split; (intros [H|H]; [left; apply HA | right; apply HB]; exact H). Qed.
Lemma t_eq_refl' : forall T : TSet, t_eq T T.
Proof. intros T tr. tauto. Qed.
Lemma sd_salt2 : forall D E fs a b, D [] ->
  t_eq (t_alt2 (sd D E fs a) (sd D E fs b)) (sd D E fs (salt2 a b)).
Proof.
  intros D E fs a b HD.
  assert (Ha : sd D E fs a []) by (apply sd_has_nil; exact HD).
  assert (Hb : sd D E fs b []) by (apply sd_has_nil; exact HD).
  unfold salt2. destruct a; destruct b; cbn [sd] in *;
    first [ apply t_alt2_nil_l; assumption | apply t_alt2_nil_r; assumption | apply t_eq_refl' ].
Qed.
Lemma salt2_vars : forall b x y, shape_vars_lt b x = true -> shape_vars_lt b y = true -> shape_vars_lt b (salt2 x y) = true.
Proof.
  intros b x y Hx Hy. unfold salt2.
  destruct x; destruct y; cbn [shape_vars_lt] in *; rewrite ?Hx, ?Hy; try reflexivity; try assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node1_stmt (pre : acs -> bool) (node : acs -> option acs) : Prop :=
  forall cs cs' E R FULL model T,
    cs_ok E cs R FULL model -> pre cs = true -> node cs = Some cs' ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
    srealizes SEGS (cfg R (pc cs) FULL model) T.

(* [comment removed for export] *)
Definition brk2d_stmt (node2 : acs -> option (acs * acs)) : Prop :=
  forall cs csg csf E R FULL model T,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node2 cs = Some (csg, csf) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csg R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csg) FULL' model') T) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csf R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csf) FULL' model') T) ->
    srealizes SEGS (cfg R (pc cs) FULL model) T.

Definition always (cs : acs) : bool := true.

(* [comment removed for export] *)
Definition ws_out (E : env) (ws : list (saddr * expr)) (a : word) : Prop :=
  forall w, In w ws -> (bv_unsigned a < estart E (fst w) \/ estart E (fst w) + elenZ E (snd w) <= bv_unsigned a)%Z.
(* [comment removed for export] *)
Definition sys_stmt (y : snode) : Prop :=
  forall cs cs' E R FULL model T,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node_sys A nx0 y cs = Some cs' ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
        (forall W a, AP.sys_frame A y cs = Some W -> ws_out E W a -> Mr E' cs' model' FULL' a = Mr E cs model FULL a) ->
        srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
    srealizes SEGS (cfg R (pc cs) FULL model) T.
(* [comment removed for export] *)
Definition x_stmt (x : xnode) : Prop := forall args, node1_stmt always (node_x SEGS A nx0 x args).
(* [comment removed for export] *)
Definition fresh_stmt : Prop := forall r logc base, node1_stmt always (fun cs => node_fresh nx0 cs r logc base).
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition exit_stmt : Prop :=
  forall cs code E R FULL model,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node_exit cs = Some code ->
    srealizes SEGS (cfg R (pc cs) FULL model) (t_exit (Z_to_bv 64 code) (m_fs model)).

(* [comment removed for export] *)
Definition ext_stmt : Prop := forall id args, node1_stmt always (XN id args).
(* [comment removed for export] *)
Definition ext_stmt_at (id : nat) : Prop := forall args, node1_stmt always (XN id args).
(* [comment removed for export] *)
Definition node1_stmtF (pre : acs -> bool) (node : acs -> option acs) : Prop :=
  forall cs cs' E R FULL model T,
    cs_ok E cs R FULL model -> pre cs = true -> node cs = Some cs' ->
    (forall E' R' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL model' -> m_fs model' = m_fs model ->
        mvis_eq model model' ->                                  (* [comment removed for export] *)
        hid E' cs' model' = hid E cs model ->                    (* [comment removed for export] *)
        srealizes SEGS (cfg R' (pc cs') FULL model') T) ->
    srealizes SEGS (cfg R (pc cs) FULL model) T.
Definition ext_stmtF (id : nat) : Prop := forall args, node1_stmtF always (XN id args).
(* [comment removed for export] *)
Definition join_stmt : Prop := forall b off n, node1_stmtF always (fun cs => node_join SEGS cs b off n).

(* [comment removed for export] *)
Definition node1_stmtW_at (pre : acs -> bool) (node : acs -> option acs) (cs : acs) (ws : list (saddr * expr)) : Prop :=
  forall cs' E R FULL model T,
    cs_ok E cs R FULL model -> pre cs = true -> node cs = Some cs' ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
        (forall a, ws_out E ws a -> FULL' a = FULL a) -> mvis_eq model model' ->
        hid E' cs' model' = hid E cs model ->                  (* [comment removed for export] *)
        srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
    srealizes SEGS (cfg R (pc cs) FULL model) T.
(* [comment removed for export] *)
Definition node1_stmtWP (pre : acs -> bool) (node : acs -> option acs) (wsf : acs -> option (list (saddr * expr))) : Prop :=
  forall cs cs' E R FULL model T,
    cs_ok E cs R FULL model -> pre cs = true -> node cs = Some cs' ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
        (forall W a, wsf cs' = Some W -> ws_out E' W a -> FULL' a = FULL a) ->
        (forall W a, wsf cs' = Some W -> ws_out E' W a -> hid E' cs' model' a = hid E cs model a) ->
        srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
    srealizes SEGS (cfg R (pc cs) FULL model) T.
Definition mmap_stmtW : Prop := node1_stmtWP (is_ecall_at SEGS) (node_mmap A nx0 LIMIT) (AP.mmap_win A).
Lemma node1_stmtWP_stmt : forall pre node wsf, node1_stmtWP pre node wsf -> node1_stmt pre node.
Proof.
  intros pre node wsf HF cs cs' E R FULL model T HC Hp Hn Hk.
  apply (HF cs cs' E R FULL model T HC Hp Hn). intros E' R' FULL' model' Hag HC' Hfs _ _. exact (Hk E' R' FULL' model' Hag HC' Hfs).
Qed.
Definition emit_stmtW_at (id : nat) (args : list expr) (cs : acs) (ws : list (saddr * expr)) : Prop :=
  forall fd ps cs' E R FULL model T,
    cs_ok E cs R FULL model -> XE id args cs = Some (fd, ps, cs') -> T [] ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
        (forall a, ws_out E ws a -> FULL' a = FULL a) -> mvis_eq model model' ->
        hid E' cs' model' = hid E cs model ->
        srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
    srealizes SEGS (cfg R (pc cs) FULL model) (t_emit (Wp E fd ps) T).
Lemma node1_stmtF_stmt : forall pre node, node1_stmtF pre node -> node1_stmt pre node.
Proof.
  intros pre node HF cs cs' E R FULL model T HC Hp Hn Hk.
  apply (HF cs cs' E R FULL model T HC Hp Hn). intros E' R' model' Hag HC' Hfs _ _. exact (Hk E' R' FULL model' Hag HC' Hfs).
Qed.
(* [comment removed for export] *)
Lemma node1_stmtW_stmt : forall pre node (ows : acs -> option (list (saddr * expr))),
  (forall cs cs', node cs = Some cs' -> exists ws, ows cs = Some ws) ->
  (forall cs ws, ows cs = Some ws -> node1_stmtW_at pre node cs ws) -> node1_stmt pre node.
Proof.
  intros pre node ows Htot HW cs cs' E R FULL model T HC Hp Hn Hk.
  destruct (Htot cs cs' Hn) as [ws Hws].
  apply (HW cs ws Hws cs' E R FULL model T HC Hp Hn). intros E' R' FULL' model' Hag HC' Hfs _ _ _. exact (Hk E' R' FULL' model' Hag HC' Hfs).
Qed.
(* [comment removed for export] *)
Definition ext2_stmt : Prop :=
  forall id args cs csa csb E R FULL model TA TB,
    cs_ok E cs R FULL model -> XB id args cs = Some (csa, csb) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csb) FULL' model') TB) ->
    srealizes SEGS (cfg R (pc cs) FULL model) (t_alt2 TA TB).
(* [comment removed for export] *)
Definition mm2_stmt (node : acs -> option (acs * acs)) : Prop :=
  forall cs csa csb E R FULL model TA TB,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node cs = Some (csa, csb) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csb) FULL' model') TB) ->
    srealizes SEGS (cfg R (pc cs) FULL model) (t_alt2 TA TB).

Definition mm3_stmt (node : acs -> option (acs * acs * list acs)) : Prop :=
  forall cs csa csb cscs E R FULL model TA TB TC,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node cs = Some (csa, csb, cscs) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csb) FULL' model') TB) ->
    (forall csc E' R' FULL' model', In csc cscs ->
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csc R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csc) FULL' model') TC) ->
    srealizes SEGS (cfg R (pc cs) FULL model) (t_alt2 TA (t_alt2 TB TC)).

(* [comment removed for export] *)
Definition emit_stmt : Prop :=
  forall id args cs fd ps cs' E R FULL model T,
    cs_ok E cs R FULL model -> XE id args cs = Some (fd, ps, cs') -> T [] ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
    srealizes SEGS (cfg R (pc cs) FULL model) (t_emit (Wp E fd ps) T).
(* [comment removed for export] *)
Lemma emitW_stmt : forall (xews : nat -> list expr -> acs -> option (list (saddr * expr))),
  (forall id args cs r, XE id args cs = Some r -> exists ws, xews id args cs = Some ws) ->
  (forall id args cs ws, xews id args cs = Some ws -> emit_stmtW_at id args cs ws) -> emit_stmt.
Proof.
  intros xews Htot HW id args cs fd ps cs' E R FULL model T HC Hn HT Hk.
  destruct (Htot id args cs _ Hn) as [ws Hws].
  apply (HW id args cs ws Hws fd ps cs' E R FULL model T HC Hn HT). intros E' R' FULL' model' Hag HC' Hfs _ _ _. exact (Hk E' R' FULL' model' Hag HC' Hfs).
Qed.

(* [comment removed for export] *)
Definition holes_stmt : Prop :=
  forall h ch, HS h = Some ch ->
  forall E R FULL model, cs_ok E ch R FULL model ->
    props_ok E (Mr E ch model FULL) (a_props ch) ->      (* [comment removed for export] *)
    srealizes SEGS (cfg R (pc ch) FULL model) (HOLES h E (m_fs model)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis lia_guard : forall k : Empty_set, sec_guard (HS, XN, XE, XB, KC) k.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma split_sound : forall cs e mid lo hi E R FULL model,
  cs_ok E cs R FULL model -> erange (kn cs) e = Some (lo, hi) ->
  (bv_unsigned (edenot E e) <= mid -> cs_ok E (set_kn cs (KRange e lo mid :: kn cs)) R FULL model)
  /\ (mid < bv_unsigned (edenot E e) -> cs_ok E (set_kn cs (KRange e (mid + 1) hi :: kn cs)) R FULL model).
Proof.
  intros cs e mid lo hi E R FULL model HC Hr.
  pose proof (erange_sound SEGS E _ (kn cs) e lo hi (co_know _ _ _ _ _ HC) Hr) as Hb.
  split; intros Hm; apply cs_ok_set_kn; [exact HC| |exact HC|];
    (constructor; [cbn [kentry_ok]; lia | exact (co_know _ _ _ _ _ HC)]).
Qed.

(* [comment removed for export] *)
Lemma erange_any_sound : forall E M k e lo hi,
  know_ok SEGS E M k -> AP.erange_any k e = Some (lo, hi) -> lo <= bv_unsigned (edenot E e) <= hi.
Proof.
  intros E M k e lo hi HK H. unfold AP.erange_any in H.
  destruct (erange k e) as [[lo' hi']|] eqn:Hr.
  - injection H as <- <-. exact (erange_sound SEGS E M k e lo' hi' HK Hr).
  - injection H as <- <-. pose proof (u64_range (edenot E e)). unfold two64. lia.
Qed.
Lemma split_sound_any : forall cs e mid lo hi E R FULL model,
  cs_ok E cs R FULL model -> AP.erange_any (kn cs) e = Some (lo, hi) ->
  (bv_unsigned (edenot E e) <= mid -> cs_ok E (set_kn cs (KRange e lo mid :: kn cs)) R FULL model)
  /\ (mid < bv_unsigned (edenot E e) -> cs_ok E (set_kn cs (KRange e (mid + 1) hi :: kn cs)) R FULL model).
Proof.
  intros cs e mid lo hi E R FULL model HC Hr.
  pose proof (erange_any_sound E _ (kn cs) e lo hi (co_know _ _ _ _ _ HC) Hr) as Hb.
  split; intros Hm; apply cs_ok_set_kn; [exact HC| |exact HC|];
    (constructor; [cbn [kentry_ok]; lia | exact (co_know _ _ _ _ _ HC)]).
Qed.

Lemma kn_contra_sound : forall E M k, know_ok SEGS E M k -> kn_contra k = true -> False.
Proof.
  intros E M k HK H. unfold kn_contra in H. apply existsb_exists in H as (K & Hin & HKb).
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct K as [| | | | |e lo hi| | | |]; try discriminate. cbn [kentry_ok] in HKK.
  destruct (Z.ltb hi lo) eqn:Hlt; [apply Z.ltb_lt in Hlt; lia|].
  assert (GEN : forall c ts, lin_of e = (c, ts) ->
            match lin_range (erange k) c ts with
            | Some (a, b) => (Z.leb 0 a && Z.ltb b two64 && (Z.ltb b lo || Z.ltb hi a))%bool
            | None => false end = true -> False).
  { intros c ts Hle Hm.
    destruct (lin_range (erange k) c ts) as [[a b]|] eqn:Hlr; [|discriminate].
    apply andb_prop in Hm as [Hm Hd]. apply andb_prop in Hm as [Ha Hb].
    apply Z.leb_le in Ha. apply Z.ltb_lt in Hb. unfold two64 in Hb.
    pose proof (lin_range_sound E (erange k) (fun a lo hi Ha => erange_sound SEGS E M k a lo hi HK Ha) _ _ _ _ Hlr) as Hbd.
    pose proof (lin_of_sound E e) as [q Hq]. unfold lden, AX2S.uE in Hq. rewrite Hle in Hq. cbn [fst snd] in Hq.
    pose proof (u64_range (edenot E e)).
    assert (q = 0)%Z by nia. subst q.
    apply orb_prop in Hd as [Hd|Hd]; apply Z.ltb_lt in Hd; lia. }
  destruct e; try discriminate;
    (destruct (lin_of _) as [c [|t1 [|t2 ts]]] eqn:Hle; try discriminate; exact (GEN _ _ eq_refl HKb)).
Qed.

Lemma estart_SA : forall E b k, estart E (SA b k) = bv_unsigned (edenot E b) + k.
Proof. reflexivity. Qed.

Lemma xlo1_sound : forall E M k e lo, know_ok SEGS E M k -> xlo1 k e = Some lo -> lo <= bv_unsigned (edenot E e).
Proof.
  intros E M k e lo HK H. unfold xlo1 in H.
  assert (LIT : forall z, e = ELit z -> Some (zlit64 z) = Some lo -> lo <= bv_unsigned (edenot E e)).
  { intros z -> Hs. injection Hs as <-. cbn [edenot]. rewrite zlit64_eq, u_lit64. lia. }
  destruct e; [exact (LIT _ eq_refl H)|..]; clear LIT;
  (destruct (erange k _) as [[l1 h1]|] eqn:He; [pose proof (erange_sound SEGS E M k _ l1 h1 HK He)|];
   destruct (lin_brange k _) as [[l2 h2]|] eqn:Hb; [pose proof (lin_brange_sound SEGS E M k _ l2 h2 HK Hb)| |pose proof (lin_brange_sound SEGS E M k _ l2 h2 HK Hb)|];
   [..| (* [comment removed for export] *) destruct (lin_srange k _) as [[l3 h3]|] eqn:Hs; [pose proof (lin_srange_sound SEGS E M k _ l3 h3 HK Hs)|]];
   try discriminate; injection H as <-; lia).
Qed.

Lemma xhi1_sound : forall E M k e hi, know_ok SEGS E M k -> xhi1 k e = Some hi -> bv_unsigned (edenot E e) <= hi.
Proof.
  intros E M k e hi HK H. unfold xhi1 in H.
  assert (LIT : forall z, e = ELit z -> Some (zlit64 z) = Some hi -> bv_unsigned (edenot E e) <= hi).
  { intros z -> Hs. injection Hs as <-. cbn [edenot]. rewrite zlit64_eq, u_lit64. lia. }
  destruct e; [exact (LIT _ eq_refl H)|..]; clear LIT;
  (destruct (erange k _) as [[l1 h1]|] eqn:He; [pose proof (erange_sound SEGS E M k _ l1 h1 HK He)|];
   destruct (lin_brange k _) as [[l2 h2]|] eqn:Hb; [pose proof (lin_brange_sound SEGS E M k _ l2 h2 HK Hb)| |pose proof (lin_brange_sound SEGS E M k _ l2 h2 HK Hb)|];
   [..| (* [comment removed for export] *) destruct (lin_srange k _) as [[l3 h3]|] eqn:Hs; [pose proof (lin_srange_sound SEGS E M k _ l3 h3 HK Hs)|]];
   try discriminate; injection H as <-; lia).
Qed.

(* [comment removed for export] *)
Lemma mul_srl_sound : forall E a b y j, mul_srl a b = Some (y, j) ->
  0 <= j <= 48 /\ bv_unsigned (edenot E (EMd M_MUL a b)) = bv_unsigned (edenot E y) - bv_unsigned (edenot E y) mod 2 ^ j.
Proof.
  intros E a b y j H.
  assert (KEY : forall c y0 j0, (Z.leb 0 j0 && Z.leb j0 48 && Z.eqb (c mod two64) (2 ^ j0))%bool = true ->
            0 <= j0 <= 48
            /\ bv_unsigned (mul_div M_MUL (edenot E (ELit c)) (edenot E (EAlu ALU_SRL y0 (ELit j0))))
               = bv_unsigned (edenot E y0) - bv_unsigned (edenot E y0) mod 2 ^ j0
            /\ bv_unsigned (mul_div M_MUL (edenot E (EAlu ALU_SRL y0 (ELit j0))) (edenot E (ELit c)))
               = bv_unsigned (edenot E y0) - bv_unsigned (edenot E y0) mod 2 ^ j0).
  { intros c y0 j0 Ht. apply andb_prop in Ht as [Ht Hc]. apply andb_prop in Ht as [Hj0 Hj1].
    apply Z.leb_le in Hj0. apply Z.leb_le in Hj1. apply Z.eqb_eq in Hc.
    cbn [edenot]. rewrite !u_mul64, !u_srl64, !u_lit64. rewrite Hc.
    assert (Hjm : j0 mod two64 = j0) by (unfold two64; apply Z.mod_small; lia). rewrite Hjm.
    rewrite (Z.mod_small j0 64) by lia.
    pose proof (u64_range (edenot E y0)) as HY. set (Y := bv_unsigned (edenot E y0)) in *.
    assert (Hp : 0 < 2 ^ j0) by (apply Z.pow_pos_nonneg; lia).
    assert (Hpj : 2 ^ j0 <= 2 ^ 48) by (apply Z.pow_le_mono_r; lia).
    assert (Hr : 0 <= Y mod 2 ^ j0 < 2 ^ j0) by (apply Z.mod_pos_bound; lia).
    assert (Hdm : 2 ^ j0 * (Y / 2 ^ j0) = Y - Y mod 2 ^ j0) by (pose proof (Z.div_mod Y (2 ^ j0) ltac:(lia)); lia).
    split; [lia|]. rewrite (Z.mul_comm (Y / 2 ^ j0) (2 ^ j0)). rewrite Hdm.
    rewrite Z.mod_small by lia. split; reflexivity. }
  unfold mul_srl in H.
  destruct a as [c| |opa a1 a2| | | | |].
  - destruct b as [| |opb b1 b2| | | | |]; try discriminate. destruct opb; try discriminate.
    destruct b2 as [j2| | | | | | |]; try discriminate.
    destruct (Z.leb 0 j2 && Z.leb j2 48 && Z.eqb (c mod two64) (2 ^ j2))%bool eqn:Ht; [|discriminate].
    injection H as <- <-. destruct (KEY c b1 j2 Ht) as (K0 & K1 & K2). split; [exact K0 | exact K1].
  - discriminate.
  - destruct opa; try discriminate. destruct a2 as [j1| | | | | | |]; try discriminate.
    destruct b as [c'| |opb b1 b2| | | | |]; try discriminate.
    destruct (Z.leb 0 j1 && Z.leb j1 48 && Z.eqb (c' mod two64) (2 ^ j1))%bool eqn:Ht; [|discriminate].
    injection H as <- <-. destruct (KEY c' a1 j1 Ht) as (K0 & K1 & K2). split; [exact K0 | exact K2].
  - discriminate. - discriminate. - discriminate. - discriminate. - discriminate.
Qed.

Lemma mul_srl_vars : forall bnd a b y j, mul_srl a b = Some (y, j) ->
  AP.expr_vars_lt bnd (EMd M_MUL a b) = true -> AP.expr_vars_lt bnd y = true.
Proof.
  intros bnd a b y j H Hv. cbn [AP.expr_vars_lt] in Hv. fold (AP.expr_vars_lt bnd a) (AP.expr_vars_lt bnd b) in Hv.
  apply andb_prop in Hv as [Hva Hvb]. unfold mul_srl in H.
  destruct a as [c| |opa a1 a2| | | | |]; try discriminate.
  - destruct b as [| |opb b1 b2| | | | |]; try discriminate. destruct opb; try discriminate.
    destruct b2 as [j2| | | | | | |]; try discriminate.
    match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
    injection H as <- <-. cbn [AP.expr_vars_lt] in Hvb. apply andb_prop in Hvb as [X _]. exact X.
  - destruct opa; try discriminate. destruct a2 as [j1| | | | | | |]; try discriminate.
    destruct b as [c'| |opb b1 b2| | | | |]; try discriminate.
    match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
    injection H as <- <-. cbn [AP.expr_vars_lt] in Hva. apply andb_prop in Hva as [X _]. exact X.
Qed.


(* [comment removed for export] *)
Lemma deand_sound : forall E e e' s, deand e = (e', s) ->
  0 <= s /\ exists rho, 0 <= rho <= s /\ bv_unsigned (edenot E e) = (bv_unsigned (edenot E e') - rho) mod 2 ^ 64.
Proof.
  intros E e. induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|u w sx a IHa|bk bo bn bw];
    intros e' s Hd;
    try (cbn [deand] in Hd; injection Hd as <- <-; split; [lia|]; exists 0; split; [lia|];
         rewrite Z.sub_0_r, Z.mod_small by (apply u64_range); reflexivity).
  2:{ (* [comment removed for export] *)
      cbn [deand] in Hd.
      destruct op; try (injection Hd as <- <-; split; [lia|]; exists 0; split; [lia|];
                        rewrite Z.sub_0_r, Z.mod_small by (apply u64_range); reflexivity).
      destruct (mul_srl a b) as [[y j]|] eqn:Hm;
        [|injection Hd as <- <-; split; [lia|]; exists 0; split; [lia|];
          rewrite Z.sub_0_r, Z.mod_small by (apply u64_range); reflexivity].
      injection Hd as <- <-. destruct (mul_srl_sound E a b y j Hm) as [Hj Hv].
      assert (Hp : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
      pose proof (u64_range (edenot E y)) as HY.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      assert (Hr : 0 <= bv_unsigned (edenot E y) mod 2 ^ j < 2 ^ j) by (apply Z.mod_pos_bound; lia).
      assert (Hr2 : bv_unsigned (edenot E y) mod 2 ^ j <= bv_unsigned (edenot E y)) by (apply Z.mod_le; lia).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      rewrite Hv. set (r := bv_unsigned (edenot E y) mod 2 ^ j) in *. clearbody r.
      set (Y := bv_unsigned (edenot E y)) in *. clearbody Y.
      split; [lia|]. exists r. split; [lia|]. rewrite Z.mod_small by lia. reflexivity. }
  cbn [deand] in Hd. fold (deand a) (deand b) in Hd.
  destruct op;
    try (injection Hd as <- <-; split; [lia|]; exists 0; split; [lia|];
         rewrite Z.sub_0_r, Z.mod_small by (apply u64_range); reflexivity).
  - (* [comment removed for export] *)
    destruct (deand a) as [a' s1] eqn:Ha. destruct (deand b) as [b' s2] eqn:Hb. injection Hd as <- <-.
    destruct (IHa a' s1 eq_refl) as [Hs1 [ra [Hra Ea]]]. destruct (IHb b' s2 eq_refl) as [Hs2 [rb [Hrb Eb]]].
    split; [lia|]. exists (ra + rb). split; [lia|].
    cbn [edenot]. rewrite !u_add64, Ea, Eb. unfold two64.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    pose proof (u64_range (edenot E a')). pose proof (u64_range (edenot E b')).
    set (A1 := bv_unsigned (edenot E a')) in *. set (B1 := bv_unsigned (edenot E b')) in *.
    nia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - (* [comment removed for export] *)
    destruct b as [m| | | | | | |];
      try (injection Hd as <- <-; split; [lia|]; exists 0; split; [lia|];
           rewrite Z.sub_0_r, Z.mod_small by (apply u64_range); reflexivity).
    cbv zeta in Hd.
    set (m' := m mod two64) in Hd. set (j := Z.log2 (two64 - m')) in Hd.
    destruct (Z.eqb (two64 - m') (2 ^ j) && Z.leb j 48)%bool eqn:Ht;
      [|injection Hd as <- <-; split; [lia|]; exists 0; split; [lia|];
         rewrite Z.sub_0_r, Z.mod_small by (apply u64_range); reflexivity].
    apply andb_prop in Ht as [Hm Hj]. apply Z.eqb_eq in Hm. apply Z.leb_le in Hj.
    assert (Hj0 : 0 <= j) by (unfold j; apply Z.log2_nonneg).
    destruct (deand a) as [a' s0] eqn:Ha. injection Hd as <- <-.
    destruct (IHa a' s0 eq_refl) as [Hs0 [ra [Hra Ea]]].
    assert (Hp : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
    split; [lia|].
    set (X := bv_unsigned (edenot E a)) in *.
    pose proof (u64_range (edenot E a)) as HX. fold X in HX.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (Hr : 0 <= X mod 2 ^ j < 2 ^ j) by (apply Z.mod_pos_bound; lia).
    assert (Hr2 : X mod 2 ^ j <= X) by (apply Z.mod_le; lia).
    exists (ra + X mod 2 ^ j). split; [lia|].
    cbn [edenot]. rewrite u_and64, u_lit64. fold X. fold m'.
    assert (Hm' : 0 <= m' < two64) by (unfold m'; apply Z.mod_pos_bound; unfold two64; lia).
    replace m' with (2 ^ 64 - 2 ^ j) by (unfold two64 in *; lia).
    rewrite land_highmask by lia.
    pose proof (u64_range (edenot E a')) as HA'. set (A' := bv_unsigned (edenot E a')) in *.
    set (r := X mod 2 ^ j) in *. clearbody r.
    rewrite Ea. rewrite Ea in HX. nia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma deand_vars : forall bnd e e' s, deand e = (e', s) -> AP.expr_vars_lt bnd e = true -> AP.expr_vars_lt bnd e' = true.
Proof.
  intros bnd e. induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|u w sx a IHa|bk bo bn bw];
    intros e' s Hd Hv; try (cbn [deand] in Hd; injection Hd as <- <-; exact Hv).
  2:{ (* [comment removed for export] *)
      cbn [deand] in Hd. pose proof Hv as Hv0.
      destruct op; try (injection Hd as <- <-; exact Hv0).
      destruct (mul_srl a b) as [[y j]|] eqn:Hm; [|injection Hd as <- <-; exact Hv0]. injection Hd as <- <-.
      exact (mul_srl_vars bnd a b _ _ Hm Hv0). }
  cbn [deand] in Hd. fold (deand a) (deand b) in Hd.
  pose proof Hv as Hv0.
  cbn [AP.expr_vars_lt] in Hv. apply andb_prop in Hv as [Hva Hvb].
  destruct op; try (injection Hd as <- <-; exact Hv0).
  - destruct (deand a) as [a' s1] eqn:Ha. destruct (deand b) as [b' s2] eqn:Hb. injection Hd as <- <-.
    cbn [AP.expr_vars_lt]. rewrite (IHa a' s1 eq_refl Hva), (IHb b' s2 eq_refl Hvb). reflexivity.
  - destruct b as [m| | | | | | |]; try (injection Hd as <- <-; exact Hv0).
    cbv zeta in Hd.
    destruct (Z.eqb _ _ && Z.leb _ 48)%bool; [|injection Hd as <- <-; exact Hv0].
    destruct (deand a) as [a' s0] eqn:Ha. injection Hd as <- <-. exact (IHa a' s0 eq_refl Hva).
Qed.

Lemma xb2_sound : forall E M k e lo hi, know_ok SEGS E M k -> xb2 k e = Some (lo, hi) ->
  lo <= bv_unsigned (edenot E e) <= hi.
Proof.
  intros E M k e lo hi HK H. unfold xb2 in H.
  set (plain := match xlo1 k e, xhi1 k e with Some lo, Some hi => Some (lo, hi) | _, _ => None end) in H.
  assert (HP : forall lo hi, plain = Some (lo, hi) -> lo <= bv_unsigned (edenot E e) <= hi).
  { intros l h Hp. unfold plain in Hp.
    destruct (xlo1 k e) as [l1|] eqn:H1; [|discriminate]. destruct (xhi1 k e) as [h1|] eqn:H2; [|discriminate].
    injection Hp as <- <-. split; [eapply xlo1_sound; eassumption | eapply xhi1_sound; eassumption]. }
  destruct (deand e) as [e' s] eqn:Hd.
  destruct (deand_sound E e e' s Hd) as [Hs [rho [Hrho Ee]]].
  destruct (Z.eqb s 0); [exact (HP lo hi H)|].
  destruct (xlo1 k e') as [lo'|] eqn:H1; [|exact (HP lo hi H)].
  destruct (xhi1 k e') as [hi'|] eqn:H2; [|exact (HP lo hi H)].
  destruct (Z.leb s lo') eqn:Hsl; [|exact (HP lo hi H)]. apply Z.leb_le in Hsl.
  pose proof (xlo1_sound E M k e' lo' HK H1) as L1. pose proof (xhi1_sound E M k e' hi' HK H2) as L2.
  pose proof (u64_range (edenot E e')) as R'.
  assert (Hue : bv_unsigned (edenot E e) = bv_unsigned (edenot E e') - rho) by (rewrite Ee; apply Z.mod_small; lia).
  destruct plain as [[l0 h0]|].
  - specialize (HP l0 h0 eq_refl). injection H as <- <-. lia.
  - injection H as <- <-. lia.
Qed.

Lemma xlo2_sound : forall E M k e lo, know_ok SEGS E M k -> xlo2 k e = Some lo -> lo <= bv_unsigned (edenot E e).
Proof.
  intros E M k e lo HK H. unfold xlo2 in H. destruct (xb2 k e) as [[l h]|] eqn:Hb; [|discriminate].
  injection H as <-. exact (proj1 (xb2_sound E M k e l h HK Hb)).
Qed.

Lemma xhi2_sound : forall E M k e hi, know_ok SEGS E M k -> xhi2 k e = Some hi -> bv_unsigned (edenot E e) <= hi.
Proof.
  intros E M k e hi HK H. unfold xhi2 in H. destruct (xb2 k e) as [[l h]|] eqn:Hb; [|discriminate].
  injection H as <-. exact (proj2 (xb2_sound E M k e l h HK Hb)).
Qed.

(* [comment removed for export] *)
Lemma residue_fact_sound : forall E E' M M' k e ne,
  know_ok SEGS E M k ->
  edenot E' ne = edenot E e ->
  (forall e' s, deand e = (e', s) -> edenot E' e' = edenot E e') ->
  know_ok SEGS E' M' (residue_fact k e ne).
Proof.
  intros E E' M M' k e ne HK Hne Hag. unfold residue_fact.
  destruct (deand e) as [e' s] eqn:Hd. destruct (Z.ltb 0 s) eqn:Hs; [|constructor].
  destruct (xlo1 k e') as [lo'|] eqn:H1; [|constructor]. destruct (xhi1 k e') as [hi'|] eqn:H2; [|constructor].
  destruct (Z.leb s lo') eqn:Hsl; [|constructor]. apply Z.leb_le in Hsl.
  constructor; [|constructor]. cbn [kentry_ok]. unfold esub. rewrite mkAlu_denot, u_sub64, Hne, (Hag e' s eq_refl).
  destruct (deand_sound E e e' s Hd) as [Hs0 [rho [Hrho Ee]]].
  pose proof (xlo1_sound E M k e' lo' HK H1) as L1. pose proof (u64_range (edenot E e')) as R'.
  assert (Hue : bv_unsigned (edenot E e) = bv_unsigned (edenot E e') - rho) by (rewrite Ee; apply Z.mod_small; lia).
  rewrite Hue. replace (bv_unsigned (edenot E e') - (bv_unsigned (edenot E e') - rho)) with rho by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma fact_ok_sound : forall E M k K, know_ok SEGS E M k -> fact_ok k K = true -> kentry_ok SEGS E M K.
Proof.
  intros E M k K HK H. destruct K as [| | | |e m|e lo hi| |[b1 k1] n1 [b2 k2] n2| |]; try discriminate; cbn [fact_ok] in H.
  - (* [comment removed for export] *) apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. cbn [kentry_ok]. split; [exact H1|].
    destruct (ealign_sound SEGS E M k e HK) as [Hr Hd].
    rewrite H2. apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Hd]. apply pow2_divide_le. split; [apply Z.log2_nonneg | exact H3].
  - (* [comment removed for export] *) destruct (xlo2 k e) as [l|] eqn:Hl; [|discriminate]. destruct (xhi2 k e) as [h|] eqn:Hh; [|discriminate].
    apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (xlo2_sound E M k e l HK Hl). pose proof (xhi2_sound E M k e h HK Hh). cbn [kentry_ok]. lia.
  - (* [comment removed for export] *) cbn [kentry_ok]. exact (ranges_apart_x_sound SEGS E M k b1 k1 n1 b2 k2 n2 HK H).
Qed.

Lemma fact_sound : forall E cs R FULL model K,
  cs_ok E cs R FULL model -> fact_ok (kn cs) K = true -> cs_ok E (add_kn cs [K]) R FULL model.
Proof.
  intros E cs R FULL model K HC H. unfold add_kn. apply cs_ok_set_kn; [exact HC|].
  constructor; [eapply fact_ok_sound; [exact (co_know _ _ _ _ _ HC) | exact H] | exact (co_know _ _ _ _ _ HC)].
Qed.

(* [comment removed for export] *)
Lemma fact_soundL : forall E cs R FULL model K,
  cs_ok E cs R FULL model -> (fact_ok (kn cs) K || AP.fact_okL (kn cs) K)%bool = true -> cs_ok E (add_kn cs [K]) R FULL model.
Proof.
  intros E cs R FULL model K HC H. apply Bool.orb_prop in H as [H|H]; [exact (fact_sound E cs R FULL model K HC H)|].
  unfold AP.fact_okL in H. destruct K as [| | | | |e lo hi| | | |]; try discriminate.
  unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact (co_know _ _ _ _ _ HC)].
  cbn [kentry_ok]. exact (APWS.krange_lin_sound SEGS E _ (kn cs) e lo hi (co_know _ _ _ _ _ HC) H).
Qed.

Lemma regs_ok_ext_eq : forall E sr sr' R, sr = sr' -> regs_ok E sr R -> regs_ok E sr' R.
Proof. intros; subst; assumption. Qed.

(* [comment removed for export] *)
Lemma entails_sound : forall E cs ch R FULL model,
  cs_ok E cs R FULL model -> entails cs ch = true -> cs_ok E ch R FULL model /\ pc ch = pc cs.
Proof.
  intros E cs ch R FULL model HC H. unfold entails in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  rename H into Hpc. apply Z.eqb_eq in Hpc. split; [|symmetry; exact Hpc].
  match goal with Hl : match s_log (a_ss ch) with _ => _ end = true |- _ => rename Hl into HL; destruct (s_log (a_ss ch)) eqn:HL'; [clear HL; rename HL' into HL|discriminate] end.
  match goal with Hr : list_eqb expr_eqb _ _ = true |- _ => apply (list_eqb_eq expr_eqb expr_eqb_eq) in Hr; rename Hr into Hregs end.
  match goal with Hm : list_eqb amap_eqb _ _ = true |- _ => apply (list_eqb_eq amap_eqb amap_eqb_eq) in Hm; rename Hm into Hmaps end.
  match goal with Ha : list_eqb pair_eqb (a_vis cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ha; rename Ha into Hallow end.
  match goal with Hg : list_eqb pair_eqb (a_ghost cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hg; rename Hg into Hghost end.
  match goal with Hb : expr_eqb (a_brk cs) _ = true |- _ => apply expr_eqb_eq in Hb; rename Hb into Hbrk end.
  match goal with Hf : afd_eqb _ _ = true |- _ => apply afd_eqb_eq in Hf; rename Hf into Hfd end.
  match goal with Ht : Bool.eqb _ _ = true |- _ => apply eqb_prop in Ht; rename Ht into Htid end.
  match goal with Hk : forallb _ (kn ch) = true |- _ => rename Hk into Hkn end.
  repeat match goal with Hz : Z.leb _ _ = true |- _ => apply Z.leb_le in Hz end.
  assert (HA : allowA E ch = allowA E cs) by (unfold allowA; rewrite Hallow, Hghost; reflexivity).
  assert (HH : hid E ch model = hid E cs model) by (apply hid_ext; symmetry; exact Hallow).
  destruct HC; constructor; rewrite <- ?Hregs, <- ?Hmaps, <- ?Hallow, <- ?Hghost, <- ?Hbrk, <- ?Hfd, <- ?Htid, ?HA; try assumption.
  - unfold Mr. rewrite HH. unfold know_ok. apply Forall_forall. intros K Hin.
    pose proof (proj1 (forallb_forall _ _) Hkn K Hin) as HK. apply existsb_exists in HK as [K' [Hin' Heq]].
    apply kentry_eqb_eq in Heq. subst K'. exact (proj1 (Forall_forall _ _) co_know0 K Hin').
  - eapply holes_mono; [exact co_holes0 | lia].
  - lia.
  - lia.
  - lia.
  - intros a. rewrite HH. replace (in_ghost E ch) with (in_ghost E cs) by (unfold in_ghost; rewrite Hghost; reflexivity). exact (co_zero0 a).
Qed.


(* [comment removed for export] *)
Lemma ridx_lit : forall n, (n < 32)%nat -> ridx (Z_to_bv 5 (Z.of_nat n)) = n.
Proof.
  intros n Hn. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.

Lemma reg_sound : forall E cs R FULL model n,
  cs_ok E cs R FULL model -> (0 < n < 32)%nat ->
  getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (reg cs n).
Proof.
  intros E cs R FULL model n HC Hn. rewrite (co_regs _ _ _ _ _ HC). unfold sr_get, reg.
  assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
  rewrite Hnz. rewrite ridx_lit by lia. reflexivity.
Qed.

Lemma lit_of_sound : forall E e z, lit_of e = Some z -> edenot E e = Z_to_bv 64 z /\ (0 <= z < two64)%Z.
Proof.
  intros E e z H. destruct e; try discriminate. cbn [lit_of] in H. injection H as <-.
  split; [| unfold two64; apply Z.mod_pos_bound; lia].
  cbn [edenot]. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma reg_lit_sound : forall E cs R FULL model n z,
  cs_ok E cs R FULL model -> (0 < n < 32)%nat -> reg_lit cs n = Some z ->
  getr R (Z_to_bv 5 (Z.of_nat n)) = Z_to_bv 64 z /\ (0 <= z < two64)%Z.
Proof.
  intros E cs R FULL model n z HC Hn H. unfold reg_lit in H.
  destruct (lit_of_sound E (reg cs n) z H) as [He Hz]. rewrite (reg_sound E cs R FULL model n HC Hn), He. auto.
Qed.

(* [comment removed for export] *)
Lemma regs_ok_respell : forall E sr R n e,
  regs_ok E sr R -> (0 < n < 32)%nat -> edenot E e = edenot E (nth n sr (ELit 0)) ->
  regs_ok E (sr_upd sr n e) R.
Proof.
  intros E sr R n e HR Hn He.
  replace (sr_upd sr n e) with (sr_upd sr (ridx (Z_to_bv 5 (Z.of_nat n))) e) by (rewrite ridx_lit by lia; reflexivity).
  apply regs_ok_pin; [exact HR|].
  rewrite (HR (Z_to_bv 5 (Z.of_nat n))). unfold sr_get.
  assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
  rewrite Hnz, ridx_lit by lia. symmetry. exact He.
Qed.

(* [comment removed for export] *)
Lemma regs_ok_set_n : forall E sr R n e v,
  regs_ok E sr R -> (0 < n < 32)%nat -> edenot E e = v ->
  regs_ok E (sr_upd sr n e) (regupd R (Z_to_bv 5 (Z.of_nat n)) v).
Proof.
  intros E sr R n e v HR Hn He.
  replace (sr_upd sr n e) with (sr_upd sr (ridx (Z_to_bv 5 (Z.of_nat n))) e) by (rewrite ridx_lit by lia; reflexivity).
  apply regs_ok_set; [exact HR | | exact He].
  intros Hz. apply (f_equal bv_unsigned) in Hz. rewrite Z_to_bv_unsigned in Hz. unfold bv_wrap in Hz.
  change (bv_modulus 5) with 32%Z in Hz. rewrite Z.mod_small in Hz by lia.
  replace (bv_unsigned (0%bv : bv 5)) with 0%Z in Hz by reflexivity. lia.
Qed.

(* [comment removed for export] *)
Lemma fresh_ok_parts : forall cs, fresh_ok nx0 cs = true ->
  AP.sr_vars_lt (nxt cs) (s_regs (a_ss cs)) = true /\ AP.kn_vars_lt (nxt cs) (kn cs) = true
  /\ maps_vars_lt (nxt cs) (a_maps cs) = true /\ pairs_vars_lt (nxt cs) (a_vis cs ++ a_ghost cs) = true
  /\ AP.expr_vars_lt (nxt cs) (a_brk cs) = true /\ fd_vars_lt (nxt cs) (a_fd cs) = true /\ (nx0 <= nxt cs)%nat.
Proof.
  intros cs H. unfold fresh_ok in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Nat.leb_le in X. repeat split; try assumption.
  unfold pairs_vars_lt in *. rewrite forallb_app. apply andb_true_intro. split; assumption.
Qed.

Lemma allowA_agree : forall b E E' cs, env_agree b E E' -> pairs_vars_lt b (a_vis cs ++ a_ghost cs) = true -> allowA E' cs = allowA E cs.
Proof.
  intros b E E' cs Hag H. unfold allowA. rewrite !flat_map_concat_map. f_equal. apply map_ext_in. intros p Hin.
  pose proof (proj1 (forallb_forall _ _) H p Hin) as Hp. apply andb_prop in Hp as [H1 H2].
  unfold allow1, sh_lo, sh_hi, uE. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2). reflexivity.
Qed.

Lemma in_allow_agree : forall b E E' cs, env_agree b E E' -> pairs_vars_lt b (a_vis cs) = true -> in_allow E' cs = in_allow E cs.
Proof.
  intros b E E' cs Hag H. apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh. unfold pairs_vars_lt in H.
  induction (a_vis cs) as [|p l IH]; [reflexivity|]. cbn [existsb forallb] in H |- *.
  apply andb_prop in H as [Hp Hl]. apply andb_prop in Hp as [H1 H2].
  unfold sh_lo, sh_hi, uE in *. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2).
  pose proof (IH Hl) as E1. apply (f_equal negb) in E1. rewrite !negb_orb in E1.
  apply (f_equal negb) in E1. rewrite !negb_andb, !negb_involutive in E1.
  destruct (existsb _ l), (existsb _ l), (existsb _ l), (existsb _ l); cbn in E1 |- *; rewrite ?orb_true_r, ?orb_false_r; try reflexivity; try discriminate.
Qed.

Lemma in_ghost_agree : forall b E E' cs, env_agree b E E' -> pairs_vars_lt b (a_vis cs ++ a_ghost cs) = true ->
  in_ghost E' cs = in_ghost E cs.
Proof.
  intros b E E' cs Hag H. apply functional_extensionality. intros z. unfold in_ghost.
  unfold pairs_vars_lt in H. rewrite forallb_app in H. apply andb_prop in H as [_ H].
  induction (a_ghost cs) as [|p l IH]; [reflexivity|]. cbn [existsb forallb] in H |- *.
  apply andb_prop in H as [Hp Hl]. apply andb_prop in Hp as [H1 H2].
  unfold uE in *. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2), (IH Hl). reflexivity.
Qed.

Lemma hid_agree : forall b E E' cs model, env_agree b E E' -> (nx0 <= b)%nat -> pairs_vars_lt b (a_vis cs ++ a_ghost cs) = true ->
  hid E' cs model = hid E cs model.
Proof.
  intros b E E' cs model Hag Hle H. apply functional_extensionality. intros a. unfold hid, vis.
  assert (H' : pairs_vars_lt b (a_vis cs) = true).
  { unfold pairs_vars_lt in *. rewrite forallb_app in H. apply andb_prop in H as [H _]. exact H. }
  rewrite (in_allow_agree b E E' cs Hag H'). rewrite (argH_agree E E' a) by (eapply env_agree_le; eassumption). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma hid_extF : forall b E E' cs cs' model model',
  a_vis cs' = a_vis cs -> env_agree b E E' -> (nx0 <= b)%nat -> pairs_vars_lt b (a_vis cs ++ a_ghost cs) = true ->
  mvis_eq model model' -> hid E' cs' model' = hid E cs model.
Proof.
  intros b E E' cs cs' model model' Hv Hag Hb Hp Hmv.
  rewrite (hid_ext E' cs cs' model' Hv), (hid_mvis E' cs model model' Hmv). exact (hid_agree b E E' cs model Hag Hb Hp).
Qed.
Lemma hid_extF0 : forall E cs cs' model model', a_vis cs' = a_vis cs -> mvis_eq model model' -> hid E cs' model' = hid E cs model.
Proof. intros E cs cs' model model' Hv Hmv. rewrite (hid_ext E cs cs' model' Hv). exact (hid_mvis E cs model model' Hmv). Qed.

Lemma maps_den_agree : forall b E E' ms, env_agree b E E' -> maps_vars_lt b ms = true -> map (amap_den E') ms = map (amap_den E) ms.
Proof.
  intros b E E' ms Hag H. apply map_ext_in. intros m Hin.
  pose proof (proj1 (forallb_forall _ _) H m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
  unfold amap_den. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2). reflexivity.
Qed.

Lemma maps_match_agree : forall b E E' ms l, env_agree b E E' -> maps_vars_lt b ms = true ->
  maps_match E ms l -> maps_match E' ms l.
Proof.
  intros b E E' ms. induction ms as [|m ms IH]; intros l Hag H HM; cbn [maps_match] in *; [exact HM|].
  cbn [maps_vars_lt forallb] in H. apply andb_prop in H as [Hm Hr]. apply andb_prop in Hm as [H1 H2].
  unfold uE, amap_den in *. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2).
  destruct (is_fog m).
  - destruct HM as [HM|(iv & l' & -> & Hsz & HM)]; [left; exact (IH _ Hag Hr HM) | right].
    exists iv, l'. split; [reflexivity|]. split; [exact Hsz | exact (IH _ Hag Hr HM)].
  - destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | exact (IH _ Hag Hr HM)].
Qed.

(* [comment removed for export] *)
Lemma holes_agree : forall b E E' y l ms,
  env_agree b E E' -> maps_vars_lt b ms = true -> Forall (hole_ok E y l) ms -> Forall (hole_ok E' y l) ms.
Proof.
  intros b E E' y l ms Hag Hv H. apply Forall_forall. intros m Hin Hh.
  pose proof (proj1 (forallb_forall _ _) Hv m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
  unfold hole_ok, uE in *. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2).
  exact (proj1 (Forall_forall _ _) H m Hin Hh).
Qed.

Lemma fds_ok_agree : forall b E E' f model,
  env_agree b E E' -> fd_vars_lt b f = true -> fds_ok E f model -> fds_ok E' f model.
Proof.
  intros b E E' f model Hag Hv H. destruct f as [|k len off|]; try exact H.
  cbn [fd_vars_lt] in Hv. apply andb_prop in Hv as [Hl Ho].
  destruct H as [p [c (H1 & H2 & H3 & H4 & H5)]]. exists p, c.
  unfold uE in *. rewrite <- (edenot_agree' b E E' _ Hag Hl), <- (edenot_agree' b E E' _ Hag Ho).
  destruct Hag as [_ Heb]. rewrite <- Heb. repeat split; assumption.
Qed.

Lemma cs_ok_agree : forall E E' cs R FULL model,
  env_agree (nxt cs) E E' -> fresh_ok nx0 cs = true ->
  cs_ok E cs R FULL model -> cs_ok E' cs R FULL model.
Proof.
  intros E E' cs R FULL model Hag Hf HC.
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (hid_agree (nxt cs) E E' cs model Hag Fle Fallow) as HH.
  pose proof (allowA_agree (nxt cs) E E' cs Hag Fallow) as HA.
  destruct HC; constructor; rewrite ?HA; try assumption.
  - eapply regs_ok_agree'; eassumption.
  - unfold Mr. rewrite HH. eapply know_ok_agree'; eassumption.
  - eapply fds_ok_agree; eassumption.
  - eapply maps_match_agree; [exact Hag | exact Fmaps | assumption].
  - eapply holes_agree; [exact Hag | exact Fmaps | assumption].
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk.
    pose proof (proj1 (forallb_forall _ _) Fmaps m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
    unfold amap_den. rewrite <- (edenot_agree' (nxt cs) E E' _ Hag H1), <- (edenot_agree' (nxt cs) E E' _ Hag H2).
    exact (proj1 (Forall_forall _ _) co_none0 m Hin Hk).
  - apply Forall_forall. intros m Hin Hk a Ha.
    pose proof (proj1 (forallb_forall _ _) Fmaps m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
    rewrite <- (edenot_agree' (nxt cs) E E' _ Hag H1), <- (edenot_agree' (nxt cs) E E' _ Hag H2) in Ha.
    exact (proj1 (Forall_forall _ _) co_kinds0 m Hin Hk a Ha).
  - (* [comment removed for export] *) rewrite (e_sp0_agree _ _ _ Hag Fle). assumption.
  - rewrite <- (edenot_agree' (nxt cs) E E' _ Hag Fbrk). assumption.
  - intros a. rewrite HH, (in_ghost_agree (nxt cs) E E' cs Hag Fallow). exact (co_zero0 a).
  - eapply SINV_agree; [eapply env_agree_le; [exact Hag | exact Fle] | assumption].
Qed.


(* [comment removed for export] *)
Lemma fresh_ok_mono : forall gb cs, (nx0 <= gb)%nat -> fresh_ok gb cs = true -> fresh_ok nx0 cs = true.
Proof.
  intros gb cs Hle H. unfold fresh_ok in *.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Nat.leb_le in X.
  repeat (apply andb_true_intro; split); try assumption. apply Nat.leb_le. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition log_out (E : env) (log : list sentry) (a : word) : Prop :=
  forall s, In s log -> match s with SE sa w _ =>
    (bv_unsigned a < estart E sa \/ estart E sa + Z.of_nat w <= bv_unsigned a)%Z end.
Lemma mem_denot_out : forall E base log a, log_flat E log -> log_out E log a -> mem_denot E base log a = base a.
Proof.
  intros E base log a. induction log as [|[sa w v] rest IH]; intros Hlf Hout; [reflexivity|].
  cbn [mem_denot]. cbn [log_flat] in Hlf. destruct Hlf as (Hw & Hfl & Hrest).
  rewrite wbytes_out.
  - apply IH; [exact Hrest|]. intros s Hs. apply Hout. right. exact Hs.
  - unfold word_to_le_bytes. rewrite length_Z_to_le_bytes, (flat_u _ _ _ Hfl). destruct Hfl as (_ & _ & _ & H4). exact H4.
  - unfold word_to_le_bytes. rewrite length_Z_to_le_bytes, (flat_u _ _ _ Hfl). apply (Hout (SE sa w v)). left. reflexivity.
Qed.
Lemma run_block_soundX : forall gb bfuel stops cs kn' hs E R FULL model T,
  frm_zero (@fp_csr fx) ->
  (nx0 <= gb)%nat -> fresh_ok gb cs = true ->
  let ss := a_ss cs in
  let ss' := AX2F.sym_execTXF SEGS IT KC bfuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
  carry (s_log ss') (kunwrap_head (s_know ss')) [] = (kn', [], hs) ->
  let cs' := with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')) in
  cs_ok E cs R FULL model ->
  (forall (fy : FPState) E' R' FULL' model',
      frm_zero (@fp_csr fy) ->
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      log_flat E' (s_log ss') -> know_ok SEGS E' (Mr E cs model FULL) (s_know ss') ->
      (forall a, log_out E' (s_log ss') a -> FULL' a = FULL a) ->
      (forall a, log_out E' (s_log ss') a -> Mr E' cs' model' FULL' a = Mr E cs model FULL a) ->   (* [comment removed for export] *)
      mvis_eq model model' ->                                                                          (* [comment removed for export] *)
      srealizes SEGS (@cfg_of fy SEGS R' (pc cs') FULL' model') T) ->
  srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
  intros gb bfuel stops cs kn' hs E R FULL model T Hfz Hgb Hf0. cbv zeta. intros Hc HC Hk.
  pose proof (fresh_ok_mono gb cs Hgb Hf0) as Hf.
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (co_regs _ _ _ _ _ HC) as HR. pose proof (co_know _ _ _ _ _ HC) as HK.
  unfold kn in HK, Fkn. unfold nxt in Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle, Hk.
  revert Hc Hk. destruct (a_ss cs) as [p sr log k nx rsv] eqn:Hss.
  cbn [s_know s_regs s_pc s_next] in HR, HK, Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle |- *.
  set (ss' := AX2F.sym_execTXF SEGS IT KC bfuel true stops (SS p sr [] k nx)). intros Hc Hk.
  (* [comment removed for export] *)
  set (H := hid E cs model). set (MR := Mr E cs model FULL).
  rewrite sr_vars_lt_eq in Fsr. rewrite kn_vars_lt_eq in Fkn.
  pose proof (runTXF_sound SEGS fx IT KC bfuel stops p sr k nx E MR (seg_rom SEGS) R IT_ok Hfz HR HK Fsr Fkn) as HX.
  cbn zeta in HX. fold ss' in HX. destruct HX as (E' & R' & fy' & Hag & Hle & HR' & Hlf & HK' & Hz' & Hms & _).
  assert (Hagc : env_agree (nxt cs) E E') by (unfold nxt; rewrite Hss; exact Hag).
  pose proof (cs_ok_agree E E' cs R FULL model Hagc Hf HC) as HC'.
  assert (HH : hid E' cs model = H).
  { unfold H. eapply hid_agree; [exact Hagc | unfold nxt; rewrite Hss; exact Fle | unfold nxt; rewrite Hss; exact Fallow]. }
  unfold cfg_of, pc. rewrite Hss. cbn [a_ss s_pc].
  apply (srz_msteps_restricted_T SEGS H (H_off_segments_cs E cs model) SEGS_wx (allowA E cs)
           (mkst R (Z_to_bv 64 p) FULL (seg_rom SEGS)) _ model T
           (lazy_cover_cs E cs R FULL model HC) (A_wf_allowA E cs) (co_minv _ _ _ _ _ HC) (co_halt _ _ _ _ _ HC) Hms).
  intros model' Hinv' Hsame Hclean.
  assert (HKc : know_ok SEGS E' (mem_denot E' MR (s_log ss')) kn').
  { eapply (carry_sound SEGS E' MR); [exact Hc | exact Hlf | apply know_ok_kunwrap_head; exact HK' | constructor]. }
  set (FULL' := munrestrict H FULL (mem_denot E' MR (s_log ss'))).
  assert (Hmr' : Mr E' cs model FULL' = mem_denot E' MR (s_log ss')).
  { unfold Mr, FULL'. rewrite HH. apply mrestrict_munrestrict_clean. intros a Ha. exact (Hclean a Ha). }
  assert (Flec : (nx0 <= nxt cs)%nat) by (unfold nxt; rewrite Hss; exact Fle).
  assert (Fallowc : pairs_vars_lt (nxt cs) (a_vis cs ++ a_ghost cs) = true) by (unfold nxt; rewrite Hss; exact Fallow).
  specialize (Hk fy' E' R' FULL' model' Hz' (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
  unfold cfg_of, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk.
  replace (unrestrict H (ms_mem (mkst R (Z_to_bv 64 p) FULL (seg_rom SEGS)))
             (@mkst fy' R' (Z_to_bv 64 (s_pc ss')) (mem_denot E' MR (s_log ss')) (seg_rom SEGS)))
    with (@mkst fy' R' (Z_to_bv 64 (s_pc ss')) FULL' (seg_rom SEGS)) by reflexivity.
  apply Hk.
  - eapply cs_ok_frame; [exact HC' | exact Hsame | | exact HR' | reflexivity | | ].
    + rewrite (allowA_agree (nxt cs) E E' cs Hagc Fallowc). exact Hinv'.
    + cbn [mk_ss s_know]. rewrite Hmr'. exact HKc.
    + intros a Ha. rewrite HH in Ha. unfold FULL', munrestrict. rewrite Ha. reflexivity.
  - pose proof (same_but_materialized_frame _ _ Hsame) as Hfr. apply Hfr.
  - exact Hlf.
  - exact HK'.
  - (* [comment removed for export] *)
    intros a Hout. unfold FULL', munrestrict. destruct (H a) eqn:Hh; [reflexivity|].
    rewrite (mem_denot_out E' MR (s_log ss') a Hlf Hout). unfold MR, Mr, mrestrict. unfold H in Hh. rewrite Hh. reflexivity.
  - (* [comment removed for export] *)
    intros a Hout. unfold Mr at 1. unfold mrestrict.
    replace (hid E' (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss'))) model') with H
      by (symmetry; rewrite (hid_same E' _ model model' Hsame); exact HH).
    unfold FULL', munrestrict. destruct (H a) eqn:Hh.
    + unfold MR, Mr, mrestrict. unfold H in Hh. rewrite Hh. reflexivity.
    + rewrite (mem_denot_out E' MR (s_log ss') a Hlf Hout). reflexivity.
  - (* [comment removed for export] *) exact (mvis_of_materialized _ _ Hsame).
Qed.

Lemma run_block_sound : forall gb bfuel stops cs cs' E R FULL model T,
  frm_zero (@fp_csr fx) ->
  (nx0 <= gb)%nat ->
  run_block SEGS IT gb KC bfuel stops cs = Some cs' -> cs_ok E cs R FULL model ->
  (forall (fy : FPState) E' R' FULL' model',
      frm_zero (@fp_csr fy) ->
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (@cfg_of fy SEGS R' (pc cs') FULL' model') T) ->
  srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
  intros gb bfuel stops cs cs' E R FULL model T Hfz Hgb Hrb HC Hk.
  rewrite run_block_eq in Hrb. (* [comment removed for export] *) unfold run_block_ref in Hrb.
  destruct (fresh_ok gb cs) eqn:Hf0; [|discriminate].
  destruct (carry _ _ []) as [[kn' scs] hs] eqn:Hc. destruct scs; [|discriminate]. injection Hrb as <-.
  eapply (run_block_soundX gb bfuel stops cs kn' hs E R FULL model T Hfz Hgb Hf0 Hc HC).
  intros fy E' R' FULL' model' Hz Hag HC1 Hfs _ _ _ _ _. exact (Hk fy E' R' FULL' model' Hz Hag HC1 Hfs).
Qed.

Lemma run_block_gc_sound : forall gb bfuel stops cs cs' E R FULL model T,
  frm_zero (@fp_csr fx) ->
  (nx0 <= gb)%nat ->
  run_block_gc SEGS IT gb KC bfuel stops cs = Some cs' -> cs_ok E cs R FULL model ->
  (forall (fy : FPState) E' R' FULL' model',
      frm_zero (@fp_csr fy) ->
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (@cfg_of fy SEGS R' (pc cs') FULL' model') T) ->
  srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
  intros gb bfuel stops cs cs' E R FULL model T Hfz Hgb H HC Hk. unfold run_block_gc in H.
  destruct (run_block SEGS IT gb KC bfuel stops cs) as [cs1|] eqn:Hrb; [|discriminate]. injection H as <-.
  eapply run_block_sound; [exact Hfz | exact Hgb | exact Hrb | exact HC |].
  intros fy E' R' FULL' model' Hz Hag HC1 Hfs. rewrite <- (pc_cs_gc gb cs1).
  apply (Hk fy E' R' FULL' model'); [exact Hz | exact Hag | apply cs_gc_ok; exact HC1 | exact Hfs].
Qed.

(* [comment removed for export] *)
Lemma u_small : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros. apply u64_lit. assumption. Qed.

Lemma nth_sr_vars_lt : forall b sr r, AP.sr_vars_lt b sr = true -> (r < 32)%nat -> AP.expr_vars_lt b (nth r sr (ELit 0)) = true.
Proof.
  intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
  cbn [AP.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma node_fresh_soundL : forall r logc base cs cs' E R FULL model,
  cs_ok E cs R FULL model -> node_fresh nx0 cs r logc base = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros r logc base cs cs' E R FULL model HC Hn. unfold node_fresh in Hn.
  set (b := match base with Some b => b | None => ELit 0 end) in Hn.
  set (e := esub (reg cs r) b) in Hn.
  destruct (Nat.ltb 0 r && Nat.ltb r 32 && Z.leb 0 logc && Z.leb logc 40 && Z.leb logc (ealign (kn cs) e)
            && AP.expr_vars_lt (nxt cs) b && AP.expr_vars_lt (nxt cs) e && fresh_ok nx0 cs)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hc Hfresh]. apply andb_prop in Hc as [Hc Hve]. apply andb_prop in Hc as [Hc Hvb].
  apply andb_prop in Hc as [Hc Hal]. apply andb_prop in Hc as [Hc H40]. apply andb_prop in Hc as [Hc H0].
  apply andb_prop in Hc as [Hr0 Hr32].
  apply Nat.ltb_lt in Hr0. apply Nat.ltb_lt in Hr32. apply Z.leb_le in H0. apply Z.leb_le in H40. apply Z.leb_le in Hal.
  destruct (xlo2 (kn cs) e) as [lo|] eqn:Hlo; [|discriminate].
  destruct (xhi2 (kn cs) e) as [hi|] eqn:Hhi; [|discriminate].
  injection Hn as <-.
  set (c := 2 ^ logc) in *. set (v := nxt cs) in *.
  pose proof (co_know _ _ _ _ _ HC) as HK.
  pose proof (xlo2_sound E _ (kn cs) e lo HK Hlo) as Hlo'.
  pose proof (xhi2_sound E _ (kn cs) e hi HK Hhi) as Hhi'.
  destruct (ealign_sound SEGS E _ (kn cs) e HK) as [Hea Hdiv].
  assert (Hc : 0 < c) by (unfold c; apply Z.pow_pos_nonneg; lia).
  assert (Hc2 : c <= 2 ^ 40) by (unfold c; apply Z.pow_le_mono_r; lia).
  assert (Hcd : (c | bv_unsigned (edenot E e))%Z).
  { eapply Z.divide_trans; [|exact Hdiv]. unfold c. apply pow2_divide_le. lia. }
  destruct Hcd as [q Hq].
  pose proof (u64_range (edenot E e)) as Hue.
  assert (Hq0 : 0 <= q) by nia.
  assert (Hq64 : q < 2 ^ 64) by nia.
  set (a := Z_to_bv 64 q). set (E' := ext1 E v a).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  destruct (fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (cs_ok_agree E E' cs R FULL model Hag Hfresh HC) as HC'.
  assert (Hev : edenot E' e = edenot E e) by (symmetry; eapply (edenot_agree' v); [exact Hag | exact Hve]).
  assert (Hbv : edenot E' b = edenot E b) by (symmetry; eapply (edenot_agree' v); [exact Hag | exact Hvb]).
  assert (Hrv : edenot E' (reg cs r) = edenot E (reg cs r)).
  { symmetry. eapply (edenot_agree' v); [exact Hag|]. unfold reg. apply nth_sr_vars_lt; [exact Fsr | lia]. }
  assert (Hne : edenot E' (escale c (EVar v)) = edenot E e).
  { unfold escale. rewrite mkMd_denot. cbn [edenot]. unfold E'. rewrite ext1_at. unfold a.
    apply bv_eq. rewrite u_mul64. rewrite (u_small c) by lia. rewrite (u_small q) by lia. rewrite Z.mod_small by nia. lia. }
  assert (He_sem : edenot E e = alu64 ALU_SUB (edenot E (reg cs r)) (edenot E b)) by (unfold e, esub; apply mkAlu_denot).
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  (* [comment removed for export] *)
  assert (HKf : know_ok SEGS E' (Mr E' cs model FULL)
            ((KRange (EVar v) ((lo + c - 1) / c) (hi / c) :: KRange (esub e (escale c (EVar v))) 0 0
               :: residue_fact (kn cs) e (escale c (EVar v)))
             ++ kn cs)).
  { apply Forall_app. split; [|exact (co_know _ _ _ _ _ HC')].
    constructor; [|constructor].
    - cbn [kentry_ok edenot]. unfold E' at 1 2. rewrite ext1_at. unfold a. rewrite u_small by lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      split; nia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - cbn [kentry_ok]. unfold esub. rewrite !mkAlu_denot, !Hne, !Hev.
      rewrite !u_sub64. rewrite Z.sub_diag, Z.mod_0_l by lia. lia.
    - eapply (residue_fact_sound E E' _ _ (kn cs) e); [exact HK | exact Hne |].
      intros e1 s1 Hd1. symmetry. eapply (edenot_agree' v); [exact Hag | exact (deand_vars v e e1 s1 Hd1 Hve)]. }
  destruct HC'; constructor; cbn [bump set_reg add_kn set_kn with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset]; try assumption.
  - apply regs_ok_respell; [exact co_regs0 | lia |].
    unfold eadd. rewrite mkAlu_denot, Hne, Hbv. fold (reg cs r). rewrite Hrv, He_sem.
    apply bv_eq. rewrite u_add64, u_sub64. pose proof (u64_range (edenot E (reg cs r))). pose proof (u64_range (edenot E b)).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite Zplus_mod_idemp_r. replace (bv_unsigned (edenot E b) + (bv_unsigned (edenot E (reg cs r)) - bv_unsigned (edenot E b))) with (bv_unsigned (edenot E (reg cs r))) by lia.
    rewrite Z.mod_small by lia. reflexivity.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - reflexivity.
Qed.


(* [comment removed for export] *)
Lemma listZ_eqb_eq : forall x y, listZ_eqb x y = true -> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y] H; cbn [listZ_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. rewrite (IH y H2), H1. reflexivity.
Qed.
Lemma spieces_eqb_eq : forall x y, spieces_eqb x y = true -> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y] H; cbn [spieces_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (IH y H2). f_equal.
  destruct a as [l|k], b as [l'|k']; cbn [spiece_eqb] in H1; try discriminate.
  - apply listZ_eqb_eq in H1. congruence.
  - apply Nat.eqb_eq in H1. congruence.
Qed.
Lemma shape_eqb_eq : forall x y, shape_eqb x y = true -> x = y.
Proof.
  induction x; intros y H; destruct y; cbn [shape_eqb] in H; try discriminate;
    repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end; try reflexivity.
  - apply Z.eqb_eq in H. congruence.
  - apply Z.eqb_eq in H. apply spieces_eqb_eq in X0. rewrite (IHx _ X). congruence.
  - rewrite (IHx1 _ H), (IHx2 _ X). reflexivity.
  - apply expr_eqb_eq in H. apply Z.eqb_eq in X1. rewrite (IHx1 _ X0), (IHx2 _ X). congruence.
  - apply Nat.eqb_eq in H. congruence.
Qed.

(* [comment removed for export] *)
Lemma sd_holes_eq : (forall h1 h2, HOLES h1 = HOLES h2) ->
  forall D E fs x y, shape_eqb_holes x y = true -> sd D E fs x = sd D E fs y.
Proof.
  intros HQ D E fs x. induction x; intros y H; destruct y; cbn [shape_eqb_holes] in H; try discriminate;
    repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end; cbn [sd]; try reflexivity.
  - apply Z.eqb_eq in H. congruence.
  - apply Z.eqb_eq in H. apply spieces_eqb_eq in X0. rewrite (IHx _ X). congruence.
  - rewrite (IHx1 _ H), (IHx2 _ X). reflexivity.
  - apply expr_eqb_eq in H. apply Z.eqb_eq in X1. rewrite (IHx1 _ X0), (IHx2 _ X). subst. reflexivity.
  - rewrite (HQ h h0). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma shape_ok2 : forall x y, (shape_eqb x y || (xp_hq xp && shape_eqb_holes x y))%bool = true ->
  forall D E fs, sd D E fs y = sd D E fs x.
Proof.
  intros x y H D E fs. apply orb_prop in H as [H|H].
  - apply shape_eqb_eq in H. subst y. reflexivity.
  - apply andb_prop in H as [Hq H]. symmetry. apply (sd_holes_eq (XPHQ Hq)). exact H.
Qed.

(* [comment removed for export] *)
Lemma sd_salt2_in : forall lc D E fs a b, D [] ->
  t_eq (t_alt2 (sd D E fs a) (sd D E fs b)) (sd D E fs (salt2_in lc a b)).
Proof.
  intros lc D E fs a b HD. unfold salt2_in, salt2c.
  assert (ID : t_eq (t_alt2 (sd D E fs a) (sd D E fs a)) (sd D E fs a)) by (intros tr; unfold t_alt2; tauto).
  destruct lc as [[| | |]|]; try (apply sd_salt2; exact HD).
  destruct (shape_eqb a b) eqn:He; [|apply sd_salt2; exact HD]. apply shape_eqb_eq in He. subst b. exact ID.
Qed.
Lemma salt2_in_vars : forall lc b x y, shape_vars_lt b x = true -> shape_vars_lt b y = true -> shape_vars_lt b (salt2_in lc x y) = true.
Proof.
  intros lc b x y Hx Hy. unfold salt2_in, salt2c. destruct lc as [[| | |]|]; try (apply salt2_vars; assumption).
  destruct (shape_eqb x y); [exact Hx | apply salt2_vars; assumption].
Qed.

(* [comment removed for export] *)
Lemma xinside_joint_sound : forall E M kn b1 k1 n1 b2 k2 n2,
  know_ok SEGS E M kn -> xinside_joint kn b1 k1 n1 b2 k2 n2 = true ->
  (estart E (SA b2 k2) <= estart E (SA b1 k1))%Z
  /\ (estart E (SA b1 k1) + elenZ E n1 <= estart E (SA b2 k2) + elenZ E n2)%Z.
Proof.
  intros E M kn b1 k1 n1 b2 k2 n2 Hkn H. unfold xinside_joint in H.
  apply andb_prop in H as [_ H].
  destruct (xlo kn b2) as [lo2|] eqn:Xl2; [|discriminate].
  destruct (xhi kn b2) as [hi2|] eqn:Xh2; [|discriminate].
  destruct (base_range kn b1) as [[lo1 hi1]|] eqn:Hb1; [|discriminate].
  destruct (xhi kn n1) as [h1|] eqn:Xh1; [|discriminate].
  destruct (xlo kn n2) as [l2|] eqn:Xl2n; [|discriminate].
  destruct (xhi kn (eadd (eaddz b1 k1) n1)) as [e|] eqn:Xe; [|discriminate].
  apply andb_prop in H as [H He]. apply andb_prop in H as [H Hw]. apply andb_prop in H as [H H0]. apply andb_prop in H as [Heq Ha].
  apply Z.eqb_eq in Heq. subst hi2. apply Z.leb_le in Ha. apply Z.leb_le in H0. apply Z.ltb_lt in Hw. apply Z.leb_le in He.
  pose proof (xlo_sound SEGS E M kn b2 lo2 Hkn Xl2). pose proof (xhi_sound SEGS E M kn b2 lo2 Hkn Xh2).
  pose proof (base_range_sound SEGS E M kn b1 lo1 hi1 Hkn Hb1) as [A1 B1].
  pose proof (xhi_sound SEGS E M kn n1 h1 Hkn Xh1). pose proof (xlo_sound SEGS E M kn n2 l2 Hkn Xl2n).
  pose proof (xhi_sound SEGS E M kn _ e Hkn Xe) as HXE.
  unfold eadd, eaddz in HXE. rewrite !mkAlu_denot in HXE. rewrite !u_add64 in HXE. rewrite edenot_lit, u_lit64 in HXE.
  pose proof (u64_range (edenot E b1)) as Rb1. pose proof (u64_range (edenot E n1)) as Rn1.
  unfold two64 in *.
  assert (K1 : (k1 mod 2 ^ 64 = k1 /\ 0 <= k1) \/ (k1 mod 2 ^ 64 = k1 + 2 ^ 64 /\ k1 < 0)).
  { destruct (Z_lt_le_dec k1 0) as [Hn|Hp].
    - right. split; [|lia]. rewrite <- (Z.mod_add k1 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
    - left. split; [|lia]. apply Z.mod_small. lia. }
  assert (E1 : (bv_unsigned (edenot E b1) + k1 mod 2 ^ 64) mod 2 ^ 64 = bv_unsigned (edenot E b1) + k1).
  { destruct K1 as [[-> Hk]|[-> Hk]].
    - apply Z.mod_small. lia.
    - rewrite Z.add_assoc. rewrite <- (Z.mod_add _ (-1) (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
  rewrite E1 in HXE. rewrite Z.mod_small in HXE by lia.
  unfold estart, elenZ. cbn [a_base a_off]. lia.
Qed.
Lemma xinside_j_sound : forall E M kn b1 k1 n1 b2 k2 n2,
  know_ok SEGS E M kn -> xinside_j kn b1 k1 n1 b2 k2 n2 = true ->
  (estart E (SA b2 k2) <= estart E (SA b1 k1))%Z
  /\ (estart E (SA b1 k1) + elenZ E n1 <= estart E (SA b2 k2) + elenZ E n2)%Z.
Proof.
  intros E M kn b1 k1 n1 b2 k2 n2 Hkn H. unfold xinside_j in H. apply orb_prop in H as [H|H].
  - exact (xinside_sound SEGS E M kn b1 k1 n1 b2 k2 n2 Hkn H).
  - exact (xinside_joint_sound E M kn b1 k1 n1 b2 k2 n2 Hkn H).
Qed.

Lemma find_disj_sound : forall E M k b1 b2 c1 o1 n1 c2 o2 n2,
  know_ok SEGS E M k -> find_disj k b1 b2 = Some (c1, o1, n1, c2, o2, n2) ->
  estart E (SA c1 o1) + elenZ E n1 <= estart E (SA c2 o2) \/ estart E (SA c2 o2) + elenZ E n2 <= estart E (SA c1 o1).
Proof.
  intros E M k b1 b2 c1 o1 n1 c2 o2 n2 HK. induction k as [|K k IH]; intros H; [discriminate|].
  inversion HK as [|K' k' HKK HK']; subst.
  cbn [find_disj] in H.
  destruct K as [| | | | | | |[d1 p1] m1 [d2 p2] m2| |]; try exact (IH HK' H).
  destruct (expr_eqb d1 b1 && expr_eqb d2 b2)%bool.
  - injection H as <- <- <- <- <- <-. exact HKK.
  - destruct (expr_eqb d1 b2 && expr_eqb d2 b1)%bool; [|exact (IH HK' H)].
    injection H as <- <- <- <- <- <-. cbn [kentry_ok] in HKK. lia.
Qed.

(* [comment removed for export] *)
Definition disj_res_ok (E : env) (r : expr * Z * expr * expr * Z * expr) : Prop :=
  match r with (c1, o1, n1, c2, o2, n2) =>
    estart E (SA c1 o1) + elenZ E n1 <= estart E (SA c2 o2) \/ estart E (SA c2 o2) + elenZ E n2 <= estart E (SA c1 o1) end.
Lemma find_disj_off_all_sound : forall E M k e1 z1 e2 z2,
  know_ok SEGS E M k -> Forall (disj_res_ok E) (find_disj_off_all k e1 z1 e2 z2).
Proof.
  intros E M k e1 z1 e2 z2 HK. induction k as [|K k IH]; [constructor|].
  inversion HK as [|K' k' HKK HK']; subst.
  cbn [find_disj_off_all].
  destruct K as [| | | | | | |[d1 p1] m1 [d2 p2] m2| |]; try exact (IH HK').
  destruct (expr_eqb d1 e1 && Z.eqb p1 z1 && expr_eqb d2 e2 && Z.eqb p2 z2)%bool.
  - constructor; [exact HKK | exact (IH HK')].
  - destruct (expr_eqb d1 e2 && Z.eqb p1 z2 && expr_eqb d2 e1 && Z.eqb p2 z1)%bool; [|exact (IH HK')].
    constructor; [|exact (IH HK')]. cbn [kentry_ok] in HKK. cbn [disj_res_ok]. lia.
Qed.
Lemma pick_longest_ok : forall E best l, disj_res_ok E best -> Forall (disj_res_ok E) l -> disj_res_ok E (pick_longest best l).
Proof.
  intros E best l. revert best. induction l as [|r l IH]; intros best Hb Hl; [exact Hb|].
  inversion Hl as [|r' l' Hr Hl']; subst. cbn [pick_longest]. apply IH; [|exact Hl'].
  destruct (Z.ltb _ _); assumption.
Qed.
Lemma find_disj_off_sound : forall E M k e1 z1 e2 z2 c1 o1 n1 c2 o2 n2,
  know_ok SEGS E M k -> find_disj_off k e1 z1 e2 z2 = Some (c1, o1, n1, c2, o2, n2) ->
  estart E (SA c1 o1) + elenZ E n1 <= estart E (SA c2 o2) \/ estart E (SA c2 o2) + elenZ E n2 <= estart E (SA c1 o1).
Proof.
  intros E M k e1 z1 e2 z2 c1 o1 n1 c2 o2 n2 HK H. unfold find_disj_off in H.
  pose proof (find_disj_off_all_sound E M k e1 z1 e2 z2 HK) as HA.
  destruct (find_disj_off_all k e1 z1 e2 z2) as [|r l]; [discriminate|]. injection H as Hp.
  inversion HA as [|r' l' Hr Hl]; subst.
  pose proof (pick_longest_ok E r l Hr Hl) as X. rewrite Hp in X. exact X.
Qed.
Lemma find_disj2_sound : forall E M k b1 b2 c1 o1 n1 c2 o2 n2,
  know_ok SEGS E M k -> find_disj2 k b1 b2 = Some (c1, o1, n1, c2, o2, n2) ->
  estart E (SA c1 o1) + elenZ E n1 <= estart E (SA c2 o2) \/ estart E (SA c2 o2) + elenZ E n2 <= estart E (SA c1 o1).
Proof.
  intros E M k b1 b2 c1 o1 n1 c2 o2 n2 HK H. unfold find_disj2 in H.
  destruct (find_disj k b1 b2) as [r|] eqn:Hf.
  - injection H as ->. exact (find_disj_sound E M k b1 b2 c1 o1 n1 c2 o2 n2 HK Hf).
  - destruct (split_lit b1) as [e1 z1]. destruct (split_lit b2) as [e2 z2].
    exact (find_disj_off_sound E M k e1 z1 e2 z2 c1 o1 n1 c2 o2 n2 HK H).
Qed.
Lemma disj_side_fact_sound : forall E M k cA oA nA cB oB K,
  know_ok SEGS E M k -> disj_side_fact A k cA oA nA cB oB = Some K ->
  0 <= estart E (SA cA oA) -> estart E (SA cB oB) < 2 ^ 64 ->
  estart E (SA cA oA) + elenZ E nA <= estart E (SA cB oB) ->
  kentry_ok SEGS E M K.
Proof.
  intros E M k cA oA nA cB oB K HK H HA HB Hle. unfold disj_side_fact in H.
  destruct (xlo2 k nA) as [n|] eqn:Hn; [|discriminate].
  destruct (base_range k cB) as [[blo bhi]|] eqn:Hbr; [|discriminate].
  cbv zeta in H.
  destruct (Z.leb 0 n && Z.leb n (disj_side_hi A k cA oA n bhi oB))%bool eqn:Ht; [|discriminate]. injection H as <-.
  apply andb_prop in Ht as [H0 H1]. apply Z.leb_le in H0. apply Z.leb_le in H1.
  pose proof (xlo2_sound E M k nA n HK Hn) as Ln. pose proof (base_range_sound SEGS E M k cB blo bhi HK Hbr) as [_ Bh].
  assert (HI : bhi + oB - estart E (SA cA oA) <= disj_side_hi A k cA oA n bhi oB /\ disj_side_hi A k cA oA n bhi oB <= bhi + oB).
  { unfold disj_side_hi. destruct (plain A); [lia|]. destruct (base_range k cA) as [[alo ahi]|] eqn:Har; [|lia].
    pose proof (base_range_sound SEGS E M k cA alo ahi HK Har) as [Al _]. unfold estart in *; cbn [a_base a_off] in *. cbv zeta. destruct (Z.leb _ _); lia. }
  destruct HI as [HI1 HI2]. set (dhi := disj_side_hi A k cA oA n bhi oB) in *. clearbody dhi.
  pose proof (u64_range (edenot E nA)) as RnA.
  cbn [kentry_ok]. unfold esub, eaddz. rewrite !mkAlu_denot, u_sub64, !u_add64. cbn [edenot]. rewrite !u_lit64.
  unfold estart, elenZ in *; cbn [a_base a_off] in *.
  pose proof (u64_range (edenot E cA)) as RA. pose proof (u64_range (edenot E cB)) as RB. unfold two64.
  set (uA := bv_unsigned (edenot E cA)) in *. set (uB := bv_unsigned (edenot E cB)) in *. set (uN := bv_unsigned (edenot E nA)) in *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (E1 : (uB + oB mod 2 ^ 64) mod 2 ^ 64 = uB + oB).
  { rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia. }
  assert (E2 : (uA + oA mod 2 ^ 64) mod 2 ^ 64 = uA + oA).
  { rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia. }
  rewrite E1, E2. rewrite Z.mod_small by lia. lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma casedisj_sound : forall cs b1 b2 csa csb E R FULL model,
  cs_ok E cs R FULL model -> node_casedisj A cs b1 b2 = Some (csa, csb) ->
  (cs_ok E csa R FULL model /\ pc csa = pc cs) \/ (cs_ok E csb R FULL model /\ pc csb = pc cs).
Proof.
  intros cs b1 b2 csa csb E R FULL model HC H. unfold node_casedisj in H.
  pose proof (co_know _ _ _ _ _ HC) as HK.
  destruct (find_disj2 (kn cs) b1 b2) as [[[[[[c1 o1] n1] c2] o2] n2]|] eqn:Hf; [|discriminate].
  destruct (flat_x (kn cs) c1 o1 n1) eqn:F1; [|discriminate].
  destruct (flat_x (kn cs) c2 o2 n2) eqn:F2; [|cbn in H; discriminate].
  destruct (disj_side_fact A (kn cs) c1 o1 n1 c2 o2) as [K1|] eqn:D1; [|discriminate].
  destruct (disj_side_fact A (kn cs) c2 o2 n2 c1 o1) as [K2|] eqn:D2; [|discriminate].
  injection H as <- <-.
  pose proof (flat_x_sound E _ (kn cs) c1 o1 n1 HK F1) as (A1 & A2 & A3).
  pose proof (flat_x_sound E _ (kn cs) c2 o2 n2 HK F2) as (B1 & B2 & B3).
  unfold elenZ in *.
  destruct (find_disj2_sound E _ (kn cs) b1 b2 c1 o1 n1 c2 o2 n2 HK Hf) as [Hd|Hd].
  - left. split; [|reflexivity]. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
    eapply disj_side_fact_sound; [exact HK | exact D1 | lia | unfold elenZ in *; lia | exact Hd].
  - right. split; [|reflexivity]. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
    eapply disj_side_fact_sound; [exact HK | exact D2 | lia | unfold elenZ in *; lia | exact Hd].
Qed.

(* [comment removed for export] *)
Lemma disj_side_dead_sound : forall E M k cA oA nA cB oB,
  know_ok SEGS E M k -> disj_side_dead k cA oA nA cB oB = true ->
  0 <= estart E (SA cA oA) ->
  ~ (estart E (SA cA oA) + elenZ E nA <= estart E (SA cB oB)).
Proof.
  intros E M k cA oA nA cB oB HK H HA Hle. unfold disj_side_dead in H.
  destruct (xlo2 k nA) as [n|] eqn:Hn; [|discriminate].
  destruct (base_range k cB) as [[blo bhi]|] eqn:Hbr; [|discriminate].
  destruct (base_range k cA) as [[alo ahi]|] eqn:Har; [|discriminate]. apply Z.ltb_lt in H.
  pose proof (xlo2_sound E M k nA n HK Hn) as Ln. pose proof (base_range_sound SEGS E M k cB blo bhi HK Hbr) as [_ Bh].
  pose proof (base_range_sound SEGS E M k cA alo ahi HK Har) as [Al _].
  unfold estart, elenZ in *; cbn [a_base a_off] in *. lia.
Qed.
Lemma casedisjJ_sound : forall cs b1 b2 csa csb (da db : bool) E R FULL model,
  cs_ok E cs R FULL model -> node_casedisj A cs b1 b2 = Some (csa, csb) -> casedisj_dead cs b1 b2 = (da, db) ->
  (da = false /\ cs_ok E csa R FULL model /\ pc csa = pc cs)
  \/ (db = false /\ cs_ok E csb R FULL model /\ pc csb = pc cs).
Proof.
  intros cs b1 b2 csa csb da db E R FULL model HC H HD. unfold node_casedisj in H. unfold casedisj_dead in HD.
  pose proof (co_know _ _ _ _ _ HC) as HK.
  destruct (find_disj2 (kn cs) b1 b2) as [[[[[[c1 o1] n1] c2] o2] n2]|] eqn:Hf; [|discriminate].
  destruct (flat_x (kn cs) c1 o1 n1) eqn:F1; [|discriminate].
  destruct (flat_x (kn cs) c2 o2 n2) eqn:F2; [|cbn in H; discriminate].
  destruct (disj_side_fact A (kn cs) c1 o1 n1 c2 o2) as [K1|] eqn:D1; [|discriminate].
  destruct (disj_side_fact A (kn cs) c2 o2 n2 c1 o1) as [K2|] eqn:D2; [|discriminate].
  injection H as <- <-. injection HD as HDa HDb.
  pose proof (flat_x_sound E _ (kn cs) c1 o1 n1 HK F1) as (A1 & A2 & A3).
  pose proof (flat_x_sound E _ (kn cs) c2 o2 n2 HK F2) as (B1 & B2 & B3).
  unfold elenZ in *.
  destruct (find_disj2_sound E _ (kn cs) b1 b2 c1 o1 n1 c2 o2 n2 HK Hf) as [Hd|Hd].
  - left. split.
    { destruct da; [|reflexivity]. exfalso. exact (disj_side_dead_sound E _ (kn cs) c1 o1 n1 c2 o2 HK HDa ltac:(lia) Hd). }
    split; [|reflexivity]. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
    eapply disj_side_fact_sound; [exact HK | exact D1 | lia | unfold elenZ in *; lia | exact Hd].
  - right. split.
    { destruct db; [|reflexivity]. exfalso. exact (disj_side_dead_sound E _ (kn cs) c2 o2 n2 c1 o1 HK HDb ltac:(lia) Hd). }
    split; [|reflexivity]. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
    eapply disj_side_fact_sound; [exact HK | exact D2 | lia | unfold elenZ in *; lia | exact Hd].
Qed.

(* [comment removed for export] *)
Lemma node_casedisjJ_sound : forall cs b1 b2 csl ocb E R FULL model,
  cs_ok E cs R FULL model -> node_casedisjJ A cs b1 b2 = Some (csl, ocb) ->
  match ocb with
  | None => cs_ok E csl R FULL model /\ exists K, csl = set_kn cs (K :: kn cs)
  | Some csb => ((cs_ok E csl R FULL model) \/ (cs_ok E csb R FULL model))
                /\ (exists K, csl = set_kn cs (K :: kn cs)) /\ (exists K, csb = set_kn cs (K :: kn cs))
  end.
Proof.
  intros cs b1 b2 csl ocb E R FULL model HC H. unfold node_casedisjJ in H.
  pose proof (co_know _ _ _ _ _ HC) as HK.
  destruct (find_disj2 (kn cs) b1 b2) as [[[[[[c1 o1] n1] c2] o2] n2]|] eqn:Hf; [|discriminate].
  destruct (flat_x (kn cs) c1 o1 n1) eqn:F1; [|discriminate].
  destruct (flat_x (kn cs) c2 o2 n2) eqn:F2; [|discriminate]. cbn [andb] in H.
  pose proof (flat_x_sound E _ (kn cs) c1 o1 n1 HK F1) as (A1 & A2 & A3).
  pose proof (flat_x_sound E _ (kn cs) c2 o2 n2 HK F2) as (B1 & B2 & B3).
  unfold elenZ in *.
  pose proof (find_disj2_sound E _ (kn cs) b1 b2 c1 o1 n1 c2 o2 n2 HK Hf) as Hd. unfold elenZ in Hd.
  assert (OKA : forall K1, disj_side_fact A (kn cs) c1 o1 n1 c2 o2 = Some K1 ->
            estart E (SA c1 o1) + bv_unsigned (edenot E n1) <= estart E (SA c2 o2) -> cs_ok E (add_kn cs [K1]) R FULL model).
  { intros K1 D1 Hs. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
    eapply disj_side_fact_sound; [exact HK | exact D1 | lia | unfold elenZ in *; lia | exact Hs]. }
  assert (OKB : forall K2, disj_side_fact A (kn cs) c2 o2 n2 c1 o1 = Some K2 ->
            estart E (SA c2 o2) + bv_unsigned (edenot E n2) <= estart E (SA c1 o1) -> cs_ok E (add_kn cs [K2]) R FULL model).
  { intros K2 D2 Hs. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
    eapply disj_side_fact_sound; [exact HK | exact D2 | lia | unfold elenZ in *; lia | exact Hs]. }
  destruct (disj_side_dead (kn cs) c1 o1 n1 c2 o2) eqn:Da; destruct (disj_side_dead (kn cs) c2 o2 n2 c1 o1) eqn:Db.
  - discriminate.
  - destruct (disj_side_fact A (kn cs) c2 o2 n2 c1 o1) as [K2|] eqn:D2; [|discriminate]. injection H as <- <-.
    split; [|exists K2; reflexivity]. apply (OKB K2 ltac:(first [exact D2 | reflexivity])).
    destruct Hd as [Hd|Hd]; [|exact Hd]. exfalso. exact (disj_side_dead_sound E _ (kn cs) c1 o1 n1 c2 o2 HK Da ltac:(lia) Hd).
  - destruct (disj_side_fact A (kn cs) c1 o1 n1 c2 o2) as [K1|] eqn:D1; [|discriminate]. injection H as <- <-.
    split; [|exists K1; reflexivity]. apply (OKA K1 ltac:(first [exact D1 | reflexivity])).
    destruct Hd as [Hd|Hd]; [exact Hd|]. exfalso. exact (disj_side_dead_sound E _ (kn cs) c2 o2 n2 c1 o1 HK Db ltac:(lia) Hd).
  - destruct (disj_side_fact A (kn cs) c1 o1 n1 c2 o2) as [K1|] eqn:D1; [|discriminate].
    destruct (disj_side_fact A (kn cs) c2 o2 n2 c1 o1) as [K2|] eqn:D2; [|discriminate]. injection H as <- <-.
    split; [|split; [exists K1 | exists K2]; reflexivity].
    destruct Hd as [Hd|Hd]; [left; exact (OKA K1 ltac:(first [exact D1 | reflexivity]) Hd) | right; exact (OKB K2 ltac:(first [exact D2 | reflexivity]) Hd)].
Qed.

Lemma shadow_of_val : forall E M k b n sb sk sn,
  know_ok SEGS E M k -> shadow_of A k b n = (sb, sk, sn) ->
  flat_x k sb sk sn = true ->
  estart E (SA sb sk) = (bv_unsigned (edenot E b) / 8 + shadow_off A) mod 2 ^ 64
  /\ elenZ E sn = bv_unsigned (edenot E n) / 8.
Proof.
  intros E M k b n sb sk sn HK Hs Hf. unfold shadow_of in Hs.
  destruct (split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hsp. injection Hs as E1 E2 E3. subst sb' sk'. rewrite <- E3 in *.
  pose proof (flat_x_sound E _ k sb sk (mkSrl k n 3) HK Hf) as (F1 & F2 & F3).
  pose proof (split_lit_denot E _ sb sk Hsp) as Hd.
  assert (S3 : forall x, bv_unsigned (edenot E (mkSrl k x 3)) = bv_unsigned (edenot E x) / 8).
  { intros x. rewrite (mkSrl_denot SEGS E _ k x 3 (Z_to_bv 64 3) HK) by reflexivity.
    rewrite u_srl64. rewrite u64_lit by lia. reflexivity. }
  split.
  - unfold eadd in Hd. rewrite mkAlu_denot in Hd. apply (f_equal bv_unsigned) in Hd.
    rewrite u_add64, S3 in Hd. cbn [edenot] in Hd. rewrite (u64_lit (shadow_off A)) in Hd by (pose proof SHADOW_ok as SO; unfold shadow_ok in SO; lia).
    rewrite Z_to_bv_unsigned in Hd. unfold bv_wrap, bv_modulus in Hd. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hd.
    unfold estart; cbn [a_base a_off].
    pose proof (u64_range (edenot E (mkSrl k n 3))). unfold elenZ, estart in *; cbn [a_base a_off] in *.
    unfold two64 in *. rewrite (Z.mod_small (bv_unsigned (edenot E sb) + sk)) in Hd by lia.
    rewrite <- Hd. reflexivity.
  - unfold elenZ. apply S3.
Qed.

Lemma shdisj_sound : forall cs b1 n1 b2 n2 cs' E R FULL model,
  cs_ok E cs R FULL model -> node_shdisj A cs b1 n1 b2 n2 = Some cs' -> cs_ok E cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros cs b1 n1 b2 n2 cs' E R FULL model HC H. rewrite node_shdisj_eq in H. (* [comment removed for export] *) unfold node_shdisj_ref in H.
  pose proof (co_know _ _ _ _ _ HC) as HK.
  destruct (split_lit b1) as [c1 o1] eqn:S1. destruct (split_lit b2) as [c2 o2] eqn:S2.
  destruct (shadow_of A (kn cs) b1 n1) as [[sb1 sk1] sn1] eqn:H1. destruct (shadow_of A (kn cs) b2 n2) as [[sb2 sk2] sn2] eqn:H2.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection H as <-.
  apply andb_prop in Hc as [Hc Hap]. apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hc Fs2]. apply andb_prop in Hc as [Hc Fs1].
  apply andb_prop in Hc as [Hc F2]. apply andb_prop in Hc as [Hc F1].
  apply andb_prop in Hc as [Hc Ln2]. apply andb_prop in Hc as [Hc Lb2]. apply andb_prop in Hc as [Lb1 Ln1].
  apply Z.leb_le in Lb1. apply Z.leb_le in Ln1. apply Z.leb_le in Lb2. apply Z.leb_le in Ln2.
  split; [|reflexivity]. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
  destruct (xhi (kn cs) b1) as [h1|] eqn:Xh1; [|discriminate]. destruct (xhi (kn cs) n1) as [m1|] eqn:Xm1; [|discriminate].
  destruct (xhi (kn cs) b2) as [h2|] eqn:Xh2; [|discriminate]. destruct (xhi (kn cs) n2) as [m2|] eqn:Xm2; [|discriminate].
  apply andb_prop in Hhi as [Y1 Y2]. (* [comment removed for export] *)
  pose proof (xhi_sound SEGS E _ (kn cs) b1 h1 HK Xh1) as B1. pose proof (xhi_sound SEGS E _ (kn cs) n1 m1 HK Xm1) as M1.
  pose proof (xhi_sound SEGS E _ (kn cs) b2 h2 HK Xh2) as B2. pose proof (xhi_sound SEGS E _ (kn cs) n2 m2 HK Xm2) as M2.
  pose proof (flat_x_sound E _ (kn cs) c1 o1 n1 HK F1) as (A1 & A2 & A3).
  pose proof (flat_x_sound E _ (kn cs) c2 o2 n2 HK F2) as (C1 & C2 & C3).
  pose proof (u64_range (edenot E n1)) as Rn1. pose proof (u64_range (edenot E n2)) as Rn2.
  pose proof (u_of_split E b1 c1 o1 S1 ltac:(lia)) as U1. pose proof (u_of_split E b2 c2 o2 S2 ltac:(lia)) as U2.
  pose proof (ranges_apart_x_sound SEGS E _ (kn cs) c1 o1 n1 c2 o2 n2 HK Hap) as AP0.
  destruct (shadow_of_val E _ (kn cs) b1 n1 sb1 sk1 sn1 HK H1 Fs1) as [V1 L1].
  destruct (shadow_of_val E _ (kn cs) b2 n2 sb2 sk2 sn2 HK H2 Fs2) as [V2 L2].
  pose proof SHADOW_ok as SO; unfold shadow_ok in SO.
  cbn [kentry_ok]. rewrite V1, V2, L1, L2.
  destruct (ealign_sound SEGS E _ (kn cs) b1 HK) as [_ D1]. destruct (ealign_sound SEGS E _ (kn cs) n1 HK) as [_ D2].
  destruct (ealign_sound SEGS E _ (kn cs) b2 HK) as [_ D3]. destruct (ealign_sound SEGS E _ (kn cs) n2 HK) as [_ D4].
  assert (P8 : forall e, 3 <= ealign (kn cs) e -> (2 ^ ealign (kn cs) e | bv_unsigned (edenot E e)) -> (8 | bv_unsigned (edenot E e))).
  { intros e He Hd. eapply Z.divide_trans; [|exact Hd]. change 8 with (2 ^ 3). apply pow2_divide_le. lia. }
  pose proof (P8 _ Lb1 D1) as [q1 Q1]. pose proof (P8 _ Ln1 D2) as [q2 Q2]. pose proof (P8 _ Lb2 D3) as [q3 Q3]. pose proof (P8 _ Ln2 D4) as [q4 Q4].
  unfold elenZ in AP0. rewrite <- U1, <- U2 in AP0.
  pose proof (u64_range (edenot E b1)) as Rb1. pose proof (u64_range (edenot E b2)) as Rb2.
  generalize dependent AP0. rewrite Q1, Q2, Q3, Q4. rewrite Q1 in Rb1, B1. rewrite Q2 in Rn1, M1. rewrite Q3 in Rb2, B2. rewrite Q4 in Rn2, M2.
  rewrite !Z.div_mul by lia. intros AP0.
  rewrite (Z.mod_small (q1 + shadow_off A)) by lia. rewrite (Z.mod_small (q3 + shadow_off A)) by lia.
  clear - AP0 Rb1 Rb2 Rn1 Rn2 SO. lia.
Qed.

(* [comment removed for export] *)
Lemma expr_vars_lt_mono : forall b b' e, AP.expr_vars_lt b e = true -> (b <= b')%nat -> AP.expr_vars_lt b' e = true.
Proof.
  intros b b' e H Hle. induction e; cbn [AP.expr_vars_lt] in *; try reflexivity;
    try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity); try (apply IHe; exact H).
  apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
Qed.
Lemma sr_vars_lt_mono : forall b b' sr, AP.sr_vars_lt b sr = true -> (b <= b')%nat -> AP.sr_vars_lt b' sr = true.
Proof.
  intros b b' sr H Hle. induction sr; cbn [AP.sr_vars_lt] in *; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (expr_vars_lt_mono _ _ _ H1 Hle), (IHsr H2). reflexivity.
Qed.
Lemma sr_vars_lt_upd : forall b sr n e, AP.sr_vars_lt b sr = true -> AP.expr_vars_lt b e = true -> AP.sr_vars_lt b (sr_upd sr n e) = true.
Proof.
  intros b sr n e. revert sr. induction n as [|n IH]; intros sr Hsr He.
  - destruct sr; cbn [sr_upd AP.sr_vars_lt]; cbn [AP.sr_vars_lt] in Hsr; rewrite He; [reflexivity|].
    apply andb_prop in Hsr as [_ H2]. rewrite H2. reflexivity.
  - destruct sr; cbn [sr_upd AP.sr_vars_lt]; cbn [AP.sr_vars_lt] in Hsr.
    + rewrite IH by (reflexivity || exact He). reflexivity.
    + apply andb_prop in Hsr as [H1 H2]. rewrite H1, (IH _ H2 He). reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint ext_list (E : env) (nx : nat) (vals : list word) : env :=
  match vals with
  | [] => E
  | v :: rest => ext_list (ext1 E nx v) (Datatypes.S nx) rest
  end.

Lemma ext_list_agree : forall E nx vals, env_agree nx E (ext_list E nx vals).
Proof.
  intros E nx vals. revert E nx. induction vals as [|v rest IH]; intros E nx; cbn [ext_list].
  - apply env_agree_refl.
  - eapply env_agree_trans; [apply ext1_agree|]. eapply env_agree_le; [apply IH | lia].
Qed.

Lemma ext_list_at : forall E nx vals i, (i < length vals)%nat -> ev (ext_list E nx vals) (nx + i) = nth i vals (Z_to_bv 64 0).
Proof.
  intros E nx vals. revert E nx. induction vals as [|v rest IH]; intros E nx i Hi; cbn [length] in Hi; [lia|].
  cbn [ext_list]. destruct i as [|i].
  - rewrite Nat.add_0_r. pose proof (ext_list_agree (ext1 E nx v) (Datatypes.S nx) rest) as [Hag _].
    rewrite <- Hag by lia. cbn [nth]. apply ext1_at.
  - replace (nx + Datatypes.S i)%nat with (Datatypes.S nx + i)%nat by lia. cbn [nth]. apply IH. lia.
Qed.

Lemma regs_ok_sr_fresh : forall E sr R rs nx,
  regs_ok E sr R -> AP.sr_vars_lt nx sr = true -> Forall (fun r => 0 < r < 32)%nat rs ->
  regs_ok (ext_list E nx (map (fun r => getr R (Z_to_bv 5 (Z.of_nat r))) rs)) (sr_fresh sr rs nx) R.
Proof.
  intros E sr R rs. revert E sr. induction rs as [|r rest IH]; intros E sr nx HR Hsr Hrs; cbn [sr_fresh map ext_list].
  - exact HR.
  - apply Forall_cons_iff in Hrs as [Hr Hrest].
    apply IH.
    + apply regs_ok_respell.
      * eapply regs_ok_agree'; [apply ext1_agree | exact Hsr | exact HR].
      * exact Hr.
      * cbn [edenot]. rewrite ext1_at.
        pose proof (regs_ok_agree' nx E (ext1 E nx (getr R (Z_to_bv 5 (Z.of_nat r)))) sr R (ext1_agree _ _ _) Hsr HR) as HR'.
        etransitivity; [exact (HR' (Z_to_bv 5 (Z.of_nat r)))|]. unfold sr_get.
        assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat r)) 0%bv = false).
        { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
          change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
          replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
        rewrite Hnz, ridx_lit by lia. reflexivity.
    + apply sr_vars_lt_upd; [eapply sr_vars_lt_mono; [exact Hsr | lia] |]. cbn [AP.expr_vars_lt]. apply Nat.ltb_lt. lia.
    + exact Hrest.
Qed.

Lemma havoc_sound : forall E cs R FULL model rs cs',
  cs_ok E cs R FULL model -> node_havoc nx0 cs rs = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model rs cs' HC H. unfold node_havoc in H.
  destruct (fresh_ok nx0 cs && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) rs)%bool eqn:Hc; [|discriminate].
  injection H as <-. apply andb_prop in Hc as [Hf Hrs].
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (E' := ext_list E (nxt cs) (map (fun r => getr R (Z_to_bv 5 (Z.of_nat r))) rs)).
  assert (Hag : env_agree (nxt cs) E E') by apply ext_list_agree.
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  pose proof (cs_ok_agree E E' cs R FULL model Hag Hf HC) as HC'.
  destruct HC'; constructor; cbn [with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset]; try assumption; [|reflexivity].
  apply regs_ok_sr_fresh; [exact (co_regs _ _ _ _ _ HC) | exact Fsr |].
  apply Forall_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) Hrs r Hr) as Hb.
  apply andb_prop in Hb as [H1 H2]. apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2. lia.
Qed.

(* [comment removed for export] *)
Fixpoint kn_bigexprs (K : nat) (k : list kentry) : list expr :=
  match k with
  | [] => []
  | KWord a w v :: r => if bigb K v then v :: kn_bigexprs K r else kn_bigexprs K r
  | _ :: r => kn_bigexprs K r
  end.

Lemma kentry_vars_lt_mono : forall b b' K, AP.kentry_vars_lt b K = true -> (b <= b')%nat -> AP.kentry_vars_lt b' K = true.
Proof.
  intros b b' K H Hle.
  assert (E1 : forall e, AP.expr_vars_lt b e = true -> AP.expr_vars_lt b' e = true) by (intros; eapply expr_vars_lt_mono; eassumption).
  assert (A1 : forall a, AP.saddr_vars_lt b a = true -> AP.saddr_vars_lt b' a = true) by (intros [? ?]; unfold AP.saddr_vars_lt; apply E1).
  destruct K; cbn [AP.kentry_vars_lt] in *;
    repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end;
    repeat match goal with
    | Y : AP.expr_vars_lt b ?e = true |- _ => rewrite (E1 e Y); clear Y
    | Y : AP.saddr_vars_lt b ?a = true |- _ => rewrite (A1 a Y); clear Y
    end; reflexivity.
Qed.
Lemma kn_vars_lt_mono' : forall b b' k, AP.kn_vars_lt b k = true -> (b <= b')%nat -> AP.kn_vars_lt b' k = true.
Proof.
  intros b b' k H Hle. induction k as [|K k IH]; [reflexivity|]. cbn [AP.kn_vars_lt] in *. apply andb_prop in H as [H1 H2].
  rewrite (kentry_vars_lt_mono b b' K H1 Hle), (IH H2). reflexivity.
Qed.

Lemma kn_bigsubst_len : forall K k nx, snd (kn_bigsubst K k nx) = length (kn_bigexprs K k).
Proof.
  intros K k. induction k as [|x r IH]; intros nx; [reflexivity|].
  cbn [kn_bigsubst kn_bigexprs]. destruct x as [a w v| | | | | | | | |]; try (specialize (IH nx); destruct (kn_bigsubst K r nx); cbn in *; exact IH).
  destruct (bigb K v).
  - specialize (IH (Datatypes.S nx)). destruct (kn_bigsubst K r (Datatypes.S nx)). cbn in *. rewrite IH. reflexivity.
  - specialize (IH nx). destruct (kn_bigsubst K r nx). cbn in *. exact IH.
Qed.

Lemma kn_bigsubst_sound : forall K k nx E2 M,
  know_ok SEGS E2 M k -> AP.kn_vars_lt nx k = true ->
  (forall i, (i < length (kn_bigexprs K k))%nat -> ev E2 (nx + i) = edenot E2 (nth i (kn_bigexprs K k) (ELit 0))) ->
  know_ok SEGS E2 M (fst (kn_bigsubst K k nx)).
Proof.
  intros K k. induction k as [|x r IH]; intros nx E2 M HK Hv Hvals; [constructor|].
  inversion HK as [|x' r' Hx Hr]; subst. cbn [AP.kn_vars_lt] in Hv. apply andb_prop in Hv as [Hvx Hvr].
  cbn [kn_bigsubst]. cbn [kn_bigexprs] in Hvals.
  assert (DFLT : (forall i, (i < length (kn_bigexprs K r))%nat -> ev E2 (nx + i) = edenot E2 (nth i (kn_bigexprs K r) (ELit 0))) ->
                 know_ok SEGS E2 M (fst (let '(r', c) := kn_bigsubst K r nx in (x :: r', c)))).
  { intros Hvals'. pose proof (IH nx E2 M Hr Hvr Hvals') as IH'. destruct (kn_bigsubst K r nx) as [r' c]. cbn [fst] in *. constructor; [exact Hx | apply IH']. }
  destruct x as [a w v| | | | | | | | |]; try (apply DFLT; exact Hvals).
  destruct (bigb K v) eqn:Hb; [|apply DFLT; exact Hvals]. clear DFLT.
  pose proof (IH (Datatypes.S nx) E2 M Hr ltac:(eapply kn_vars_lt_mono'; [exact Hvr | lia])) as IH'.
  destruct (kn_bigsubst K r (Datatypes.S nx)) as [r' c] eqn:Hs. cbn [fst]. constructor.
  - cbn [kentry_ok] in Hx |- *. destruct Hx as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
    rewrite H3. f_equal. f_equal. cbn [edenot]. symmetry. replace nx with (nx + 0)%nat by lia. rewrite (Hvals 0%nat ltac:(cbn; lia)). reflexivity.
  - apply IH'. intros i Hi. replace (Datatypes.S nx + i)%nat with (nx + Datatypes.S i)%nat by lia. rewrite (Hvals (Datatypes.S i) ltac:(cbn; lia)). reflexivity.
Qed.

Lemma node_havoc_nxt : forall cs rs cs1, node_havoc nx0 cs rs = Some cs1 -> nxt cs1 = (nxt cs + length rs)%nat /\ pc cs1 = pc cs.
Proof.
  intros cs rs cs1 H. unfold node_havoc in H.
  destruct (fresh_ok nx0 cs && forallb (fun r : nat => Nat.ltb 0 r && Nat.ltb r 32) rs)%bool; [|discriminate].
  injection H as <-. split; reflexivity.
Qed.

Lemma havocbig_sound : forall E cs R FULL model K cs',
  cs_ok E cs R FULL model -> node_havocbig nx0 cs K = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model K cs' HC H. unfold node_havocbig in H.
  destruct (node_havoc nx0 cs _) as [cs1|] eqn:Hh; [|discriminate].
  destruct (fresh_ok nx0 cs1) eqn:Hf1; [|discriminate].
  destruct (kn_bigsubst K (kn cs1) (nxt cs1)) as [k' c] eqn:Hs. injection H as <-.
  destruct (havoc_sound E cs R FULL model _ cs1 HC Hh) as (E1 & [Hag0 Hag1] & HC1 & Hpc1).
  destruct (fresh_ok_parts cs1 Hf1) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (vals := map (edenot E1) (kn_bigexprs K (kn cs1))).
  set (E2 := ext_list E1 (nxt cs1) vals).
  assert (Hag2 : env_agree (nxt cs1) E1 E2) by apply ext_list_agree.
  assert (Hnx : (nxt cs <= nxt cs1)%nat).
  { destruct (node_havoc_nxt cs _ cs1 Hh) as [-> _]. lia. }
  exists E2. split; [|split; [|rewrite <- Hpc1; reflexivity]].
  { split; (eapply env_agree_trans; [|eapply env_agree_le; [exact Hag2 | lia]]); assumption. }
  pose proof (cs_ok_agree E1 E2 cs1 R FULL model Hag2 Hf1 HC1) as HC2.
  replace (with_ss cs1 (mk_ss (pc cs1) (s_regs (a_ss cs1)) k' (nxt cs1 + c))) with (set_kn (bump cs1 c) k') by reflexivity.
  apply cs_ok_set_kn.
  - destruct HC2; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset];
      try assumption; reflexivity.
  - replace k' with (fst (kn_bigsubst K (kn cs1) (nxt cs1))) by (rewrite Hs; reflexivity).
    unfold Mr. change (hid E2 (bump cs1 c) model) with (hid E2 cs1 model).
    apply kn_bigsubst_sound; [exact (co_know _ _ _ _ _ HC2) | rewrite kn_vars_lt_eq; rewrite <- kn_vars_lt_eq; exact Fkn |].
    intros i Hi. unfold E2. rewrite ext_list_at by (unfold vals; rewrite length_map; exact Hi).
    unfold vals. change (Z_to_bv 64 0) with (edenot E1 (ELit 0)). rewrite map_nth.
    eapply (edenot_agree' (nxt cs1)); [apply ext_list_agree|].
    (* [comment removed for export] *)
    clear - Fkn Hi. revert i Hi. generalize (kn cs1) Fkn. intros k Hk.
    induction k as [|x r IH]; intros i Hi; [cbn in Hi; lia|].
    cbn [AP.kn_vars_lt] in Hk. apply andb_prop in Hk as [Hx Hr]. cbn [kn_bigexprs] in Hi |- *.
    destruct x as [a w v| | | | | | | | |]; try (apply IH; assumption).
    destruct (bigb K v); [|apply IH; assumption].
    destruct i as [|i]; cbn [nth]; [cbn [AP.kentry_vars_lt] in Hx; apply andb_prop in Hx as [_ Hx]; exact Hx | apply IH; [exact Hr | cbn [length] in Hi; lia]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition upd (E : env) (J : nat) (w : word) : env := Env (fun n => if Nat.eqb n J then w else ev E n) (eb E).

Lemma esubst_denot : forall E J e x, edenot E (esubst J e x) = edenot (upd E J (edenot E e)) x.
Proof.
  intros E J e x. induction x as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n];
    cbn [esubst edenot]; try reflexivity.
  - cbn [upd ev]. destruct (Nat.eqb n J); reflexivity.
  - rewrite mkAlu_denot, IHa, IHb. reflexivity.
  - rewrite mkAluw_denot, IHa, IHb. reflexivity.
  - rewrite mkMd_denot, IHa, IHb. reflexivity.
  - rewrite mkMdw_denot, IHa, IHb. reflexivity.
  - rewrite IHa. reflexivity.
Qed.

Lemma upd_agree : forall E J w, env_agree J E (upd E J w).
Proof. intros E J w. split; [|reflexivity]. intros n Hn. cbn [upd ev]. destruct (Nat.eqb_spec n J); [lia|reflexivity]. Qed.
Lemma upd_at : forall E J w, ev (upd E J w) J = w.
Proof. intros. cbn [upd ev]. rewrite Nat.eqb_refl. reflexivity. Qed.
Lemma upd_same : forall E J, upd E J (ev E J) = E.
Proof. intros [f g] J. unfold upd. cbn [ev eb]. f_equal. apply functional_extensionality. intros n. destruct (Nat.eqb_spec n J); [subst; reflexivity|reflexivity]. Qed.
Lemma upd_upd : forall E J w w', upd (upd E J w) J w' = upd E J w'.
Proof. intros [f g] J w w'. unfold upd. cbn [ev eb]. f_equal. apply functional_extensionality. intros n. destruct (Nat.eqb n J); reflexivity. Qed.

Lemma estart_asubst : forall E J e a, estart E (asubst J e a) = estart (upd E J (edenot E e)) a.
Proof. intros E J e [b o]. unfold asubst, estart. cbn [a_base a_off]. rewrite esubst_denot. reflexivity. Qed.
Lemma adenot_asubst : forall E J e a, adenot E (asubst J e a) = adenot (upd E J (edenot E e)) a.
Proof. intros E J e [b o]. unfold asubst, adenot. cbn [a_base a_off]. rewrite esubst_denot. reflexivity. Qed.

Lemma kentry_ok_ksubst : forall E J e M K,
  kentry_ok SEGS E M (ksubst J e K) <-> kentry_ok SEGS (upd E J (edenot E e)) M K.
Proof.
  intros E J e M K. set (E' := upd E J (edenot E e)).
  destruct K as [a w v|a n|a n k|lo hi|x m|x lo hi|a n|a1 n1 a2 n2|a n c|a n]; cbn [ksubst kentry_ok];
    unfold flat, elenZ; rewrite ?estart_asubst, ?adenot_asubst, ?esubst_denot; fold E'; tauto.
Qed.

Lemma know_ok_ksubst : forall E J e M k,
  know_ok SEGS E M (map (ksubst J e) k) <-> know_ok SEGS (upd E J (edenot E e)) M k.
Proof.
  intros E J e M k. unfold know_ok. induction k as [|K k IH]; [split; intros; constructor|].
  cbn [map]. split; intros H; inversion H; subst; constructor; try (apply IH; assumption);
    apply (kentry_ok_ksubst E J e M K); assumption.
Qed.

(* [comment removed for export] *)
Lemma inst_allowA : forall E J e inv, allowA E (inst inv J e) = allowA (upd E J (edenot E e)) inv.
Proof.
  intros E J e inv. unfold allowA, inst. cbn [a_vis a_ghost]. rewrite <- map_app, flat_map_concat_map, flat_map_concat_map, map_map.
  f_equal. apply map_ext. intros [b n]. unfold allow1, psubst, sh_lo, sh_hi, uE. cbn [fst snd]. rewrite !esubst_denot. reflexivity.
Qed.

Lemma existsb_map' : forall {X Y} (f : Y -> bool) (g : X -> Y) l, existsb f (map g l) = existsb (fun x => f (g x)) l.
Proof. intros X Y f g l. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma inst_in_allow : forall E J e inv, in_allow E (inst inv J e) = in_allow (upd E J (edenot E e)) inv.
Proof.
  intros E J e inv. apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh, inst. cbn [a_vis].
  rewrite !existsb_map'. f_equal; f_equal; apply functional_extensionality; intros [b n];
    unfold psubst, sh_lo, sh_hi, uE; cbn [fst snd]; rewrite !esubst_denot; reflexivity.
Qed.

Lemma inst_in_ghost : forall E J e inv, in_ghost E (inst inv J e) = in_ghost (upd E J (edenot E e)) inv.
Proof.
  intros E J e inv. apply functional_extensionality. intros z. unfold in_ghost, inst. cbn [a_ghost].
  induction (a_ghost inv) as [|[b n] l IH]; [reflexivity|]. cbn [map existsb fst snd psubst].
  unfold uE in *. cbn [fst snd]. rewrite !esubst_denot, IH. reflexivity.
Qed.

Lemma inst_hid : forall E J e inv model, (nx0 <= J)%nat ->
  hid E (inst inv J e) model = hid (upd E J (edenot E e)) inv model.
Proof.
  intros E J e inv model HJ. apply functional_extensionality. intros a. unfold hid, vis.
  rewrite inst_in_allow. rewrite (argH_agree E (upd E J (edenot E e)) a); [|eapply env_agree_le; [apply upd_agree | exact HJ]].
  unfold inst. cbn [a_maps]. reflexivity.
Qed.

Lemma inst_maps : forall E J e inv, map (amap_den E) (a_maps (inst inv J e)) = map (amap_den (upd E J (edenot E e))) (a_maps inv).
Proof.
  intros. unfold inst. cbn [a_maps]. rewrite map_map. apply map_ext. intros m. unfold amap_den, msubst. cbn [am_base am_len].
  rewrite !esubst_denot. reflexivity.
Qed.

Lemma maps_match_msubst : forall E J e ms l,
  maps_match E (map (msubst J e) ms) l <-> maps_match (upd E J (edenot E e)) ms l.
Proof.
  intros E J e ms. induction ms as [|m ms IH]; intros l; cbn [maps_match map]; [tauto|].
  unfold is_fog, msubst, uE, amap_den. cbn [am_kind am_base am_len]. rewrite !esubst_denot.
  destruct (is_tok_kind (am_kind m)).
  - split; (intros [HM|(iv & l' & -> & Hsz & HM)]; [left; apply IH; exact HM | right; exists iv, l'; split; [reflexivity|]; split; [exact Hsz | apply IH; exact HM]]).
  - split; (intros (l' & -> & HM); exists l'; split; [reflexivity | apply IH; exact HM]).
Qed.
(* [comment removed for export] *)
Lemma holes_msubst : forall E J e y l ms,
  Forall (hole_ok E y l) (map (msubst J e) ms) <-> Forall (hole_ok (upd E J (edenot E e)) y l) ms.
Proof.
  intros E J e y l ms. induction ms as [|m ms IH]; cbn [map].
  - split; intros; constructor.
  - rewrite !Forall_cons_iff, IH.
    assert (X : hole_ok E y l (msubst J e m) <-> hole_ok (upd E J (edenot E e)) y l m).
    { unfold hole_ok, is_hole, msubst, uE. cbn [am_kind am_base am_len]. rewrite !esubst_denot. tauto. }
    rewrite X. tauto.
Qed.
Lemma inst_maps_match : forall E J e inv l,
  maps_match E (a_maps (inst inv J e)) l <-> maps_match (upd E J (edenot E e)) (a_maps inv) l.
Proof. intros. unfold inst. cbn [a_maps]. apply maps_match_msubst. Qed.

Lemma regs_ok_inst : forall E J e sr R,
  regs_ok E (map (esubst J e) sr) R <-> regs_ok (upd E J (edenot E e)) sr R.
Proof.
  intros E J e sr R. unfold regs_ok, sr_get.
  assert (G : forall r, edenot E (if bv_eqb r 0 then ELit 0 else nth (ridx r) (map (esubst J e) sr) (ELit 0))
                     = edenot (upd E J (edenot E e)) (if bv_eqb r 0 then ELit 0 else nth (ridx r) sr (ELit 0))).
  { intros r. destruct (bv_eqb r 0); [reflexivity|].
    replace (ELit 0) with (esubst J e (ELit 0)) at 1 by reflexivity. rewrite map_nth. apply esubst_denot. }
  split; intros H r; [rewrite <- G | rewrite G]; apply H.
Qed.

Lemma fds_ok_inst : forall E J e f model, fds_ok E (fsubst J e f) model <-> fds_ok (upd E J (edenot E e)) f model.
Proof.
  intros E J e f model. destruct f as [|k l o|]; cbn [fsubst fds_ok]; try tauto.
  unfold uE. rewrite !esubst_denot. cbn [eb upd]. tauto.
Qed.

Lemma cs_ok_inst : forall E J e inv R FULL model, (nx0 <= J)%nat -> s_log (a_ss inv) = [] ->
  cs_ok E (inst inv J e) R FULL model <-> cs_ok (upd E J (edenot E e)) inv R FULL model.
Proof.
  intros E J e inv R FULL model HJ Hlog.
  pose proof (inst_hid E J e inv model HJ) as HH. pose proof (inst_allowA E J e inv) as HA. pose proof (inst_maps E J e inv) as HM.
  pose proof (inst_in_ghost E J e inv) as HG.
  assert (AG : env_agree nx0 E (upd E J (edenot E e))) by (eapply env_agree_le; [apply upd_agree | exact HJ]).
  split; intros HC; destruct HC; constructor;
    cbn [inst a_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset mk_ss] in *;
    rewrite <- ?HA, <- ?HM; try assumption.
  - apply regs_ok_inst. assumption.
  - unfold Mr. rewrite <- HH. apply know_ok_ksubst. exact co_know0.
  - apply fds_ok_inst. assumption.
  - apply (proj1 (maps_match_msubst E J e _ _)). assumption.
  - apply (proj1 (holes_msubst E J e _ _ _)). assumption.
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk.
    pose proof (proj1 (Forall_forall _ _) co_none0 (msubst J e m) ltac:(apply in_map; exact Hin) Hk) as X.
    unfold amap_den, msubst in X |- *. cbn [am_base am_len am_kind] in X. rewrite !esubst_denot in X. exact X.
  - apply Forall_forall. intros m Hin Hk a Ha.
    pose proof (proj1 (Forall_forall _ _) co_kinds0 (msubst J e m) ltac:(apply in_map; exact Hin) Hk a) as X.
    unfold msubst in X. cbn [am_base am_len] in X. rewrite !esubst_denot in X. exact (X Ha).
  - (* [comment removed for export] *) rewrite (e_sp0_agree _ _ _ AG (le_n _)). assumption.
  - rewrite <- esubst_denot. assumption.
  - intros a. unfold Mr in *. rewrite <- HH. first [rewrite HG | rewrite <- HG]. exact (co_zero0 a).
  - eapply SINV_agree; [exact AG | assumption].
  - apply regs_ok_inst. assumption.
  - reflexivity.
  - unfold Mr in *. rewrite HH. apply know_ok_ksubst. assumption.
  - apply fds_ok_inst. assumption.
  - apply (proj2 (maps_match_msubst E J e _ _)). assumption.
  - apply (proj2 (holes_msubst E J e _ _ _)). assumption.
  - apply Forall_forall. intros m' Hin Hk. apply in_map_iff in Hin as [m [<- Hin]].
    pose proof (proj1 (Forall_forall _ _) co_none0 m Hin Hk) as X.
    unfold amap_den, msubst. cbn [am_base am_len am_kind]. rewrite !esubst_denot. exact X.
  - apply Forall_forall. intros m' Hin Hk a Ha. apply in_map_iff in Hin as [m [<- Hin]].
    unfold msubst in Ha, Hk. cbn [am_base am_len am_kind] in Ha, Hk. rewrite !esubst_denot in Ha.
    exact (proj1 (Forall_forall _ _) co_kinds0 m Hin Hk a Ha).
  - (* [comment removed for export] *) rewrite <- (e_sp0_agree _ _ _ AG (le_n _)). assumption.
  - rewrite esubst_denot. assumption.
  - rewrite HA. assumption.
  - rewrite HA. assumption.
  - intros a. unfold Mr in *. rewrite HH. first [rewrite <- HG | rewrite HG]. exact (co_zero0 a).
  - eapply SINV_agree; [|eassumption]. destruct AG as [AG1 AG2]. split; [intros n Hn; symmetry; apply AG1; exact Hn | symmetry; exact AG2].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma kentry_eqb_h_sound : forall E M k X K,
  know_ok SEGS E M k -> kentry_ok SEGS E M X -> kentry_eqb_h X K = true -> kflat_h k K = true -> kentry_ok SEGS E M K.
Proof.
  intros E M k X K HK HX Heq Hfl. unfold kentry_eqb_h in Heq. apply orb_prop in Heq as [Heq|Heq].
  { apply kentry_eqb_eq in Heq. subst. exact HX. }
  assert (SAD : forall b o b' o' n ne, saddr_eqb_h (SA b o) (SA b' o') = true -> flat E (SA b o) n ->
            flat_x k b' o' ne = true -> estart E (SA b' o') = estart E (SA b o)).
  { intros b o b' o' n ne Hs Hf Hf'. unfold saddr_eqb_h in Hs. cbn [a_base a_off] in *.
    apply orb_prop in Hs as [Hs|Hs]; [apply saddr_eqb_eq in Hs; injection Hs as -> ->; reflexivity|].
    apply expr_eqb_eq in Hs. apply (f_equal (fun x => bv_unsigned (edenot E x))) in Hs.
    unfold eaddz in Hs. rewrite !mkAlu_denot, !u_add64 in Hs. cbn [edenot] in Hs. rewrite !u_lit64 in Hs.
    pose proof (flat_x_sound E M k b' o' ne HK Hf') as (F1 & F2 & F3). pose proof (u64_range (edenot E ne)).
    unfold flat, estart in *; cbn [a_base a_off] in *.
    pose proof (u64_range (edenot E b)). pose proof (u64_range (edenot E b')). unfold two64 in Hs.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (E1 : (bv_unsigned (edenot E b) + o mod 2 ^ 64) mod 2 ^ 64 = bv_unsigned (edenot E b) + o) by (rewrite Zplus_mod_idemp_r; apply Z.mod_small; lia).
    assert (E2 : (bv_unsigned (edenot E b') + o' mod 2 ^ 64) mod 2 ^ 64 = bv_unsigned (edenot E b') + o') by (rewrite Zplus_mod_idemp_r; apply Z.mod_small; lia).
    lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  assert (AD : forall a a', estart E a' = estart E a -> adenot E a' = adenot E a).
  { intros [b o] [b' o'] He. unfold adenot, estart, v_addi in *. cbn [a_base a_off] in *. apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite He. reflexivity. }
  destruct X as [[b o] w v|[b o] n|[b o] n kk| | | |[b o] n| |[b o] n c|[b o] n];
    destruct K as [[b' o'] w' v'|[b' o'] n'|[b' o'] n' kk'| | | |[b' o'] n'| |[b' o'] n' c'|[b' o'] n']; try discriminate;
    repeat match type of Heq with (_ && _)%bool = true => apply andb_prop in Heq as [Heq ?X] end;
    cbn [kentry_ok kflat_h] in *.
  - apply Nat.eqb_eq in X0. apply expr_eqb_eq in X. subst w' v'. destruct HX as (H1 & H2 & H3).
    pose proof (SAD b o b' o' _ _ Heq H2 Hfl) as ES.
    split; [exact H1|]. split; [unfold flat in *; rewrite ES; exact H2|]. rewrite (AD _ _ ES). exact H3.
  - apply expr_eqb_eq in X. subst n'. destruct HX as [H1 H2].
    pose proof (SAD b o b' o' _ _ Heq H1 Hfl) as ES. split; [unfold flat in *; rewrite ES; exact H1|]. rewrite ES. exact H2.
  - apply Nat.eqb_eq in X. apply expr_eqb_eq in X0. subst n' kk'. destruct HX as (H1 & H2 & H3).
    pose proof (SAD b o b' o' _ _ Heq H1 Hfl) as ES. split; [unfold flat in *; rewrite ES; exact H1|]. rewrite ES. split; [exact H2 | exact H3].
  - apply expr_eqb_eq in X. subst n'. destruct HX as [H1 H2].
    pose proof (SAD b o b' o' _ _ Heq H1 Hfl) as ES. split; [unfold flat in *; rewrite ES; exact H1|]. rewrite ES. exact H2.
  - apply Z.eqb_eq in X. apply expr_eqb_eq in X0. subst n' c'. destruct HX as [H1 H2].
    pose proof (SAD b o b' o' _ _ Heq H1 Hfl) as ES. split; [unfold flat in *; rewrite ES; exact H1|]. rewrite ES. exact H2.
  - apply expr_eqb_eq in X. subst n'. destruct HX as [H1 H2].
    pose proof (SAD b o b' o' _ _ Heq H1 Hfl) as ES. split; [unfold flat in *; rewrite ES; exact H1|]. rewrite ES. exact H2.
Qed.

(* [comment removed for export] *)
Lemma seg_rom_off_hull : forall a : word, in_hull A (bv_unsigned a) = false -> seg_rom SEGS a = None.
Proof.
  intros a Ha. unfold seg_rom.
  rewrite (memory_read1_hidden SEGS (fun x => negb (in_hull A (bv_unsigned x)))); [reflexivity| |].
  - intros x Hx. apply SEGS_in_hull. apply negb_true_iff in Hx. exact Hx.
  - rewrite Ha. reflexivity.
Qed.

Lemma rdn_bytes_some : forall M (a : word) w bs,
  rdn SEGS M a w = Some bs ->
  forall x : word, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat w)%Z ->
  in_hull A (bv_unsigned x) = false -> M x <> None.
Proof.
  intros M a w. revert a. induction w as [|w IH]; intros a bs Hr x Hx Hh; [lia|].
  cbn [rdn] in Hr.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  - assert (x = a) by (apply bv_eq; exact Heq). subst x.
    destruct (M a) eqn:HMa; [congruence|]. rewrite (seg_rom_off_hull a Hh) in Hr. discriminate.
  - destruct (match M a with Some b => Some b | None => seg_rom SEGS a end) as [b|]; [|discriminate].
    destruct (rdn SEGS M (a + 1)%bv w) as [rest|] eqn:Hr2; [|discriminate].
    pose proof (u64_range x).
    assert (Hu1 : bv_unsigned (a + 1)%bv = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
    eapply (IH (a + 1)%bv rest Hr2); [rewrite Hu1; lia | exact Hh].
Qed.

Lemma cover1_sound : forall E M k b i e,
  know_ok SEGS E M k -> cover1 k b i = Some e ->
  (i < e)%Z /\ forall j, (i <= j < e)%Z -> in_hull A (uE E b + j) = false ->
     (0 <= uE E b + j < 2 ^ 64)%Z /\ M (Z_to_bv 64 (uE E b + j)) <> None.
Proof.
  intros E M k b i e HK. induction k as [|K r IH]; intros H; [discriminate|].
  inversion HK as [|K' r' HKK Hr]; subst. cbn [cover1] in H.
  match type of H with (match ?h with Some e0 => Some e0 | None => _ end = _) => destruct h as [e1|] eqn:Hhit end;
    [injection H as <- | exact (IH Hr H)].
  clear IH Hr HK.
  assert (ZF : forall kb kk l (P : option byte -> Prop),
            (flat E (SA kb kk) (elenZ E (ELit l)) /\ forall i0, (0 <= i0 < elenZ E (ELit l))%Z -> P (M (Z_to_bv 64 (estart E (SA kb kk) + i0)))) ->
            (forall x, P x -> x <> None) ->
            (if (expr_eqb b kb && Z.leb 0 l && Z.ltb l two64 && Z.leb kk i && Z.ltb i (kk + l))%bool then Some (kk + l)%Z else None) = Some e1 ->
            (i < e1)%Z /\ forall j, (i <= j < e1)%Z -> in_hull A (uE E b + j) = false ->
               (0 <= uE E b + j < 2 ^ 64)%Z /\ M (Z_to_bv 64 (uE E b + j)) <> None).
  { intros kb kk l P [Hfl Hall] HP Hc.
    destruct (expr_eqb b kb && Z.leb 0 l && Z.ltb l two64 && Z.leb kk i && Z.ltb i (kk + l))%bool eqn:Hcnd; [|discriminate].
    injection Hc as <-.
    repeat match type of Hcnd with (_ && _)%bool = true => apply andb_prop in Hcnd as [Hcnd ?X] end.
    apply expr_eqb_eq in Hcnd. subst kb. apply Z.leb_le in X2. apply Z.ltb_lt in X1. apply Z.leb_le in X0. apply Z.ltb_lt in X.
    unfold two64 in X1. rewrite (elenZ_lit E l) in Hfl, Hall by lia.
    destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in *; cbn [a_base a_off] in *. unfold uE.
    split; [lia|]. intros j Hj Hh. split; [lia|].
    replace (bv_unsigned (edenot E b) + j)%Z with (bv_unsigned (edenot E b) + kk + (j - kk))%Z by lia.
    apply HP. apply Hall. lia. }
  destruct K as [[kb kk] w v|[kb kk] [l| | | | | | |]|[kb kk] [l| | | | | | |] bk| | | | | |[kb kk] [l| | | | | | |] fc|[kb kk] [l| | | | | | |]];
    try discriminate.
  - (* [comment removed for export] *)
    destruct (expr_eqb b kb && Z.leb kk i && Z.ltb i (kk + Z.of_nat w))%bool eqn:Hcnd; [|discriminate]. injection Hhit as <-.
    apply andb_prop in Hcnd as [Hcnd X]. apply andb_prop in Hcnd as [Hb X0].
    apply expr_eqb_eq in Hb. subst kb. apply Z.leb_le in X0. apply Z.ltb_lt in X.
    cbn [kentry_ok] in HKK. destruct HKK as (Hw & Hfl & Hrd).
    pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in *; cbn [a_base a_off] in *. unfold uE.
    split; [lia|]. intros j Hj Hh. split; [lia|].
    apply (rdn_bytes_some M _ w _ Hrd); rewrite ?Hu, ?u64_lit by lia; [lia | exact Hh].
  - (* [comment removed for export] *) eapply (ZF kb kk l (fun x => x = Some (Z_to_bv 8 0))); [exact HKK | intros x ->; discriminate | exact Hhit].
  - (* [comment removed for export] *) cbn [kentry_ok] in HKK. destruct HKK as (Hfl & Hlen & Hall).
    eapply (ZF kb kk l (fun x => exists b0, x = Some b0)); [split; [exact Hfl | intros i0 Hi0; eexists; apply Hall; exact Hi0] | intros x [b0 ->]; discriminate | exact Hhit].
  - (* [comment removed for export] *) eapply (ZF kb kk l (fun x => x = Some (Z_to_bv 8 fc))); [exact HKK | intros x ->; discriminate | exact Hhit].
  - (* [comment removed for export] *) eapply (ZF kb kk l (fun x => x <> None)); [exact HKK | intros x Hx; exact Hx | exact Hhit].
Qed.

Lemma cover_x_sound : forall fuel E M k b i stop,
  know_ok SEGS E M k -> cover_x fuel k b i stop = true ->
  forall j, (i <= j < stop)%Z -> in_hull A (uE E b + j) = false ->
    (0 <= uE E b + j < 2 ^ 64)%Z /\ M (Z_to_bv 64 (uE E b + j)) <> None.
Proof.
  induction fuel as [|f IH]; intros E M k b i stop HK H j Hj Hh; [discriminate|].
  cbn [cover_x] in H. destruct (Z.leb_spec stop i); [lia|].
  destruct (cover1 k b i) as [e|] eqn:Hc; [|discriminate].
  destruct (Z.ltb_spec i e); [|discriminate].
  destruct (cover1_sound E M k b i e HK Hc) as [_ Hcov].
  destruct (Z.lt_ge_cases j e).
  - apply Hcov; [lia | exact Hh].
  - eapply IH; [exact HK | exact H | lia | exact Hh].
Qed.

Lemma kunk_covered_sound : forall E M k K, know_ok SEGS E M k -> kunk_covered A k K = true -> kentry_ok SEGS E M K.
Proof.
  intros E M k K HK H. unfold kunk_covered in H.
  destruct K as [| | | | | | | | |[b o] [n| | | | | | |]]; try discriminate.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Z.ltb_lt in H. apply Z.leb_le in X3. apply Z.leb_le in X2.
  pose proof (flat_x_sound E M k b o (ELit n) HK X1) as (F1 & F2 & F3).
  pose proof (ranges_apart_x_sound SEGS E M k _ _ _ _ _ _ HK X0) as AP0.
  cbn [edenot] in F2, F3. rewrite u64_lit in F2, F3 by lia.
  pose proof HULL_ok as HU; unfold hull_ok, KHI in HU.
  rewrite (elenZ_lit E n) in AP0 by lia. rewrite (elenZ_lit E (img_hi A - img_lo A)) in AP0 by lia.
  unfold estart in AP0; cbn [a_base a_off edenot] in AP0. rewrite u_lit0 in AP0.
  cbn [kentry_ok]. rewrite elenZ_lit by lia. split.
  - unfold flat, estart in *; cbn [a_base a_off] in *. lia.
  - intros i Hi. unfold estart in *; cbn [a_base a_off] in *.
    replace (bv_unsigned (edenot E b) + o + i)%Z with (uE E b + (o + i))%Z by (unfold uE; lia).
    apply (cover_x_sound _ E M k b o (o + n) HK X); [lia|].
    unfold in_hull, uE. apply andb_false_iff.
    destruct AP0 as [AP0|AP0]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.

Lemma kn_incl_h_sound : forall E M k tk, know_ok SEGS E M k -> kn_incl_h A k tk = true -> know_ok SEGS E M tk.
Proof.
  intros E M k tk HK H. unfold kn_incl_h in H. apply Forall_forall. intros K Hin.
  pose proof (proj1 (forallb_forall _ _) H K Hin) as HK1. unfold kn_incl1_h in HK1.
  destruct (existsb (fun X => kentry_eqb X K) k) eqn:Hex1.
  { apply existsb_exists in Hex1 as [X [HinX Heq]]. apply kentry_eqb_eq in Heq. subst. exact (proj1 (Forall_forall _ _) HK K HinX). }
  (* [comment removed for export] *)
  assert (IMG : kimg_sub_covered k K = true -> kentry_ok SEGS E M K).
  { intros Hc. unfold kimg_sub_covered in Hc. destruct K as [| | |lo hi| | | | | |]; try discriminate.
    apply existsb_exists in Hc as [X [HinX HX]]. destruct X as [| | |lo' hi'| | | | | |]; try discriminate.
    apply andb_prop in HX as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (proj1 (Forall_forall _ _) HK _ HinX) as HKX. cbn [kentry_ok] in HKX |- *.
    destruct HKX as (Ha & Hb & Hc). split; [lia|]. split; [lia|]. intros i Hi. apply Hc. lia. }
  destruct (kflat_h k K) eqn:Hfl.
  - destruct (existsb (fun X => kentry_eqb_h X K) k) eqn:Hex.
    + apply existsb_exists in Hex as [X [HinX Heq]].
      eapply kentry_eqb_h_sound; [exact HK | exact (proj1 (Forall_forall _ _) HK X HinX) | exact Heq | exact Hfl].
    + destruct (kimg_sub_covered k K) eqn:Himg; [exact (IMG eq_refl)|]. eapply kunk_covered_sound; [exact HK | exact HK1].
  - destruct (kimg_sub_covered k K) eqn:Himg; [exact (IMG eq_refl)|]. eapply kunk_covered_sound; [exact HK | exact HK1].
Qed.

(* [comment removed for export] *)
Definition is_havoc (lo hi : nat) (t : expr) : option nat :=
  match t with EVar v => if (Nat.leb lo v && Nat.ltb v hi)%bool then Some v else None | _ => None end.

Fixpoint henv (lo hi : nat) (E : env) (rs ts : list expr) : env :=
  match rs, ts with
  | r :: rs', t :: ts' =>
      let E1 := henv lo hi E rs' ts' in
      match is_havoc lo hi t with Some v => upd E1 v (edenot E r) | None => E1 end
  | _, _ => E
  end.

Lemma is_havoc_range : forall lo hi t v, is_havoc lo hi t = Some v -> t = EVar v /\ (lo <= v < hi)%nat.
Proof.
  intros lo hi t v H. destruct t; try discriminate. cbn [is_havoc] in H.
  destruct (Nat.leb lo n && Nat.ltb n hi)%bool eqn:Hc; [|discriminate]. injection H as <-.
  apply andb_prop in Hc as [H1 H2]. apply Nat.leb_le in H1. apply Nat.ltb_lt in H2. split; [reflexivity | lia].
Qed.

Lemma henv_agree : forall lo hi E rs ts, env_agree lo E (henv lo hi E rs ts).
Proof.
  intros lo hi E rs. induction rs as [|r rs IH]; intros [|t ts]; cbn [henv]; try apply env_agree_refl.
  destruct (is_havoc lo hi t) as [v|] eqn:Hv; [|apply IH].
  apply is_havoc_range in Hv as [_ Hv]. eapply env_agree_trans; [apply IH|]. eapply env_agree_le; [apply upd_agree | lia].
Qed.

Lemma henv_high : forall lo hi E rs ts n, (hi <= n)%nat -> ev (henv lo hi E rs ts) n = ev E n.
Proof.
  intros lo hi E rs. induction rs as [|r rs IH]; intros [|t ts] n Hn; cbn [henv]; try reflexivity.
  destruct (is_havoc lo hi t) as [v|] eqn:Hv; [|apply IH; exact Hn].
  apply is_havoc_range in Hv as [_ Hv]. cbn [upd ev]. destruct (Nat.eqb_spec n v); [lia|]. apply IH. exact Hn.
Qed.

(* [comment removed for export] *)
Lemma regs_match_h_char : forall lo hi seen rs ts, regs_match_h lo hi seen rs ts = true ->
  length rs = length ts /\
  forall i, (i < length ts)%nat ->
    (exists v, is_havoc lo hi (nth i ts (ELit 0)) = Some v /\ ~ In v seen /\
               forall i', (i' < i)%nat -> is_havoc lo hi (nth i' ts (ELit 0)) <> Some v)
    \/ (is_havoc lo hi (nth i ts (ELit 0)) = None /\ nth i ts (ELit 0) = nth i rs (ELit 0) /\ AP.expr_vars_lt lo (nth i ts (ELit 0)) = true).
Proof.
  intros lo hi seen rs. revert seen. induction rs as [|r rs IH]; intros seen [|t ts] H; cbn [regs_match_h length] in H |- *; try discriminate.
  - split; [reflexivity | intros i Hi; lia].
  - assert (STEP : forall seen', regs_match_h lo hi seen' rs ts = true -> (forall v, In v seen -> In v seen') ->
              (forall v, is_havoc lo hi t = Some v -> In v seen') ->
              length rs = length ts /\ forall i, (Datatypes.S i < Datatypes.S (length ts))%nat ->
                (exists v, is_havoc lo hi (nth (Datatypes.S i) (t :: ts) (ELit 0)) = Some v /\ ~ In v seen /\
                   forall i', (i' < Datatypes.S i)%nat -> is_havoc lo hi (nth i' (t :: ts) (ELit 0)) <> Some v)
                \/ (is_havoc lo hi (nth (Datatypes.S i) (t :: ts) (ELit 0)) = None /\ nth (Datatypes.S i) (t :: ts) (ELit 0) = nth (Datatypes.S i) (r :: rs) (ELit 0)
                    /\ AP.expr_vars_lt lo (nth (Datatypes.S i) (t :: ts) (ELit 0)) = true)).
    { intros seen' Hm Hsub Ht. destruct (IH seen' ts Hm) as [Hlen Hc]. split; [exact Hlen|].
      intros i Hi. cbn [nth]. destruct (Hc i ltac:(lia)) as [[v (Hv & Hns & Hbefore)]|Hn]; [left|right; exact Hn].
      exists v. split; [exact Hv|]. split; [intros Hin; apply Hns; apply Hsub; exact Hin|].
      intros [|i'] Hi'; cbn [nth].
      - intros Heq. apply Hns. apply Ht. exact Heq.
      - apply Hbefore. lia. }
    destruct (is_havoc lo hi t) as [v|] eqn:Hv.
    + destruct t as [|w| | | | | |]; try discriminate. cbn [is_havoc] in Hv.
      destruct (Nat.leb lo w && Nat.ltb w hi)%bool eqn:Hr; [|discriminate]. injection Hv as Hwv. subst v.
      apply andb_prop in H as [Hnew Hm]. apply negb_true_iff in Hnew.
      assert (Hns : ~ In w seen).
      { intros Hin. enough (existsb (Nat.eqb w) seen = true) by congruence. apply existsb_exists. exists w. split; [exact Hin | apply Nat.eqb_refl]. }
      destruct (STEP (w :: seen) Hm ltac:(intros; right; assumption) ltac:(intros v' Hv'; injection Hv' as <-; left; reflexivity)) as [Hlen Hc].
      split; [rewrite Hlen; reflexivity|]. intros [|i] Hi; [|exact (Hc i Hi)].
      left. exists w. cbn [nth is_havoc]. rewrite Hr. split; [reflexivity|]. split; [exact Hns|]. intros i' Hi'. lia.
    + assert (Hm : (expr_eqb r t && AP.expr_vars_lt lo t && regs_match_h lo hi seen rs ts)%bool = true).
      { destruct t; try exact H. cbn [is_havoc] in Hv. destruct (Nat.leb lo n && Nat.ltb n hi)%bool; [discriminate | exact H]. }
      apply andb_prop in Hm as [Hm1 Hm]. apply andb_prop in Hm1 as [He Hvl]. apply expr_eqb_eq in He. subst t.
      destruct (STEP seen Hm ltac:(intros; assumption) ltac:(intros v' Hv'; discriminate Hv')) as [Hlen Hc].
      split; [rewrite Hlen; reflexivity|]. intros [|i] Hi; [|exact (Hc i Hi)].
      right. cbn [nth]. split; [exact Hv|]. split; [reflexivity | exact Hvl].
Qed.

Lemma henv_havoc : forall lo hi E rs ts i v,
  length rs = length ts -> (i < length ts)%nat ->
  is_havoc lo hi (nth i ts (ELit 0)) = Some v ->
  (forall i', (i' < i)%nat -> is_havoc lo hi (nth i' ts (ELit 0)) <> Some v) ->
  ev (henv lo hi E rs ts) v = edenot E (nth i rs (ELit 0)).
Proof.
  intros lo hi E rs. induction rs as [|r rs IH]; intros [|t ts] i v Hlen Hi Hv Hbefore; cbn [length] in *; try lia.
  cbn [henv]. destruct i as [|i]; cbn [nth] in *.
  - rewrite Hv. apply upd_at.
  - destruct (is_havoc lo hi t) as [v'|] eqn:Ht.
    + cbn [upd ev]. destruct (Nat.eqb_spec v v').
      * subst v'. exfalso. exact (Hbefore 0%nat ltac:(lia) Ht).
      * apply IH; [lia | lia | exact Hv |]. intros i' Hi'. exact (Hbefore (Datatypes.S i') ltac:(lia)).
    + apply IH; [lia | lia | exact Hv |]. intros i' Hi'. exact (Hbefore (Datatypes.S i') ltac:(lia)).
Qed.

Lemma regs_match_h_sound : forall lo hi E rs ts R,
  regs_match_h lo hi [] rs ts = true -> length ts = 32%nat -> regs_ok E rs R -> regs_ok (henv lo hi E rs ts) ts R.
Proof.
  intros lo hi E rs ts R H Hlen HR. destruct (regs_match_h_char lo hi [] rs ts H) as [Hl Hc].
  intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0; [exact (eq_trans (HR r) ltac:(unfold sr_get; rewrite Hr0; reflexivity))|].
  pose proof (ridx_range r) as Hlt. specialize (HR r). unfold sr_get in HR. rewrite Hr0 in HR. rewrite HR.
  destruct (Hc (ridx r) ltac:(lia)) as [[v (Hv & _ & Hbefore)]|(Hn & Heq & Hvl)].
  - destruct (is_havoc_range _ _ _ _ Hv) as [Et _]. rewrite Et. cbn [edenot]. symmetry. apply (henv_havoc lo hi E rs ts (ridx r) v Hl ltac:(lia) Hv Hbefore).
  - rewrite Heq in Hvl |- *. eapply (edenot_agree' lo); [apply henv_agree | exact Hvl].
Qed.

(* [comment removed for export] *)
Lemma cs_ok_reenv : forall b E E' cs sr' R FULL model,
  cs_ok E cs R FULL model -> env_agree b E E' -> (nx0 <= b)%nat ->
  AP.kn_vars_lt b (kn cs) = true -> maps_vars_lt b (a_maps cs) = true -> pairs_vars_lt b (a_vis cs ++ a_ghost cs) = true ->
  AP.expr_vars_lt b (a_brk cs) = true -> fd_vars_lt b (a_fd cs) = true ->
  regs_ok E' sr' R ->
  cs_ok E' (set_regs cs sr') R FULL model.
Proof.
  intros b E E' cs sr' R FULL model HC Hag Hb Hkn Hmaps Hallow Hbrk Hfd HR.
  pose proof (hid_agree b E E' cs model Hag Hb Hallow) as HH.
  rewrite <- (hid_ext E' cs (set_regs cs sr') model eq_refl) in HH.
  pose proof (allowA_agree b E E' cs Hag Hallow) as HA.
  assert (HA2 : allowA E' (set_regs cs sr') = allowA E' cs) by reflexivity. rewrite <- HA2 in HA. clear HA2.
  destruct HC; constructor; cbn [set_regs with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset] in *;
    rewrite ?HA; try assumption; try reflexivity.
  - unfold Mr in *. rewrite HH. eapply know_ok_agree'; eassumption.
  - eapply fds_ok_agree; eassumption.
  - eapply maps_match_agree; [exact Hag | exact Hmaps | assumption].
  - eapply holes_agree; [exact Hag | exact Hmaps | assumption].
  - apply Forall_forall. intros m Hin Hk.
    pose proof (proj1 (forallb_forall _ _) Hmaps m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
    unfold amap_den. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2).
    exact (proj1 (Forall_forall _ _) co_none0 m Hin Hk).
  - apply Forall_forall. intros m Hin Hk a Ha.
    pose proof (proj1 (forallb_forall _ _) Hmaps m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
    rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2) in Ha.
    exact (proj1 (Forall_forall _ _) co_kinds0 m Hin Hk a Ha).
  - (* [comment removed for export] *) rewrite (e_sp0_agree _ _ _ Hag Hb). assumption.
  - rewrite <- (edenot_agree' b E E' _ Hag Hbrk). assumption.
  - intros a. rewrite HH. change (in_ghost E' (set_regs cs sr')) with (in_ghost E' cs). rewrite (in_ghost_agree b E E' cs Hag Hallow). exact (co_zero0 a).
  - eapply SINV_agree; [eapply env_agree_le; [exact Hag | exact Hb] | assumption].
Qed.

Lemma entails_h_sound : forall lo hi E cs T R FULL model,
  cs_ok E cs R FULL model -> entails_h A lo hi cs T = true -> (nx0 <= lo)%nat -> length (s_regs (a_ss T)) = 32%nat ->
  exists E', env_agree lo E E' /\ (forall n, (hi <= n)%nat -> ev E' n = ev E n) /\ cs_ok E' T R FULL model /\ pc T = pc cs.
Proof.
  intros lo hi E cs T R FULL model HC H Hlo Hlen. unfold entails_h in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  rename H into Hpc. apply Z.eqb_eq in Hpc.
  match goal with Hl : match s_log (a_ss T) with _ => _ end = true |- _ => rename Hl into HL; destruct (s_log (a_ss T)) eqn:HL'; [clear HL; rename HL' into HL|discriminate] end.
  match goal with Hl : match s_resv (a_ss T) with _ => _ end = true |- _ => rename Hl into HRV; destruct (s_resv (a_ss T)) eqn:HRV'; [discriminate|clear HRV; rename HRV' into HRV] end.
  match goal with Hr : regs_match_h _ _ _ _ _ = true |- _ => rename Hr into Hregs end.
  match goal with Hm : list_eqb amap_eqb _ _ = true |- _ => apply (list_eqb_eq amap_eqb amap_eqb_eq) in Hm; rename Hm into Hmaps end.
  match goal with Ha : list_eqb pair_eqb (a_vis cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ha; rename Ha into Hallow end.
  match goal with Hg : list_eqb pair_eqb (a_ghost cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hg; rename Hg into Hghost end.
  match goal with Hb : expr_eqb (a_brk cs) _ = true |- _ => apply expr_eqb_eq in Hb; rename Hb into Hbrk end.
  match goal with Hf : afd_eqb _ _ = true |- _ => apply afd_eqb_eq in Hf; rename Hf into Hfd end.
  match goal with Ht : Bool.eqb _ _ = true |- _ => apply eqb_prop in Ht; rename Ht into Htid end.
  match goal with Hk : kn_incl_h _ _ (kn T) = true |- _ => rename Hk into Hkn end.
  repeat match goal with Hz : Z.leb _ _ = true |- _ => apply Z.leb_le in Hz end.
  set (E' := henv lo hi E (s_regs (a_ss cs)) (s_regs (a_ss T))).
  exists E'. split; [apply henv_agree|]. split; [intros; apply henv_high; assumption|]. split; [|symmetry; exact Hpc].
  (* [comment removed for export] *)
  set (Tc := set_regs T (s_regs (a_ss cs))).
  assert (Evis : a_vis Tc = a_vis cs) by (unfold Tc; cbn [set_regs with_ss a_vis]; symmetry; exact Hallow).
  assert (HA : allowA E Tc = allowA E cs) by (unfold allowA; unfold Tc; cbn [set_regs with_ss a_vis a_ghost]; rewrite Hallow, Hghost; reflexivity).
  assert (HH : hid E Tc model = hid E cs model) by (apply hid_ext; exact Evis).
  assert (HC1 : cs_ok E Tc R FULL model).
  { destruct HC; constructor; rewrite ?HA;
      try (unfold Tc; cbn [set_regs with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
           rewrite <- ?Hmaps, <- ?Hallow, <- ?Hghost, <- ?Hbrk, <- ?Hfd, <- ?Htid; first [assumption | reflexivity | lia]).
    - unfold Mr. rewrite HH. eapply kn_incl_h_sound; [exact co_know0 | exact Hkn].
    - unfold Tc. cbn [set_regs with_ss a_maps a_ylo]. rewrite <- Hmaps. eapply holes_mono; [exact co_holes0 | lia].
    - intros a. rewrite HH. replace (in_ghost E Tc) with (in_ghost E cs) by (unfold in_ghost, Tc; cbn [set_regs with_ss a_ghost]; rewrite Hghost; reflexivity).
      exact (co_zero0 a). }
  (* [comment removed for export] *)
  assert (ET : T = set_regs Tc (s_regs (a_ss T))).
  { subst Tc. clear - HL HRV. destruct T as [[p sr lg k nx rv] m t y e v g ab br f ti]. cbn in HL, HRV. subst lg rv. reflexivity. }
  rewrite ET at 1. eapply (cs_ok_reenv lo); try eassumption.
  - apply henv_agree.
  - unfold pairs_vars_lt, Tc. cbn [set_regs with_ss a_vis a_ghost]. rewrite forallb_app. apply andb_true_intro; split; assumption.
  - apply regs_match_h_sound; [exact Hregs | exact Hlen | exact (co_regs _ _ _ _ _ HC)].
Qed.

(* [comment removed for export] *)
Lemma diamond_join_sound : forall nx joinpc rs ca cb csj,
  node_diamond_join A nx0 nx joinpc rs ca cb = Some csj ->
  (forall E R FULL model, cs_ok E ca R FULL model ->
     exists E', (env_agree nx0 E E' /\ env_agree nx E E') /\ cs_ok E' csj R FULL model /\ pc csj = pc ca)
  /\ (forall E R FULL model, cs_ok E cb R FULL model ->
     exists E', (env_agree nx0 E E' /\ env_agree nx E E') /\ cs_ok E' csj R FULL model /\ pc csj = pc cb).
Proof.
  intros nx joinpc rs ca cb csj H. unfold node_diamond_join in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-.
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  match goal with Hl : Nat.eqb (length ?l) 32 = true |- _ => apply Nat.eqb_eq in Hl; rename Hl into Hlen end.
  match goal with Hl : Nat.leb nx0 ?v = true |- _ => apply Nat.leb_le in Hl; rename Hl into Hn0 end.
  split; intros E R FULL model HC.
  - match goal with Hea : entails_h A ?lo ?hi ca ?T = true |- _ =>
      destruct (entails_h_sound lo hi E ca T R FULL model HC Hea Hn0 Hlen) as (E' & Hag & _ & HC' & Hpc) end.
    exists E'. split; [split; eapply env_agree_le; [exact Hag | lia | exact Hag | lia] | split; [exact HC' | exact Hpc]].
  - match goal with Hea : entails_h A ?lo ?hi cb ?T = true |- _ =>
      destruct (entails_h_sound lo hi E cb T R FULL model HC Hea Hn0 Hlen) as (E' & Hag & _ & HC' & Hpc) end.
    exists E'. split; [split; eapply env_agree_le; [exact Hag | lia | exact Hag | lia] | split; [exact HC' | exact Hpc]].
Qed.

(* [comment removed for export] *)
Lemma diamond_join_sound2 : forall nx joinpc rs ca cb csj,
  node_diamond_join A nx0 nx joinpc rs ca cb = Some csj ->
  (forall E R FULL model, cs_ok E ca R FULL model ->
     exists E', (env_agree nx0 E E' /\ env_agree nx E E' /\ env_agree (nxt ca) E E') /\ cs_ok E' csj R FULL model /\ pc csj = pc ca)
  /\ (forall E R FULL model, cs_ok E cb R FULL model ->
     exists E', (env_agree nx0 E E' /\ env_agree nx E E' /\ env_agree (nxt cb) E E') /\ cs_ok E' csj R FULL model /\ pc csj = pc cb)
  /\ a_vis csj = a_vis ca /\ a_ghost csj = a_ghost ca /\ incl (kn csj) (kn ca) /\ incl (kn csj) (kn cb).
Proof.
  intros nx joinpc rs ca cb csj H. unfold node_diamond_join in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-.
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  match goal with Hl : Nat.eqb (length ?l) 32 = true |- _ => apply Nat.eqb_eq in Hl; rename Hl into Hlen end.
  match goal with Hl : Nat.leb nx0 ?v = true |- _ => apply Nat.leb_le in Hl; rename Hl into Hn0 end.
  split; [|split; [|split; [reflexivity|]; split; [reflexivity|]; split;
    [ unfold kn; cbn [a_ss s_know]; apply incl_filter
    | unfold kn; cbn [a_ss s_know]; intros K HK; apply filter_In in HK as [_ HX]; apply existsb_exists in HX as (Kb & HX1 & HX2);
      apply kentry_eqb_eq in HX2; subst; exact HX1 ]]]; intros E R FULL model HC.
  - match goal with Hea : entails_h A ?lo ?hi ca ?T = true |- _ =>
      destruct (entails_h_sound lo hi E ca T R FULL model HC Hea Hn0 Hlen) as (E' & Hag & _ & HC' & Hpc) end.
    exists E'. split; [split; [|split]; eapply env_agree_le; [exact Hag | lia | exact Hag | lia | exact Hag | lia] | split; [exact HC' | exact Hpc]].
  - match goal with Hea : entails_h A ?lo ?hi cb ?T = true |- _ =>
      destruct (entails_h_sound lo hi E cb T R FULL model HC Hea Hn0 Hlen) as (E' & Hag & _ & HC' & Hpc) end.
    exists E'. split; [split; [|split]; eapply env_agree_le; [exact Hag | lia | exact Hag | lia | exact Hag | lia] | split; [exact HC' | exact Hpc]].
Qed.

Lemma loop_ok_facts : forall cs J N inv nhi,
  loop_ok nx0 cs J N inv = Some nhi ->
  fresh_ok nx0 cs = true /\ (nxt cs <= J)%nat /\ (J < nxt inv)%nat /\ s_log (a_ss inv) = [] /\
  length (s_regs (a_ss inv)) = 32%nat /\ AP.expr_vars_lt (nxt cs) N = true /\
  xhi (kn cs) N = Some nhi /\ nhi < two64.
Proof.
  intros cs J N inv nhi H. unfold loop_ok in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  destruct (xhi (kn cs) N) as [h|] eqn:Hx; [|discriminate]. destruct (Z.ltb h two64) eqn:Hlt; [|discriminate]. injection H as <-.
  apply Z.ltb_lt in Hlt.
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  apply Nat.leb_le in X12. apply Nat.ltb_lt in X11.
  destruct (s_log (a_ss inv)); [|discriminate]. apply Nat.eqb_eq in X7.
  repeat split; try assumption; reflexivity.
Qed.

Lemma pc_inst : forall inv J e, pc (inst inv J e) = pc inv.
Proof. reflexivity. Qed.
Lemma nxt_inst : forall inv J e, nxt (inst inv J e) = nxt inv.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma insts_allowA : forall E sg inv, allowA E (insts sg inv) = allowA (updl E sg) inv.
Proof.
  intros E sg inv. unfold allowA, insts. cbn [a_vis a_ghost]. rewrite <- map_app, flat_map_concat_map, flat_map_concat_map, map_map.
  f_equal. apply map_ext. intros [b n]. unfold allow1, psubsts, sh_lo, sh_hi, uE. cbn [fst snd]. rewrite !esubsts_denot. reflexivity.
Qed.

Lemma insts_in_allow : forall E sg inv, in_allow E (insts sg inv) = in_allow (updl E sg) inv.
Proof.
  intros E sg inv. apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh, insts. cbn [a_vis].
  rewrite !existsb_map'. f_equal; f_equal; apply functional_extensionality; intros [b n];
    unfold psubsts, sh_lo, sh_hi, uE; cbn [fst snd]; rewrite !esubsts_denot; reflexivity.
Qed.

Lemma insts_in_ghost : forall E sg inv, in_ghost E (insts sg inv) = in_ghost (updl E sg) inv.
Proof.
  intros E sg inv. apply functional_extensionality. intros z. unfold in_ghost, insts. cbn [a_ghost].
  induction (a_ghost inv) as [|[b n] l IH]; [reflexivity|]. cbn [map existsb fst snd psubsts].
  unfold uE in *. cbn [fst snd]. rewrite !esubsts_denot, IH. reflexivity.
Qed.

Lemma insts_hid : forall E sg inv model, sg_dom_ge nx0 sg = true ->
  hid E (insts sg inv) model = hid (updl E sg) inv model.
Proof.
  intros E sg inv model Hsg. apply functional_extensionality. intros a. unfold hid, vis.
  rewrite insts_in_allow. rewrite (argH_agree E (updl E sg) a); [|apply updl_agree; exact Hsg].
  unfold insts. cbn [a_maps]. reflexivity.
Qed.

Lemma insts_maps : forall E sg inv, map (amap_den E) (a_maps (insts sg inv)) = map (amap_den (updl E sg)) (a_maps inv).
Proof.
  intros. unfold insts. cbn [a_maps]. rewrite map_map. apply map_ext. intros m. unfold amap_den, msubsts. cbn [am_base am_len].
  rewrite !esubsts_denot. reflexivity.
Qed.

Lemma maps_match_msubsts : forall E sg ms l,
  maps_match E (map (msubsts sg) ms) l <-> maps_match (updl E sg) ms l.
Proof.
  intros E sg ms. induction ms as [|m ms IH]; intros l; cbn [maps_match map]; [tauto|].
  unfold is_fog, msubsts, uE, amap_den. cbn [am_kind am_base am_len]. rewrite !esubsts_denot.
  destruct (is_tok_kind (am_kind m)).
  - split; (intros [HM|(iv & l' & -> & Hsz & HM)]; [left; apply IH; exact HM | right; exists iv, l'; split; [reflexivity|]; split; [exact Hsz | apply IH; exact HM]]).
  - split; (intros (l' & -> & HM); exists l'; split; [reflexivity | apply IH; exact HM]).
Qed.

Lemma holes_msubsts : forall E sg y l ms,
  Forall (hole_ok E y l) (map (msubsts sg) ms) <-> Forall (hole_ok (updl E sg) y l) ms.
Proof.
  intros E sg y l ms. induction ms as [|m ms IH]; cbn [map].
  - split; intros; constructor.
  - rewrite !Forall_cons_iff, IH.
    assert (X : hole_ok E y l (msubsts sg m) <-> hole_ok (updl E sg) y l m).
    { unfold hole_ok, is_hole, msubsts, uE. cbn [am_kind am_base am_len]. rewrite !esubsts_denot. tauto. }
    rewrite X. tauto.
Qed.

Lemma fds_ok_insts : forall E sg f model, fds_ok E (fsubsts sg f) model <-> fds_ok (updl E sg) f model.
Proof.
  intros E sg f model. destruct f as [|k l o|]; cbn [fsubsts fds_ok]; try tauto.
  unfold uE. rewrite !esubsts_denot. cbn [eb updl]. tauto.
Qed.

Lemma cs_ok_insts : forall E sg inv R FULL model, sg_dom_ge nx0 sg = true -> s_log (a_ss inv) = [] ->
  cs_ok E (insts sg inv) R FULL model <-> cs_ok (updl E sg) inv R FULL model.
Proof.
  intros E sg inv R FULL model Hsg Hlog.
  pose proof (insts_hid E sg inv model Hsg) as HH. pose proof (insts_allowA E sg inv) as HA. pose proof (insts_maps E sg inv) as HM.
  pose proof (insts_in_ghost E sg inv) as HG.
  assert (AG : env_agree nx0 E (updl E sg)) by (apply updl_agree; exact Hsg).
  split; intros HC; destruct HC; constructor;
    cbn [insts a_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset mk_ss] in *;
    rewrite <- ?HA, <- ?HM; try assumption.
  - apply regs_ok_insts. assumption.
  - unfold Mr. rewrite <- HH. apply (know_ok_ksubsts SEGS). exact co_know0.
  - apply fds_ok_insts. assumption.
  - apply (proj1 (maps_match_msubsts E sg _ _)). assumption.
  - apply (proj1 (holes_msubsts E sg _ _ _)). assumption.
  - apply Forall_forall. intros m Hin Hk.
    pose proof (proj1 (Forall_forall _ _) co_none0 (msubsts sg m) ltac:(apply in_map; exact Hin) Hk) as X.
    unfold amap_den, msubsts in X |- *. cbn [am_base am_len am_kind] in X. rewrite !esubsts_denot in X. exact X.
  - apply Forall_forall. intros m Hin Hk a Ha.
    pose proof (proj1 (Forall_forall _ _) co_kinds0 (msubsts sg m) ltac:(apply in_map; exact Hin) Hk a) as X.
    unfold msubsts in X. cbn [am_base am_len] in X. rewrite !esubsts_denot in X. exact (X Ha).
  - (* [comment removed for export] *) rewrite (e_sp0_agree _ _ _ AG (le_n _)). assumption.
  - rewrite <- esubsts_denot. assumption.
  - intros a. unfold Mr in *. rewrite <- HH. first [rewrite HG | rewrite <- HG]. exact (co_zero0 a).
  - eapply SINV_agree; [exact AG | assumption].
  - apply regs_ok_insts. assumption.
  - reflexivity.
  - unfold Mr in *. rewrite HH. apply (know_ok_ksubsts SEGS). assumption.
  - apply fds_ok_insts. assumption.
  - apply (proj2 (maps_match_msubsts E sg _ _)). assumption.
  - apply (proj2 (holes_msubsts E sg _ _ _)). assumption.
  - apply Forall_forall. intros m' Hin Hk. apply in_map_iff in Hin as [m [<- Hin]].
    pose proof (proj1 (Forall_forall _ _) co_none0 m Hin Hk) as X.
    unfold amap_den, msubsts. cbn [am_base am_len am_kind]. rewrite !esubsts_denot. exact X.
  - apply Forall_forall. intros m' Hin Hk a Ha. apply in_map_iff in Hin as [m [<- Hin]].
    unfold msubsts in Ha, Hk. cbn [am_base am_len am_kind] in Ha, Hk. rewrite !esubsts_denot in Ha.
    exact (proj1 (Forall_forall _ _) co_kinds0 m Hin Hk a Ha).
  - (* [comment removed for export] *) rewrite <- (e_sp0_agree _ _ _ AG (le_n _)). assumption.
  - rewrite esubsts_denot. assumption.
  - rewrite HA. assumption.
  - rewrite HA. assumption.
  - intros a. unfold Mr in *. rewrite HH. first [rewrite <- HG | rewrite HG]. exact (co_zero0 a).
  - eapply SINV_agree; [|eassumption]. destruct AG as [AG1 AG2]. split; [intros n Hn; symmetry; apply AG1; exact Hn | symmetry; exact AG2].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma saddr_eqb_h_estart : forall E M k b o b' o' n ne,
  know_ok SEGS E M k -> saddr_eqb_h (SA b o) (SA b' o') = true -> flat E (SA b o) n ->
  flat_x k b' o' ne = true -> estart E (SA b' o') = estart E (SA b o).
Proof.
  intros E M k b o b' o' n ne HK Hs Hf Hf'. unfold saddr_eqb_h in Hs. cbn [a_base a_off] in *.
  apply orb_prop in Hs as [Hs|Hs]; [apply saddr_eqb_eq in Hs; injection Hs as -> ->; reflexivity|].
  apply expr_eqb_eq in Hs. apply (f_equal (fun x => bv_unsigned (edenot E x))) in Hs.
  unfold eaddz in Hs. rewrite !mkAlu_denot, !u_add64 in Hs. cbn [edenot] in Hs. rewrite !u_lit64 in Hs.
  pose proof (flat_x_sound E M k b' o' ne HK Hf') as (F1 & F2 & F3). pose proof (u64_range (edenot E ne)).
  unfold flat, estart in *; cbn [a_base a_off] in *.
  pose proof (u64_range (edenot E b)). pose proof (u64_range (edenot E b')). unfold two64 in Hs.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (E1 : (bv_unsigned (edenot E b) + o mod 2 ^ 64) mod 2 ^ 64 = bv_unsigned (edenot E b) + o) by (rewrite Zplus_mod_idemp_r; apply Z.mod_small; lia).
  assert (E2 : (bv_unsigned (edenot E b') + o' mod 2 ^ 64) mod 2 ^ 64 = bv_unsigned (edenot E b') + o') by (rewrite Zplus_mod_idemp_r; apply Z.mod_small; lia).
  lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
Lemma klen_weaker_sound : forall E M k X K,
  know_ok SEGS E M k -> kentry_ok SEGS E M X -> klen_weaker k X K = true -> kflat_h k K = true -> kentry_ok SEGS E M K.
Proof.
  intros E M k X K HK HX Hw Hfl.
  assert (LEN : forall n n', lin_ge0 k [(n, 0)] [(n', 0)] = true -> elenZ E n' <= elenZ E n).
  { intros n n' H. pose proof (lin_ge0_sound SEGS E M k _ _ HK H) as G. cbn [xt_den fst snd] in G. unfold elenZ. lia. }
  destruct X as [[b o] w v|[b o] n|[b o] n kk| | | |[b o] n| |[b o] n c|[b o] n];
    destruct K as [[b' o'] w' v'|[b' o'] n'|[b' o'] n' kk'| | | |[b' o'] n'| |[b' o'] n' c'|[b' o'] n']; try discriminate;
    cbn [klen_weaker] in Hw;
    repeat match type of Hw with (_ && _)%bool = true => apply andb_prop in Hw as [Hw ?X] end;
    cbn [kentry_ok kflat_h] in *.
  - (* [comment removed for export] *) destruct HX as [H1 H2]. pose proof (LEN _ _ X) as Hle.
    pose proof (saddr_eqb_h_estart E M k b o b' o' _ _ HK Hw H1 Hfl) as ES.
    pose proof (flat_x_sound E M k b' o' n' HK Hfl) as F. pose proof (u64_range (edenot E n')) as U.
    split; [unfold flat, elenZ in *; lia|]. rewrite ES. intros i Hi. apply H2. lia.
  - (* [comment removed for export] *) destruct HX as [H1 H2]. pose proof (LEN _ _ X) as Hle.
    pose proof (saddr_eqb_h_estart E M k b o b' o' _ _ HK Hw H1 Hfl) as ES.
    pose proof (flat_x_sound E M k b' o' n' HK Hfl) as F. pose proof (u64_range (edenot E n')) as U.
    split; [unfold flat, elenZ in *; lia|]. rewrite ES. intros d m Hd Hm. apply H2; lia.
  - (* [comment removed for export] *) destruct HX as [H1 H2]. pose proof (LEN _ _ X) as Hle. apply Z.eqb_eq in X0. subst c'.
    pose proof (saddr_eqb_h_estart E M k b o b' o' _ _ HK Hw H1 Hfl) as ES.
    pose proof (flat_x_sound E M k b' o' n' HK Hfl) as F. pose proof (u64_range (edenot E n')) as U.
    split; [unfold flat, elenZ in *; lia|]. rewrite ES. intros i Hi. apply H2. lia.
  - (* [comment removed for export] *) destruct HX as [H1 H2]. pose proof (LEN _ _ X) as Hle.
    pose proof (saddr_eqb_h_estart E M k b o b' o' _ _ HK Hw H1 Hfl) as ES.
    pose proof (flat_x_sound E M k b' o' n' HK Hfl) as F. pose proof (u64_range (edenot E n')) as U.
    split; [unfold flat, elenZ in *; lia|]. rewrite ES. intros i Hi. apply H2. lia.
Qed.

(* [comment removed for export] *)

Lemma uE_eaddz : forall E x c, 0 <= uE E x + c < 2 ^ 64 -> uE E (eaddz x c) = uE E x + c.
Proof.
  intros E x c H. unfold uE, eaddz in *. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite u_lit64. unfold two64.
  rewrite Zplus_mod_idemp_r. apply Z.mod_small. exact H.
Qed.
Lemma uE_eadd : forall E x y, uE E x + uE E y < 2 ^ 64 -> uE E (eadd x y) = uE E x + uE E y.
Proof.
  intros E x y H. unfold uE, eadd in *. rewrite mkAlu_denot, u_add64. unfold two64.
  pose proof (u64_range (edenot E x)). pose proof (u64_range (edenot E y)). apply Z.mod_small. lia.
Qed.

Lemma cover_step_sound : forall E M k cur kb kk len cur',
  know_ok SEGS E M k -> cover_step k cur kb kk len = Some cur' -> flat E (SA kb kk) (elenZ E len) ->
  estart E (SA kb kk) <= uE E cur /\ uE E cur' = estart E (SA kb kk) + elenZ E len.
Proof.
  intros E M k cur kb kk len cur' HK H Hfl. unfold cover_step in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection H as <-.
  apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 _].
  pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as G1.
  pose proof (lin_ge0_sound SEGS E M k _ _ HK H3) as G3. cbn [xt_den fst snd] in G1, G3.
  cbn [edenot] in G3. rewrite u_lit64 in G3. unfold two64m1, two64 in G3.
  rewrite (Z.mod_small 0) in G3 by lia.
  destruct Hfl as (F1 & F2 & F3 & F4). unfold estart, elenZ in *; cbn [a_base a_off] in *. unfold uE in *.
  pose proof (u64_range (edenot E len)).
  split; [lia|].
  unfold eadd, eaddz. rewrite mkAlu_denot, u_add64, mkAlu_denot, u_add64. cbn [edenot]. rewrite u_lit64. unfold two64.
  rewrite Zplus_mod_idemp_r. rewrite (Z.mod_small (bv_unsigned (edenot E kb) + kk)) by lia. apply Z.mod_small. lia.
Qed.

Lemma cover_sym1_sound : forall E M allk rem wok cur cur' rem',
  know_ok SEGS E M allk -> (forall X, In X rem -> In X allk) -> cover_sym1 allk rem wok cur = Some (cur', rem') ->
  (forall X, In X rem' -> In X allk) /\
  forall z, uE E cur <= z < uE E cur' -> (wok = true -> in_hull A z = false) -> M (Z_to_bv 64 z) <> None.
Proof.
  intros E M allk rem wok cur. induction rem as [|X r IH]; intros cur' rem' HK Hsub H; [discriminate|].
  cbn [cover_sym1] in H.
  match type of H with (match ?h with Some e0 => _ | None => _ end = _) => destruct h as [c1|] eqn:Hhit end.
  2: { destruct (cover_sym1 allk r wok cur) as [[c2 r2]|] eqn:Hrec; [|discriminate]. injection H as <- <-.
       destruct (IH c2 r2 HK ltac:(intros X' HX'; apply Hsub; right; exact HX') eq_refl) as [S1 S2].
       split; [|exact S2]. intros X' [<-|HX']; [apply Hsub; left; reflexivity | apply S1; exact HX']. }
  injection H as <- <-.
  split; [intros X' HX'; apply Hsub; right; exact HX'|].
  pose proof (proj1 (Forall_forall _ _) HK X (Hsub X ltac:(left; reflexivity))) as HX. clear IH.
  assert (DEF : forall kb kk len (P : option byte -> Prop),
            (flat E (SA kb kk) (elenZ E len) /\ forall i0, (0 <= i0 < elenZ E len)%Z -> P (M (Z_to_bv 64 (estart E (SA kb kk) + i0)))) ->
            (forall x, P x -> x <> None) -> cover_step allk cur kb kk len = Some c1 ->
            forall z, uE E cur <= z < uE E c1 -> (wok = true -> in_hull A z = false) -> M (Z_to_bv 64 z) <> None).
  { intros kb kk len P [Hfl Hall] HP Hc z Hz _.
    destruct (cover_step_sound E M allk cur kb kk len c1 HK Hc Hfl) as [S1 S3].
    replace z with (estart E (SA kb kk) + (z - estart E (SA kb kk)))%Z by lia. apply HP. apply Hall. lia. }
  destruct X as [[kb kk] w v|[kb kk] len|[kb kk] len bk| | | | | |[kb kk] len fc|[kb kk] len]; try discriminate.
  - (* [comment removed for export] *)
    destruct wok; [|discriminate].
    cbn [kentry_ok] in HX. destruct HX as (Hw & Hfl & Hrd).
    assert (Hfl' : flat E (SA kb kk) (elenZ E (ELit (Z.of_nat w)))) by (rewrite elenZ_lit by lia; exact Hfl).
    destruct (cover_step_sound E M allk cur kb kk (ELit (Z.of_nat w)) c1 HK Hhit Hfl') as [S1 S3].
    rewrite elenZ_lit in S3 by lia.
    pose proof (flat_u E _ _ Hfl) as Hu.
    intros z Hz Hh. pose proof (Hh eq_refl) as Hh'.
    assert (Hz' : (0 <= z < 2 ^ 64)%Z) by (destruct Hfl as (F1 & F2 & F3 & F4); lia).
    pose proof (rdn_bytes_some M _ w _ Hrd (Z_to_bv 64 z)) as R0. rewrite Hu, u_small in R0 by lia.
    apply R0; [lia | exact Hh'].
  - (* [comment removed for export] *) eapply (DEF kb kk len (fun x => x = Some (Z_to_bv 8 0))); [exact HX | intros x ->; discriminate | exact Hhit].
  - (* [comment removed for export] *) cbn [kentry_ok] in HX. destruct HX as (Hfl & Hlen & Hall).
    eapply (DEF kb kk len (fun x => exists b0, x = Some b0)); [split; [exact Hfl | intros i0 Hi0; eexists; apply Hall; exact Hi0] | intros x [b0 ->]; discriminate | exact Hhit].
  - (* [comment removed for export] *) eapply (DEF kb kk len (fun x => x = Some (Z_to_bv 8 fc))); [exact HX | intros x ->; discriminate | exact Hhit].
  - (* [comment removed for export] *) eapply (DEF kb kk len (fun x => x <> None)); [exact HX | intros x Hx; exact Hx | exact Hhit].
Qed.

Lemma cover_sym_go_sound : forall fuel E M k rem wok cur stop,
  know_ok SEGS E M k -> (forall X, In X rem -> In X k) -> cover_sym_go fuel k rem wok cur stop = true ->
  forall z, uE E cur <= z < uE E stop -> (wok = true -> in_hull A z = false) -> M (Z_to_bv 64 z) <> None.
Proof.
  induction fuel as [|f IH]; intros E M k rem wok cur stop HK Hsub H z Hz Hh; [discriminate|].
  cbn [cover_sym_go] in H.
  destruct (lin_ge0 k [(cur, 0)] [(stop, 0)]) eqn:Hge.
  { pose proof (lin_ge0_sound SEGS E M k _ _ HK Hge) as G. cbn [xt_den fst snd] in G. unfold uE in *. lia. }
  destruct (cover_sym1 k rem wok cur) as [[cur' rem']|] eqn:H1; [|discriminate].
  destruct (cover_sym1_sound E M k rem wok cur cur' rem' HK Hsub H1) as [Hsub' Hcov].
  destruct (Z.lt_ge_cases z (uE E cur')).
  - apply Hcov; [lia | exact Hh].
  - eapply IH; [exact HK | exact Hsub' | exact H | lia | exact Hh].
Qed.

Lemma kunk_cover_sym_sound : forall E M k K, know_ok SEGS E M k -> kunk_cover_sym A k K = true -> kentry_ok SEGS E M K.
Proof.
  intros E M k K HK H. unfold kunk_cover_sym in H.
  destruct K as [| | | | | | | | |[b o] n]; try discriminate.
  apply andb_prop in H as [H Hgo]. apply andb_prop in H as [Hfl Hnw].
  cbn [kflat_h] in Hfl. pose proof (flat_x_sound E M k b o n HK Hfl) as (F1 & F2 & F3).
  pose proof (lin_ge0_sound SEGS E M k _ _ HK Hnw) as G. cbn [xt_den fst snd] in G.
  cbn [edenot] in G. rewrite u_lit64 in G. unfold two64m1, two64 in G. rewrite (Z.mod_small 0) in G by lia.
  unfold estart in *; cbn [a_base a_off] in *. pose proof (u64_range (edenot E n)) as Hn.
  assert (C0 : uE E (eaddz b o) = bv_unsigned (edenot E b) + o) by (apply uE_eaddz; unfold uE; lia).
  assert (C1 : uE E (eadd (eaddz b o) n) = bv_unsigned (edenot E b) + o + bv_unsigned (edenot E n)).
  { rewrite uE_eadd; [rewrite C0; reflexivity | rewrite C0; unfold uE; lia]. }
  cbn [kentry_ok]. split; [unfold flat, estart, elenZ; cbn [a_base a_off]; lia|].
  intros i Hi. unfold elenZ in Hi.
  apply (cover_sym_go_sound _ E M k k _ _ _ HK ltac:(intros X HX; exact HX) Hgo); [rewrite C0, C1; unfold estart; cbn [a_base a_off]; lia|].
  intros Hw. apply andb_prop in Hw as [Hle Hoff]. apply Z.leb_le in Hle.
  pose proof (ranges_apart_x_sound SEGS E M k _ _ _ _ _ _ HK Hoff) as AP0.
  unfold estart in AP0; cbn [a_base a_off edenot] in AP0. rewrite u_lit0 in AP0.
  rewrite (elenZ_lit E (img_hi A - img_lo A)) in AP0 by (pose proof HULL_ok as HU; unfold hull_ok, KHI in HU; lia).
  unfold elenZ in AP0. unfold in_hull, estart; cbn [a_base a_off]. apply andb_false_iff.
  destruct AP0 as [AP0|AP0]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.

(* [comment removed for export] *)
Lemma coverw_sym1_sound : forall E M allk rem cur cur' rem',
  know_ok SEGS E M allk -> (forall X, In X rem -> In X allk) -> coverw_sym1 allk rem cur = Some (cur', rem') ->
  (forall X, In X rem' -> In X allk) /\
  forall z, uE E cur <= z < uE E cur' -> wview SEGS M (Z_to_bv 64 z) <> None.
Proof.
  intros E M allk rem cur. induction rem as [|X r IH]; intros cur' rem' HK Hsub H; [discriminate|].
  cbn [coverw_sym1] in H.
  destruct (coverw_step allk cur X) as [c1|] eqn:Hhit.
  2: { destruct (coverw_sym1 allk r cur) as [[c2 r2]|] eqn:Hrec; [|discriminate]. injection H as <- <-.
       destruct (IH c2 r2 HK ltac:(intros X' HX'; apply Hsub; right; exact HX') eq_refl) as [S1 S2].
       split; [|exact S2]. intros X' [<-|HX']; [apply Hsub; left; reflexivity | apply S1; exact HX']. }
  injection H as <- <-.
  split; [intros X' HX'; apply Hsub; right; exact HX'|].
  pose proof (proj1 (Forall_forall _ _) HK X (Hsub X ltac:(left; reflexivity))) as HX. clear IH.
  destruct X as [| | | | | |[kb kk] len| | |]; try discriminate Hhit. cbn [coverw_step] in Hhit.
  cbn [kentry_ok] in HX. destruct HX as [Hfl Hs].
  destruct (cover_step_sound E M allk cur kb kk len c1 HK Hhit Hfl) as [S1 S3].
  intros z Hz.
  pose proof Hfl as (F1 & F2 & F3 & F4). unfold estart in *; cbn [a_base a_off] in *.
  pose proof (Hs (z - (bv_unsigned (edenot E kb) + kk))%Z 1%nat ltac:(lia) ltac:(cbn; lia)) as W1.
  cbn [store_ok] in W1.
  replace (bv_unsigned (edenot E kb) + kk + (z - (bv_unsigned (edenot E kb) + kk)))%Z with z in W1 by lia.
  destruct (wview SEGS M (Z_to_bv 64 z)); [discriminate | discriminate W1].
Qed.

Lemma coverw_go_sound : forall fuel E M k rem cur stop,
  know_ok SEGS E M k -> (forall X, In X rem -> In X k) -> coverw_go fuel k rem cur stop = true ->
  forall z, uE E cur <= z < uE E stop -> wview SEGS M (Z_to_bv 64 z) <> None.
Proof.
  induction fuel as [|f IH]; intros E M k rem cur stop HK Hsub H z Hz; [discriminate|].
  cbn [coverw_go] in H.
  destruct (lin_ge0 k [(cur, 0)] [(stop, 0)]) eqn:Hge.
  { pose proof (lin_ge0_sound SEGS E M k _ _ HK Hge) as G. cbn [xt_den fst snd] in G. unfold uE in *. lia. }
  destruct (coverw_sym1 k rem cur) as [[cur' rem']|] eqn:H1; [|discriminate].
  destruct (coverw_sym1_sound E M k rem cur cur' rem' HK Hsub H1) as [Hsub' Hcov].
  destruct (Z.lt_ge_cases z (uE E cur')).
  - apply Hcov. lia.
  - eapply IH; [exact HK | exact Hsub' | exact H | lia].
Qed.

Lemma kwr_cover_sym_sound : forall E M k K, know_ok SEGS E M k -> kwr_cover_sym k K = true -> kentry_ok SEGS E M K.
Proof.
  intros E M k K HK H. unfold kwr_cover_sym in H.
  destruct K as [| | | | | |[b o] n| | |]; try discriminate.
  apply andb_prop in H as [H Hgo]. apply andb_prop in H as [Hfl Hnw].
  cbn [kflat_h] in Hfl. pose proof (flat_x_sound E M k b o n HK Hfl) as (F1 & F2 & F3).
  pose proof (lin_ge0_sound SEGS E M k _ _ HK Hnw) as G. cbn [xt_den fst snd] in G.
  cbn [edenot] in G. rewrite u_lit64 in G. unfold two64m1, two64 in G. rewrite (Z.mod_small 0) in G by lia.
  unfold estart in *; cbn [a_base a_off] in *. pose proof (u64_range (edenot E n)) as Hn.
  assert (C0 : uE E (eaddz b o) = bv_unsigned (edenot E b) + o) by (apply uE_eaddz; unfold uE; lia).
  assert (C1 : uE E (eadd (eaddz b o) n) = bv_unsigned (edenot E b) + o + bv_unsigned (edenot E n)).
  { rewrite uE_eadd; [rewrite C0; reflexivity | rewrite C0; unfold uE; lia]. }
  cbn [kentry_ok]. split; [unfold flat, estart, elenZ; cbn [a_base a_off]; lia|].
  unfold estart, elenZ; cbn [a_base a_off]. intros d m Hd Hdm.
  apply store_ok_of_all; [rewrite u_small by lia; lia|].
  intros x Hx. rewrite u_small in Hx by lia.
  rewrite <- (Z_to_bv_bv_unsigned 64 x).
  apply (coverw_go_sound _ E M k k _ _ HK ltac:(intros X HX; exact HX) Hgo). rewrite C0, C1. lia.
Qed.

(* [comment removed for export] *)
Lemma kwr_incl_sound : forall E M k b o n,
  know_ok SEGS E M k -> kflat_h k (KWr (SA b o) n) = true -> kwritable_x k k b o n = true -> kentry_ok SEGS E M (KWr (SA b o) n).
Proof.
  intros E M k b o n HK Hfl H. cbn [kflat_h] in Hfl. pose proof (flat_x_sound E M k b o n HK Hfl) as FX.
  assert (GEN : forall k', know_ok SEGS E M k' -> kwritable_x k k' b o n = true -> kentry_ok SEGS E M (KWr (SA b o) n)).
  { intros k'. induction k' as [|K rest IH]; intros HK' H'; [discriminate|].
    apply Forall_cons_iff in HK' as [HKK Hrest]. cbn [kwritable_x] in H'.
    destruct K as [| | | | | |[wb wk] wn| | |]; try exact (IH Hrest H').
    assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kwritable_x k rest b o n) = true ->
                   (c1 || c2)%bool = true \/ kwritable_x k rest b o n = true) by (intros [|] [|]; cbn; auto).
    apply H2w in H'. destruct H' as [H'|H']; [|exact (IH Hrest H')].
    cbn [kentry_ok] in HKK. destruct HKK as [Hflw Hs]. pose proof Hflw as (F1 & F2 & F3 & F4).
    unfold estart in Hs, F1, F2, F4. cbn [a_base a_off] in Hs, F1, F2, F4.
    pose proof (u64_range (edenot E n)) as Hnr.
    assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + o ->
                   bv_unsigned (edenot E b) + o + elenZ E n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
                   kentry_ok SEGS E M (KWr (SA b o) n)).
    { intros A1 B1. cbn [kentry_ok]. split.
      { unfold flat. unfold estart in FX |- *. cbn [a_base a_off] in FX |- *. unfold elenZ in *. lia. }
      unfold estart. cbn [a_base a_off].
      intros d m Hd Hdm.
      replace (bv_unsigned (edenot E b) + o + d) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + o + d - (bv_unsigned (edenot E wb) + wk))) by lia.
      apply Hs; lia. }
    apply orb_prop in H' as [H'|H'].
    - destruct (expr_eqb b wb && Z.leb wk o)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
      apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
      destruct (xhi k n) as [nh|] eqn:Hxh; [|discriminate].
      destruct (xlo k wn) as [wl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H'.
      pose proof (xhi_sound SEGS E M k n nh HK Hxh). pose proof (xlo_sound SEGS E M k wn wl HK Hxl).
      apply CORE; unfold elenZ in *; lia.
    - pose proof (xinside_sound SEGS E M k b o n wb wk wn HK H') as [A1 B1].
      unfold estart in A1, B1. cbn [a_base a_off] in A1, B1. apply CORE; lia. }
  exact (GEN k HK H).
Qed.

Lemma kn_incl1_s_sound : forall E M k K, know_ok SEGS E M k -> kn_incl1_s A k K = true -> kentry_ok SEGS E M K.
Proof.
  intros E M k K HK H. unfold kn_incl1_s in H.
  destruct (kn_incl1_h A k K) eqn:Hh.
  { pose proof (kn_incl_h_sound E M k [K] HK ltac:(unfold kn_incl_h; cbn [forallb]; rewrite Hh; reflexivity)) as X.
    exact (Forall_inv X). }
  assert (WEAK : (if kflat_h k K then existsb (fun X => klen_weaker k X K) k else false) = true -> kentry_ok SEGS E M K).
  { intros Hw. destruct (kflat_h k K) eqn:Hfl; [|discriminate]. apply existsb_exists in Hw as [X [HinX HwX]].
    eapply klen_weaker_sound; [exact HK | exact (proj1 (Forall_forall _ _) HK X HinX) | exact HwX | exact Hfl]. }
  destruct K as [a w v|a n|a n kk|lo hi|x m|x lo hi|a n|a1 n1 a2 n2|a n c|a n]; try discriminate; try (exact (WEAK H)).
  - (* [comment removed for export] *) eapply fact_ok_sound; [exact HK | exact H].
  - (* [comment removed for export] *) destruct (fact_ok k (KRange x lo hi)) eqn:Hf.
    + eapply fact_ok_sound; [exact HK | exact Hf].
    + cbn [kentry_ok]. eapply (krange_lin_sound SEGS); [exact HK | exact H].
  - (* [comment removed for export] *)
    destruct a as [b o]. destruct (kflat_h k (KWr (SA b o) n)) eqn:Hfl; [|discriminate].
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hw end.
    + apply WEAK. reflexivity.
    + destruct (kwritable_x k k b o n) eqn:Hx.
      * eapply kwr_incl_sound; [exact HK | exact Hfl | exact Hx].
      * eapply kwr_cover_sym_sound; [exact HK | exact H].
  - (* [comment removed for export] *) eapply fact_ok_sound; [exact HK | exact H].
  - (* [comment removed for export] *)
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hw; [exact (WEAK eq_refl)|] end.
    eapply kunk_cover_sym_sound; [exact HK | exact H].
Qed.

Lemma kn_incl_s_sound : forall E M k tk, know_ok SEGS E M k -> kn_incl_s A k tk = true -> know_ok SEGS E M tk.
Proof.
  intros E M k tk HK H. apply Forall_forall. intros K Hin.
  destruct (kn_incl_s_cases A k tk H K Hin) as [Hk|H1].
  - exact (proj1 (Forall_forall _ _) HK K Hk).
  - eapply kn_incl1_s_sound; [exact HK | exact H1].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma template_ok_facts : forall lo x, template_ok nx0 lo x = true ->
  fresh_ok nx0 x = true /\ s_log (a_ss x) = [] /\ length (s_regs (a_ss x)) = 32%nat /\ (lo <= nxt x)%nat.
Proof.
  intros lo x H. unfold template_ok in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  destruct (s_log (a_ss x)); [|discriminate]. apply Nat.eqb_eq in X0. apply Nat.leb_le in X.
  repeat split; assumption.
Qed.

Lemma head_ok_facts : forall lo V T, head_ok nx0 lo V T = true ->
  fresh_ok nx0 T = true /\ s_log (a_ss T) = [] /\ length (s_regs (a_ss T)) = 32%nat /\ (lo <= nxt T)%nat /\
  AP.expr_vars_lt (nxt T) V = true.
Proof.
  intros lo V T H. unfold head_ok in H. apply andb_prop in H as [H HV].
  destruct (template_ok_facts lo T H) as (F1 & F2 & F3 & F4). repeat split; assumption.
Qed.

Lemma while_okN_facts : forall cs lo hs V xs, while_okN nx0 cs lo hs V xs = true ->
  (nx0 <= lo)%nat /\ (nxt cs <= lo)%nat /\ (forall T, In T hs -> head_ok nx0 lo V T = true) /\
  (is_snext xs = true \/ no_next xs = true) /\ shape_vars_lt nx0 xs = true.
Proof.
  intros cs lo hs V xs H. unfold while_okN in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Nat.leb_le in H. apply Nat.leb_le in X2. apply orb_prop in X0.
  split; [exact H|]. split; [exact X2|]. split; [intros T HT; exact (proj1 (forallb_forall _ _) X1 T HT)|].
  split; [exact X0 | exact X].
Qed.

(* [comment removed for export] *)
Lemma chk_heads_ok : forall (chk : option loopctx -> acs -> plan -> cres) hs lo V xs xts l cur s,
  chk_heads chk hs cur lo V xs xts l = COk s ->
  s = xs /\ forall i T b, nth_error l i = Some (T, b) -> chk (Some (WC hs (cur + i) lo (nxt T) V xs xts)) T b = COk xs.
Proof.
  intros chk hs lo V xs xts l. induction l as [|[T b] rest IH]; intros cur s H; cbn [chk_heads] in H.
  - injection H as <-. split; [reflexivity | intros [|i] T b HT; discriminate].
  - destruct (chk (Some (WC hs cur lo (nxt T) V xs xts)) T b) as [sb| |] eqn:Hb; [|discriminate|destruct (chk_heads chk hs (Datatypes.S cur) lo V xs xts rest); discriminate].
    destruct (shape_eqb sb xs) eqn:He; [|discriminate]. apply shape_eqb_eq in He. subst sb.
    destruct (IH (Datatypes.S cur) s H) as [-> Hall]. split; [reflexivity|].
    intros [|i] T' b' HT; cbn [nth_error] in HT.
    + injection HT as <- <-. rewrite Nat.add_0_r. exact Hb.
    + rewrite <- Nat.add_succ_comm. exact (Hall i T' b' HT).
Qed.

(* [comment removed for export] *)
Lemma chk_exits_ok : forall (chk : acs -> plan -> cres) lo xs l xts,
  chk_exits nx0 chk lo xs l = XOk xts ->
  forall i x sx, nth_error xts i = Some (x, sx) ->
    exists kx, template_ok nx0 lo x = true /\ chk x kx = COk sx /\ (no_next sx = true \/ is_snext xs = true).
Proof.
  intros chk lo xs l. induction l as [|[x kx] rest IH]; intros xts H i x' sx Hi; cbn [chk_exits] in H.
  - injection H as <-. destruct i; discriminate.
  - destruct (template_ok nx0 lo x) eqn:Ht; [|discriminate].
    destruct (chk x kx) as [s| |] eqn:Hc; [|discriminate|discriminate].
    destruct (no_next s || is_snext xs)%bool eqn:Hn; [|discriminate].
    destruct (chk_exits nx0 chk lo xs rest) as [r|] eqn:Hr; [|discriminate]. injection H as <-.
    destruct i as [|i]; cbn [nth_error] in Hi.
    + injection Hi as <- <-. exists kx. split; [exact Ht|]. split; [exact Hc|]. apply orb_prop in Hn. exact Hn.
    + exact (IH r eq_refl i x' sx Hi).
Qed.

(* [comment removed for export] *)
Lemma chk_exits_err : forall (chk : acs -> plan -> cres) lo xs l e,
  chk_exits nx0 chk lo xs l = XErr e -> forall s, e <> COk s.
Proof.
  intros chk lo xs l. induction l as [|[x kx] rest IH]; intros e H s; cbn [chk_exits] in H; [discriminate|].
  destruct (template_ok nx0 lo x); [|injection H as <-; discriminate].
  destruct (chk x kx) as [sx|c w cs|mv]; [|injection H as <-; discriminate|injection H as <-; discriminate].
  destruct (no_next sx || is_snext xs)%bool; [|injection H as <-; discriminate].
  destruct (chk_exits nx0 chk lo xs rest) as [r|e'] eqn:Hr; [discriminate|]. injection H as <-. exact (IH e' eq_refl s).
Qed.

(* [comment removed for export] *)
Lemma sd_nonext : forall D1 D2 E fs s, no_next s = true -> sd D1 E fs s = sd D2 E fs s.
Proof.
  intros D1 D2 E fs s. induction s; cbn [no_next sd]; intros H; try reflexivity; try discriminate.
  - rewrite IHs by exact H. reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite IHs1, IHs2 by assumption. reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite IHs1, IHs2 by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sd_loop_shape : forall D E E' fs xs,
  (is_snext xs = true \/ no_next xs = true) -> shape_vars_lt nx0 xs = true -> env_agree nx0 E E' ->
  sd (sd D E fs xs) E' fs xs = sd D E fs xs.
Proof.
  intros D E E' fs xs [Hx|Hx] Hv Hag.
  - apply is_snext_eq in Hx. subst xs. reflexivity.
  - rewrite (sd_nonext (sd D E fs xs) D E' fs xs Hx). symmetry. apply sd_agree; assumption.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma check_all_ok : forall (chk : acs -> plan -> cres) k css s,
  check_all A chk k css = COk s ->
  (exists cs1, In cs1 css /\ chk cs1 k = COk s /\ True) /\ (forall cs, In cs css -> chk cs k = COk s).
Proof.
  intros chk k css s H. unfold check_all in H. destruct css as [|cs0 rest]; [discriminate|].
  destruct (chk cs0 k) as [s0| |] eqn:H0; [|discriminate|discriminate].
  match type of H with fold_left ?F rest (COk s0) = _ =>
  assert (GEN : forall l acc, fold_left F l acc = COk s ->
                 acc = COk s /\ forall cs, In cs l -> chk cs k = COk s) end.
  { induction l as [|c l IHl]; intros acc Hf; cbn [fold_left] in Hf.
    - split; [exact Hf | intros ? []].
    - destruct acc as [s1|c1 q1 r1|l1].
      + destruct (chk c k) as [s'| |] eqn:Hc'; [| apply IHl in Hf as [Hf _]; discriminate | apply IHl in Hf as [Hf _]; discriminate].
        destruct (shape_eqb s1 s') eqn:Hse; [| apply IHl in Hf as [Hf _]; discriminate].
        apply IHl in Hf as [E1 Hl]. injection E1 as ->. apply shape_eqb_eq in Hse. subst s'.
        split; [reflexivity|]. intros cs [<-|Hin]; [exact Hc' | apply Hl; exact Hin].
      + apply IHl in Hf as [Hf _]. discriminate.
      + apply IHl in Hf as [Hf _]. discriminate. }
  apply GEN in H as [E0 Hrest]. injection E0 as ->.
  split; [exists cs0; split; [left; reflexivity | split; [exact H0 | exact I]]|].
  intros cs [<-|Hin]; [exact H0 | apply Hrest; exact Hin].
Qed.

(* [comment removed for export] *)
Lemma cmerge_ok : forall r1 r2 ok s, cmerge r1 r2 ok = COk s -> exists s1 s2, r1 = COk s1 /\ r2 tt = COk s2 /\ ok s1 s2 = COk s.
Proof.
  intros [s1|c q x|l1] r2 ok s H; cbn [cmerge] in H; try discriminate.
  - destruct (r2 tt) as [s2|c q x|l2] eqn:H2; try discriminate. exists s1, s2. auto.
  - destruct (r2 tt) as [s2|c q x|l2]; discriminate.
Qed.
Lemma with_props_ok : forall cs gs r s, with_props xp cs gs r = COk s -> needs_props xp cs gs = [] /\ r = COk s.
Proof. intros cs gs r s H. unfold with_props in H. destruct (needs_props xp cs gs); [auto|discriminate]. Qed.

(* [comment removed for export] *)
Lemma anorm_sem : forall fk E M a, know_ok SEGS E M fk ->
  estart E (AP.anorm fk a) = estart E a /\ adenot E (AP.anorm fk a) = adenot E a.
Proof.
  intros fk E M [b off] HK. unfold AP.anorm. cbn [a_base a_off].
  assert (DFL : estart E (SA b off) = estart E (SA b off) /\ adenot E (SA b off) = adenot E (SA b off)) by (split; reflexivity).
  destruct b as [c|v|op b1 b2|op b1 b2|op b1 b2|op b1 b2|sx lo n b1|q1 q2 q3 q4]; try exact DFL.
  - (* [comment removed for export] *) unfold estart, adenot, v_addi. cbn [a_base a_off edenot]. rewrite !u_lit64, zlit64_eq.
    rewrite Z.mod_0_l by (unfold two64; lia). split; [lia | f_equal; lia].
  - destruct op; try exact DFL. destruct b2 as [z| | | | | | |]; try exact DFL.
    destruct (xlo fk b1) as [lo|] eqn:Hlo; [|exact DFL]. destruct (xhi fk b1) as [hi|] eqn:Hhi; [|exact DFL].
    destruct ((0 <=? lo + z) && (hi + z <? two64))%bool eqn:Hc; [|exact DFL].
    apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    pose proof (xlo_sound SEGS E M fk b1 lo HK Hlo) as L. pose proof (xhi_sound SEGS E M fk b1 hi HK Hhi) as H.
    unfold estart, adenot, v_addi. cbn [a_base a_off edenot]. rewrite u_add64, u_lit64 in *.
    unfold two64 in *. rewrite Zplus_mod_idemp_r, (Z.mod_small (bv_unsigned (edenot E b1) + z)) by lia.
    split; [lia | f_equal; lia].
Qed.
Lemma knorm_ok : forall fk K E M, know_ok SEGS E M fk -> kentry_ok SEGS E M K -> kentry_ok SEGS E M (AP.knorm fk K).
Proof.
  intros fk K E M HK H.
  destruct K; cbn [AP.knorm]; try exact H; cbn [kentry_ok] in H |- *; unfold flat in *;
    repeat match goal with |- context [AP.anorm fk ?a] => let X := fresh "X" in destruct (anorm_sem fk E M a HK) as [X ?Y]; rewrite ?X, ?Y; clear X end;
    exact H.
Qed.

(* [comment removed for export] *)
Definition apartw (E : env) (w : saddr * expr) (ka : saddr) (kl : expr) : Prop :=
  (estart E ka + elenZ E kl <= estart E (fst w) \/ estart E (fst w) + elenZ E (snd w) <= estart E ka)%Z.
Definition OKA (E : env) (M : word -> option byte) (n : nat) (D : list (saddr * expr)) (P : kentry) : Prop :=
  kentry_ok SEGS E M P /\ AP.kentry_vars_lt n P = true /\
  exists ka kl, AP.kfoot P = Some (ka, kl) /\ forall w, In w D -> apartw E w ka kl.

Lemma kresize_ok : forall E M b pk n0 K k' n' P nn,
  AP.kfoot K = Some (SA b pk, ELit n0) -> 0 <= n0 < two64 -> kentry_ok SEGS E M K ->
  AP.kresize K k' n' = Some P -> pk <= k' -> 0 < n' -> k' + n' <= pk + n0 ->
  AP.kentry_vars_lt nn K = true ->
  kentry_ok SEGS E M P /\ AP.kfoot P = Some (SA b k', ELit n') /\ AP.kentry_vars_lt nn P = true
  /\ estart E (SA b pk) <= estart E (SA b k') /\ estart E (SA b k') + elenZ E (ELit n') <= estart E (SA b pk) + elenZ E (ELit n0).
Proof.
  intros E M b pk n0 K k' n' P nn Hkf Hn0 HK Hrs Hle Hpos Hsub HV.
  unfold two64 in Hn0.
  assert (EL0 : elenZ E (ELit n0) = n0) by (unfold elenZ; cbn [edenot]; rewrite u_lit64; unfold two64; apply Z.mod_small; lia).
  assert (EL1 : elenZ E (ELit n') = n') by (unfold elenZ; cbn [edenot]; rewrite u_lit64; unfold two64; apply Z.mod_small; lia).
  assert (ES : estart E (SA b k') = estart E (SA b pk) + (k' - pk)) by (unfold estart; cbn [a_base a_off]; lia).
  destruct K as [[kb kk] w v|[kb kk] kn|[kb kk] kn bk|lo hi|ae am|re rlo rhi|[kb kk] kn|da1 dn1 da2 dn2|[kb kk] kn fc|[kb kk] kn];
    cbn [AP.kfoot AP.kresize] in Hkf, Hrs; try discriminate Hrs;
    injection Hkf as <- <- E3; subst kn; injection Hrs as <-; cbn [AP.kfoot AP.kentry_vars_lt] in HV |- *;
    unfold saddr_vars_lt in HV |- *; cbn [a_base expr_vars_lt] in HV |- *;
    apply andb_prop in HV as [HV _]; rewrite HV;
    cbn [kentry_ok] in HK |- *; rewrite EL0 in HK; rewrite EL1; rewrite ES;
    destruct HK as [HF HB]; unfold flat in HF |- *; rewrite ?ES.
  - (* [comment removed for export] *) repeat split; try lia; try reflexivity. intros i Hi. rewrite <- Z.add_assoc. apply HB. lia.
  - (* [comment removed for export] *) repeat split; try lia; try reflexivity. intros d m Hd Hdm. rewrite <- Z.add_assoc. apply HB; lia.
  - (* [comment removed for export] *) repeat split; try lia; try reflexivity. intros i Hi. rewrite <- Z.add_assoc. apply HB. lia.
  - (* [comment removed for export] *) repeat split; try lia; try reflexivity. intros i Hi. rewrite <- Z.add_assoc. apply HB. lia.
Qed.

Lemma cut_by_ok : forall fk E M Mk nn D w P P',
  know_ok SEGS E Mk fk -> OKA E M nn D P -> In P' (AP.cut_by fk w P) -> OKA E M nn (D ++ [w]) P'.
Proof.
  intros fk E M Mk nn D [[wb wk] wl] P P' HF (HK & HV & ka & kl & Hkf & HD) Hin.
  unfold AP.cut_by in Hin. rewrite Hkf in Hin. destruct ka as [pb pk]. cbn [fst snd] in Hin.
  destruct (ranges_apart_x fk pb pk kl wb wk wl) eqn:Hap.
  - destruct Hin as [<-|[]]. split; [exact HK|]. split; [exact HV|]. exists (SA pb pk), kl. split; [exact Hkf|].
    intros w' Hw'. apply in_app_or in Hw' as [Hw'|[<-|[]]]; [exact (HD w' Hw')|].
    unfold apartw. cbn [fst snd]. exact (ranges_apart_x_sound SEGS E Mk fk pb pk kl wb wk wl HF Hap).
  - destruct kl as [n0|v1|o1 e1 e2|o1 e1 e2|o1 e1 e2|o1 e1 e2|sx1 lo1 w1 e1|q1 q2 q3 q4]; cbn beta iota in Hin; try (destruct Hin; fail).
    destruct (expr_eqb pb wb && (0 <=? n0) && (n0 <? two64))%bool eqn:Hg; [|destruct Hin].
    apply andb_prop in Hg as [Hg Hn0b]. apply andb_prop in Hg as [Heqb Hn0a]. apply Z.leb_le in Hn0a. apply Z.ltb_lt in Hn0b.
    apply expr_eqb_eq in Heqb. subst wb.
    destruct (xhi fk wl) as [wh|] eqn:Hwh; [|destruct Hin].
    pose proof (xhi_sound SEGS E Mk fk wl wh HF Hwh) as WH.
    assert (PIECE : forall k' n' Q, AP.kresize P k' n' = Some Q -> pk <= k' -> 0 < n' -> k' + n' <= pk + n0 ->
              (k' + n' <= wk \/ wk + wh <= k') -> OKA E M nn (D ++ [(SA pb wk, wl)]) Q).
    { intros k' n' Q HQ H1 H2 H3 H4.
      destruct (kresize_ok E M pb pk n0 P k' n' Q nn Hkf ltac:(unfold two64 in *; lia) HK HQ H1 H2 H3 HV) as (Q1 & Q2 & Q3 & Q4 & Q5).
      split; [exact Q1|]. split; [exact Q3|]. exists (SA pb k'), (ELit n'). split; [exact Q2|].
      intros w' Hw'. apply in_app_or in Hw' as [Hw'|[<-|[]]].
      - pose proof (HD w' Hw') as X. unfold apartw in X |- *. lia.
      - unfold apartw. cbn [fst snd].
        assert (EL1 : elenZ E (ELit n') = n') by (unfold elenZ; cbn [edenot]; rewrite u_lit64; unfold two64 in *; apply Z.mod_small; lia).
        rewrite EL1. unfold estart. cbn [a_base a_off]. unfold elenZ in WH |- *.
        lia. }
    apply in_app_or in Hin as [Hin|Hin].
    + destruct (Z.ltb pk (Z.min (pk + n0) wk)) eqn:Hlt; [|destruct Hin]. apply Z.ltb_lt in Hlt.
      destruct (AP.kresize P pk (Z.min (pk + n0) wk - pk)) as [Q|] eqn:HQ; [|destruct Hin]. destruct Hin as [<-|[]].
      apply (PIECE _ _ _ HQ); lia.
    + destruct (Z.ltb (Z.max pk (wk + wh)) (pk + n0)) eqn:Hlt; [|destruct Hin]. apply Z.ltb_lt in Hlt.
      destruct (AP.kresize P (Z.max pk (wk + wh)) (pk + n0 - Z.max pk (wk + wh))) as [Q|] eqn:HQ; [|destruct Hin]. destruct Hin as [<-|[]].
      apply (PIECE _ _ _ HQ); lia.
Qed.

Lemma wcut_ok : forall fk E M Mk nn W D ps,
  know_ok SEGS E Mk fk -> (forall P, In P ps -> OKA E M nn D P) ->
  forall P, In P (fold_left (fun ps w => flat_map (AP.cut_by fk w) ps) W ps) -> OKA E M nn (D ++ W) P.
Proof.
  intros fk E M Mk nn W. induction W as [|w W IH]; intros D ps HF Hps P Hin.
  - cbn in Hin. rewrite app_nil_r. exact (Hps P Hin).
  - cbn [fold_left] in Hin. replace (D ++ w :: W) with ((D ++ [w]) ++ W) by (rewrite <- app_assoc; reflexivity).
    apply (IH (D ++ [w]) (flat_map (AP.cut_by fk w) ps) HF); [|exact Hin].
    intros Q HQ. apply in_flat_map in HQ as (P0 & HP0 & HQ). exact (cut_by_ok fk E M Mk nn D w P0 Q HF (Hps P0 HP0) HQ).
Qed.

(* [comment removed for export] *)
Lemma use_all_ok : forall chk mk p0 cs0 outs ks ss,
  AP.use_all chk mk p0 cs0 outs ks = AP.LOk ss ->
  length ss = length outs /\
  forall i x, nth_error outs i = Some x -> exists k s, nth_error ks i = Some k /\ nth_error ss i = Some s /\ chk (mk x) k = COk s.
Proof.
  intros chk mk p0 cs0 outs. induction outs as [|x outs IH]; intros [|k ks] ss H; cbn [AP.use_all] in H; try discriminate.
  - injection H as <-. split; [reflexivity|]. intros [|i] x Hx; discriminate.
  - destruct (chk (mk x) k) as [s0| |] eqn:Hc; try discriminate.
    destruct (AP.use_all chk mk p0 cs0 outs ks) as [ss'|r] eqn:Hr; [|discriminate]. injection H as <-.
    destruct (IH ks ss' Hr) as [Hlen Hi]. split; [cbn; lia|].
    intros [|i] x' Hx'; cbn [nth_error] in Hx' |- *.
    + injection Hx' as <-. exists k, s0. auto.
    + exact (Hi i x' Hx').
Qed.
Lemma use_all_err : forall chk mk p0 cs0 outs ks r s, AP.use_all chk mk p0 cs0 outs ks = AP.LErr r -> r = COk s -> False.
Proof.
  intros chk mk p0 cs0 outs. induction outs as [|x outs IH]; intros [|k ks] r s H Hr; cbn [AP.use_all] in H; subst r;
    try discriminate H; try (injection H as H'; discriminate H').
  destruct (chk (mk x) k) as [s0| |] eqn:Hc; [| injection H as H'; discriminate H' | injection H as H'; discriminate H'].
  destruct (AP.use_all chk mk p0 cs0 outs ks) as [ss'|r'] eqn:Hr'; [discriminate|]. injection H as ->. exact (IH ks (COk s) s Hr' eq_refl).
Qed.
Lemma splice_vars : forall b sh ss,
  shape_vars_lt b sh = true -> Forall (fun s => shape_vars_lt b s = true) ss -> shape_vars_lt b (AP.xsplice sh ss) = true.
Proof.
  intros b sh ss Hsh Hss. induction sh; cbn [AP.xsplice shape_vars_lt] in *; try reflexivity; try exact Hsh.
  - apply IHsh. exact Hsh.
  - apply andb_prop in Hsh as [H1 H2]. rewrite (IHsh1 H1), (IHsh2 H2). reflexivity.
  - apply andb_prop in Hsh as [H H3]. apply andb_prop in H as [H1 H2]. rewrite H1, (IHsh1 H2), (IHsh2 H3). reflexivity.
  - destruct (nth_error ss h) as [s0|] eqn:Hn.
    + rewrite (nth_error_nth ss h SNil Hn). exact (proj1 (Forall_forall _ _) Hss s0 (nth_error_In _ _ Hn)).
    + rewrite nth_overflow; [reflexivity|]. apply nth_error_None. exact Hn.
Qed.
Lemma segdef_wf_facts : forall SD, AP.segdef_wf nx0 SD = true ->
  (nx0 <= sg_lo SD)%nat /\ (sg_lo SD <= sg_hi SD)%nat /\ nxt (sg_in SD) = sg_hi SD /\ template_ok nx0 (sg_lo SD) (sg_in SD) = true
  /\ (forall i x, nth_error (sg_outs SD) i = Some x -> template_ok nx0 (sg_hi SD) x = true /\ AP.acs_frame_eqb (sg_in SD) x = true)
  /\ AP.wvars_lt (sg_hi SD) (sg_w SD) = true /\ shape_vars_lt nx0 (sg_shape SD) = true /\ no_next (sg_shape SD) = true
  /\ a_props (sg_in SD) = [].
Proof.
  intros SD H. unfold AP.segdef_wf in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Nat.leb_le in H.
  repeat match goal with Hl : Nat.leb _ _ = true |- _ => apply Nat.leb_le in Hl | Hl : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in Hl end.
  destruct (a_props (sg_in SD)); [|discriminate].
  split; [exact H|]. split; [exact X6|]. split; [exact X5|]. split; [exact X4|]. split.
  { intros i x Hi. pose proof (proj1 (forallb_forall _ _) X3 x (nth_error_In _ _ Hi)) as Y. apply andb_prop in Y as [Y1 Y2]. split; assumption. }
  repeat split; try assumption; reflexivity.
Qed.
(* [comment removed for export] *)
Lemma shiftb_get : forall lo top d v,
  sg_get (AP.shiftb lo top d) v = if ((lo <=? v) && (v <? top))%nat then Some (EVar (v + d)%nat) else None.
Proof.
  intros lo top d v. unfold AP.shiftb.
  assert (G : forall n st, sg_get (map (fun v0 : nat => (v0, EVar (v0 + d)%nat)) (seq st n)) v
                        = if ((st <=? v) && (v <? st + n))%nat then Some (EVar (v + d)%nat) else None).
  { induction n as [|n IH]; intros st; cbn [seq map sg_get].
    - destruct ((st <=? v)%nat && (v <? st + 0)%nat)%bool eqn:H; [|reflexivity].
      apply andb_prop in H as [H1 H2]. apply Nat.leb_le in H1. apply Nat.ltb_lt in H2. lia.
    - destruct (Nat.eqb_spec st v).
      + subst. replace ((v <=? v)%nat && (v <? v + Datatypes.S n)%nat)%bool with true; [reflexivity|].
        symmetry. apply andb_true_intro. split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia.
      + rewrite IH. destruct ((Datatypes.S st <=? v)%nat && (v <? Datatypes.S st + n)%nat)%bool eqn:H1; destruct ((st <=? v)%nat && (v <? st + Datatypes.S n)%nat)%bool eqn:H2; try reflexivity; exfalso.
        * apply andb_prop in H1 as [A1 A2]. apply Nat.leb_le in A1. apply Nat.ltb_lt in A2. apply andb_false_iff in H2 as [B|B]; [apply Nat.leb_gt in B | apply Nat.ltb_ge in B]; lia.
        * apply andb_prop in H2 as [A1 A2]. apply Nat.leb_le in A1. apply Nat.ltb_lt in A2. apply andb_false_iff in H1 as [B|B]; [apply Nat.leb_gt in B | apply Nat.ltb_ge in B]; lia. }
  rewrite G. destruct (Nat.leb_spec top lo).
  - replace (top - lo)%nat with 0%nat by lia. destruct ((lo <=? v)%nat && (v <? lo + 0)%nat)%bool eqn:H1; destruct ((lo <=? v)%nat && (v <? top)%nat)%bool eqn:H2; try reflexivity; exfalso.
    + apply andb_prop in H1 as [A1 A2]. apply Nat.leb_le in A1. apply Nat.ltb_lt in A2. lia.
    + apply andb_prop in H2 as [A1 A2]. apply Nat.leb_le in A1. apply Nat.ltb_lt in A2. lia.
  - replace (lo + (top - lo))%nat with top by lia. reflexivity.
Qed.
Lemma shiftb_dom_ge : forall lo top d b, (b <= lo)%nat -> sg_dom_ge b (AP.shiftb lo top d) = true.
Proof.
  intros lo top d b Hb. unfold sg_dom_ge, AP.shiftb. apply forallb_forall. intros [v e] Hin.
  apply in_map_iff in Hin as [v0 [Heq Hin]]. injection Heq as E1 E2. subst. apply in_seq in Hin. cbn [fst]. apply Nat.leb_le. lia.
Qed.
Lemma sg_top_ge : forall SD, (sg_hi SD <= AP.sg_top SD)%nat /\ forall i x, nth_error (sg_outs SD) i = Some x -> (nxt x <= AP.sg_top SD)%nat.
Proof.
  intros SD. unfold AP.sg_top.
  assert (G : forall l a, (a <= fold_left Nat.max l a)%nat /\ forall y, In y l -> (y <= fold_left Nat.max l a)%nat).
  { induction l as [|z l IH]; intros a; cbn [fold_left].
    - split; [lia | intros y []].
    - destruct (IH (Nat.max a z)) as [G1 G2]. split; [lia|]. intros y [<-|Hy]; [lia | apply G2; exact Hy]. }
  destruct (G (map nxt (sg_outs SD)) (sg_hi SD)) as [G1 G2]. split; [exact G1|].
  intros i x Hi. apply G2. apply in_map_iff. exists x. split; [reflexivity | eapply nth_error_In; exact Hi].
Qed.

(* [comment removed for export] *)
Lemma store_ok_memeq : forall k m1 m2 (a : word),
  (bv_unsigned a + Z.of_nat k <= 2^64)%Z ->
  (forall x : word, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat k)%Z -> m1 x = m2 x) ->
  store_ok SEGS m1 a k = store_ok SEGS m2 a k.
Proof.
  induction k as [|k IH]; intros m1 m2 a Hnw Hext; [reflexivity|].
  cbn [store_ok]. unfold wview. rewrite (Hext a ltac:(pose proof (u64_range a); lia)).
  destruct k as [|k'].
  - destruct (m2 a); [reflexivity|]. destruct (find_segment SEGS (bv_unsigned a) 1) as [sg|]; [|reflexivity]. destruct (seg_writable sg); reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
    assert (IH' : store_ok SEGS m1 (a + 1) (Datatypes.S k') = store_ok SEGS m2 (a + 1) (Datatypes.S k')).
    { apply IH; [lia|]. intros x Hx. apply Hext. lia. }
    fold (wview SEGS m2 a). unfold wview. rewrite IH'. reflexivity.
Qed.

Lemma check_vars : forall bfuel fuel lc p cs s,
  CHECK bfuel fuel lc cs p = COk s -> shape_vars_lt nx0 s = true.
Proof.
  intros bfuel fuel. induction fuel as [|fuel IH]; intros lc p cs s Hc; [discriminate|].
  cbn [AP.check] in Hc. rewrite ?AP.gkeepM_eq, ?AP.gkeepEM_eq, ?AP.gkeepPM_eq, ?AP.node_diamond_joinM_eq, ?AP.entails_hM_eq, ?AP.entails_sM_eq, ?AP.use_exitN_eqf, ?AP.instsN_eqf, ?AP.drop_ixsF_eqf in Hc.   (* [comment removed for export] *)
  match type of Hc with (if ?g then _ else _) = _ => destruct g; [discriminate|] end.
  assert (GW : forall r : cres, (if AP.wbb xp then CErr 11 p cs else r) = COk s -> r = COk s).
  { intros r Hr. unfold AP.wbb in Hr. destruct (xp_wb xp); [discriminate | exact Hr]. }
  assert (GWn : forall (b : bool) (r : cres), (if negb b then CErr 11 p cs else r) = COk s -> r = COk s).
  { intros b r Hr. destruct b; [exact Hr | discriminate]. }
  assert (GWa : forall (b : bool) (r : cres), (if (AP.wbb xp && b)%bool then CErr 11 p cs else r) = COk s -> r = COk s).
  { intros b r Hr. destruct (AP.wbb xp && b)%bool; [discriminate | exact Hr]. }
  destruct p as [stops k|e mid k1 k2|ce cmid ck1 ck2|db1 db2 dk1 dk2|sb1 sn1 sb2 sn2 k| |K k|jb joff jn k|ixs k|db dn k|gws k|bm k|hrs k|hbK k|r logc fb k|y k|ma|ib|qb|ka|x args k|xid xargs k|eid eargs k|bid bargs kb1 kb2|lJ lN linv lbody lk| |h| | |fi fsz fk|gi gsz gk|gb gn gk2|ub un uk|hlo hhi hk|ilo ihi ik|djp drs dk|rnm rnk|cpk|vj vjs vlo vka vk|mj|ab an ak|hws hwk|rsr rse rsk|wlo wheads wV wxs wexits|nh nwh|bi bh|usid uhints uks|gg gk|gi gdk|gK gfk|gtx gti gtK gtfk|sh slo shints|kga kgf|jjb1 jjb2 jjp jrs jk].
  - destruct (run_block_gc_wb_ws SEGS IT _ (AP.WB xp) KC bfuel (stops ++ STOPS A) cs) as [[cs1 W]|]; [|discriminate].
    lazymatch type of Hc with (if ?c then _ else _) = _ => destruct c end; [exact (IH _ (PRun stops k) _ s Hc) | exact (IH _ k _ s Hc)].   (* [comment removed for export] *)
  - destruct (AP.expr_vars_lt nx0 e) eqn:Hv; [|discriminate].
    destruct (erange (kn cs) e) as [[lo hi]|]; [|discriminate].
    destruct (Z.leb lo mid && Z.ltb mid hi)%bool.
    2: { destruct (Z.leb hi mid); [exact (IH _ k1 _ s Hc) | exact (IH _ k2 _ s Hc)]. }
    apply cmerge_ok in Hc as (s1 & s2 & H1 & H2 & Hc). cbn beta in H2. injection Hc as <-. cbn [shape_vars_lt]. rewrite Hv, (IH _ k1 _ s1 H1), (IH _ k2 _ s2 H2). reflexivity.
  - destruct (AP.erange_any (kn cs) ce) as [[lo hi]|]; [|discriminate].
    destruct (Z.leb lo cmid && Z.ltb cmid hi)%bool.
    2: { cbn [negb] in Hc. destruct (Z.leb hi cmid); [exact (IH _ ck1 _ s Hc) | exact (IH _ ck2 _ s Hc)]. }
    cbn [negb] in Hc. cbv zeta in Hc.
    destruct (kn_contra (kn (set_kn cs (KRange ce lo cmid :: kn cs)))); [exact (IH _ ck2 _ s Hc)|].
    destruct (kn_contra (kn (set_kn cs (KRange ce (cmid + 1) hi :: kn cs)))); [exact (IH _ ck1 _ s Hc)|].
    apply cmerge_ok in Hc as (s1 & s2 & H1 & H2 & Hc). cbn beta in H2.
    match type of Hc with (if ?c then _ else _) = _ => destruct c; [|discriminate] end. injection Hc as <-. exact (IH _ ck1 _ s1 H1).   (* [comment removed for export] *)
  - destruct (node_casedisj A cs db1 db2) as [[csa csb]|]; [|discriminate].
    apply cmerge_ok in Hc as (s1 & s2 & H1 & H2 & Hc). cbn beta in H2.
    match type of Hc with (if ?c then _ else _) = _ => destruct c; [|discriminate] end. injection Hc as <-. exact (IH _ dk1 _ s1 H1).   (* [comment removed for export] *)
  - destruct (node_shdisj A cs sb1 sn1 sb2 sn2) as [cs1|]; [|discriminate]. exact (IH _ k _ s Hc).
  - destruct (kn_contra (kn cs)); [|discriminate]. injection Hc as <-. reflexivity.
  - destruct (fact_ok (kn cs) K || AP.fact_okL (kn cs) K)%bool; [|discriminate]. exact (IH _ k _ s Hc).
  - apply GW in Hc.
    destruct (node_join SEGS cs jb joff jn) as [cs1|]; [|discriminate]. exact (IH _ k _ s Hc).
  - exact (IH _ k _ s Hc).
  - exact (IH _ k _ s Hc).
  - exact (IH _ k _ s Hc).
  - destruct (node_bump cs bm) as [cs1|]; [|discriminate]. exact (IH _ k _ s Hc).
  - destruct (node_havoc nx0 cs hrs) as [cs1|]; [|discriminate]. exact (IH _ k _ s Hc).
  - destruct (node_havocbig nx0 cs hbK) as [cs1|]; [|discriminate]. exact (IH _ k _ s Hc).
  - apply GW in Hc.
    destruct (node_fresh nx0 cs r logc fb) as [cs1|]; [|discriminate]. exact (IH _ k _ s Hc).
  - apply GWn in Hc. apply GWa in Hc.
    destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_sys A nx0 y cs) as [cs1|]; [|discriminate]. exact (IH _ k _ s Hc).
  - apply GW in Hc.
    destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mmap A nx0 LIMIT cs) as [cs1|]; [|discriminate]. exact (IH _ ma _ s Hc).
  - apply GW in Hc.
    destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mmapin A LIMIT cs) as [cs1|]; [|discriminate]. exact (IH _ ib _ s Hc).
  - apply GW in Hc.
    destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mprotect A LIMIT cs) as [cs1|]; [|discriminate]. exact (IH _ qb _ s Hc).
  - apply GW in Hc.
    discriminate Hc.   (* [comment removed for export] *)
  - apply GWn in Hc.
    destruct (node_x SEGS A nx0 x args cs) as [cs1|]; [|discriminate]. exact (IH _ k _ s Hc).
  - apply GWn in Hc.
    destruct (xp_extG xp xid); [destruct (AP.wbb xp); [discriminate|]|];
    (destruct (XN xid xargs cs) as [cs1|]; [|discriminate]; exact (IH _ k _ s Hc)).
  - apply GWn in Hc.
    destruct (XE eid eargs cs) as [[[fd ps] cs1]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc (AP.gsuccW xp (xp_xews xp eid eargs cs) cs cs1) k) as [s1| |] eqn:H1; [|discriminate|discriminate].
    injection Hc as <-. cbn [shape_vars_lt]. exact (IH _ k _ s1 H1).
  - apply GW in Hc.
    destruct (XB bid bargs cs) as [[csa csb]|]; [|discriminate].
    apply cmerge_ok in Hc as (sa & sb & H1 & H2 & Hc). cbn beta in H2.
    injection Hc as <-. cbn [shape_vars_lt]. rewrite (IH _ kb1 _ sa H1), (IH _ kb2 _ sb H2). reflexivity.
  - apply GW in Hc.
    destruct (a_props linv) eqn:Hpl; [|discriminate]. cbn [negb] in Hc.
    destruct (loop_ok nx0 cs lJ lN linv) as [nhi|]; [|discriminate].
    destruct (Z.eqb (pc linv) (pc cs) && entails_h A (Datatypes.S lJ) (nxt linv) cs (inst linv lJ (ELit 0)))%bool; [|discriminate].
    destruct (CHECK bfuel fuel (Some (LC (pc cs) (inst linv lJ (eaddz (EVar lJ) 1)) (Datatypes.S lJ) (nxt linv))) (loop_body_state lJ lN nhi linv) lbody) as [sb| |]; [|discriminate|discriminate].
    destruct sb; try discriminate. exact (IH _ lk _ s Hc).
  - destruct lc as [[h nx lo hi|j' js' sk' b' lo'|[|wT whs] wcur lo hi wV wxs wxts|so shi]|]; [|discriminate| discriminate | |discriminate|discriminate].
    + destruct (Z.eqb (pc cs) h && entails_h A lo hi cs nx)%bool; [|discriminate]. injection Hc as <-. reflexivity.
    + (* [comment removed for export] *)
      destruct (if Z.eqb (pc cs) (pc wT) then entails_s A lo (nxt wT) [] cs wT else None) as [sg|]; [|discriminate].
      destruct (variant_ok (kn cs) sg wV wcur 0 && shape_vars_lt nx0 wxs)%bool eqn:Hv; [|discriminate].
      apply with_props_ok in Hc as [_ Hc]. injection Hc as <-. apply andb_prop in Hv as [_ Hv]. exact Hv.
  - apply GW in Hc.
    destruct (HS h) as [ch|]; [|destruct (Nat.leb 1000 h); discriminate]. destruct (entails cs ch); [|discriminate].
    apply with_props_ok in Hc as [_ Hc]. injection Hc as <-. reflexivity.
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_exit cs); [|discriminate]. injection Hc as <-. reflexivity.
  - destruct (node_spin SEGS cs); [|discriminate]. injection Hc as <-. reflexivity.
  - apply GW in Hc. destruct (node_fog cs fi fsz) as [cs1|]; [|discriminate]. exact (IH _ fk _ s Hc).
  - apply GW in Hc. destruct (node_fognew cs gi gsz) as [cs1|]; [|discriminate]. exact (IH _ gk _ s Hc).
  - apply GW in Hc.
    destruct (node_ghost LIMIT cs gb gn) as [cs1|]; [|discriminate]. exact (IH _ gk2 _ s Hc).
  - apply GW in Hc.
    destruct (node_unvis A cs ub un) as [cs1|]; [|discriminate]. exact (IH _ uk _ s Hc).
  - destruct (node_havocbrk nx0 cs hlo hhi) as [cs1|]; [|discriminate]. exact (IH _ hk _ s Hc).
  - destruct (node_intro nx0 cs ilo ihi) as [cs1|]; [|discriminate]. exact (IH _ ik _ s Hc).
  - apply GW in Hc.
    destruct (branch_probe IT cs) as [e|]; [|discriminate].
    destruct (erange (kn cs) e) as [[lo hi]|]; [|discriminate].
    destruct (Z.ltb hi 1 || Z.ltb 0 lo)%bool.
    { destruct (run_block_gc_wb_ws SEGS IT _ (AP.WB xp) KC bfuel (djp :: STOPS A) cs) as [[cs1 W1]|]; [|discriminate].
      destruct (Z.eqb (pc cs1) djp); [|discriminate]. exact (IH _ dk _ s Hc). }
    cbv zeta in Hc.
    destruct (run_block_gc_wb_ws SEGS IT _ (AP.WB xp) KC bfuel (djp :: STOPS A) (set_kn cs (KRange e lo 0 :: kn cs))) as [[ca Wa]|]; [|discriminate].
    destruct (run_block_gc_wb_ws SEGS IT _ (AP.WB xp) KC bfuel (djp :: STOPS A) (set_kn cs (KRange e 1 hi :: kn cs))) as [[cb Wb]|]; [|discriminate].
    destruct (node_diamond_join A nx0 (nxt cs) djp drs ca cb) as [csj|]; [|discriminate]. exact (IH _ dk _ s Hc).
  - apply GW in Hc. destruct (node_rename _ cs rnm) as [cs1|]; [|discriminate]. exact (IH _ rnk _ s Hc).
  - apply GW in Hc. destruct (node_compact _ cs) as [cs1|]; [|discriminate]. exact (IH _ cpk _ s Hc).
  - apply GW in Hc.
    destruct (via_ok nx0 cs vjs vlo && forallb (gvars_lt (nxt cs)) (a_props vjs))%bool; [|discriminate].
    destruct (CHECK bfuel fuel lc vjs vk) as [sk| |]; [|discriminate|discriminate]. exact (IH _ vka _ s Hc).
  - destruct lc as [[h nx lo hi|j' js' sk' b' lo'|whs' wcur' wlo' whi' wV' wxs' wxts'|so shi]|]; [discriminate| |discriminate|discriminate|discriminate].
    destruct (Nat.eqb mj j' && Z.eqb (pc cs) (pc js') && shape_vars_lt nx0 sk' && entails_h A lo' (nxt js') cs js')%bool eqn:Ht.
    + apply with_props_ok in Hc as [_ Hc]. injection Hc as <-. apply andb_prop in Ht as [Ht _]. apply andb_prop in Ht as [_ Hsv]. exact Hsv.
    + (* [comment removed for export] *)
      destruct (Nat.eqb mj j' && Z.eqb (pc cs) (pc js') && shape_vars_lt nx0 sk' && match s_log (a_ss js') with [] => true | _ => false end)%bool eqn:Ht2; [|discriminate].
      destruct (entails_s A lo' (nxt js') [] cs js') as [sg|]; [|discriminate].
      apply with_props_ok in Hc as [_ Hc]. injection Hc as <-. apply andb_prop in Ht2 as [Ht2 _]. apply andb_prop in Ht2 as [_ Hsv]. exact Hsv.
  - destruct (node_abstractcell A cs ab an) as [cs1|]; [|discriminate]. exact (IH _ ak _ s Hc).
  - destruct (node_havocwords nx0 cs hws) as [cs1|]; [|discriminate]. exact (IH _ hwk _ s Hc).
  - destruct (node_respell cs rsr rse) as [cs1|]; [|discriminate]. exact (IH _ rsk _ s Hc).
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    revert Hc. generalize (AP.normT xp cs wexits) as wexits'. generalize (AP.normT xp cs wheads) as wheads'.
    intros wheads' wexits' Hc. rename wheads into wheads0. rename wexits into wexits0. rename wheads' into wheads. rename wexits' into wexits.
    destruct wheads as [|[T0 b0] hrest]; [discriminate|].
    destruct (while_okN nx0 cs wlo (map fst ((T0, b0) :: hrest)) wV wxs && Z.eqb (pc cs) (pc T0))%bool eqn:Hw; [|discriminate].
    destruct (entails_s A wlo (nxt T0) [] cs T0) as [sg0|]; [|discriminate].
    destruct (needs_props xp cs (map (ginst sg0) (a_props T0))); [|discriminate].
    destruct (chk_exits nx0 (CHECK bfuel fuel lc) wlo wxs wexits) as [xts|e] eqn:Hxts; [|exfalso; exact (chk_exits_err _ _ _ _ _ Hxts _ Hc)].
    destruct (chk_heads (CHECK bfuel fuel) (map fst ((T0, b0) :: hrest)) 0 wlo wV wxs xts ((T0, b0) :: hrest)) as [s'| |] eqn:Hh; [|discriminate|discriminate].
    injection Hc as <-. destruct (chk_heads_ok _ _ _ _ _ _ _ _ _ Hh) as [-> _].
    apply andb_prop in Hw as [Hw _]. destruct (while_okN_facts cs wlo _ wV wxs Hw) as (_ & _ & _ & _ & Hsv). exact Hsv.
  - (* [comment removed for export] *)
    destruct lc as [[h nx lo hi|j' js' sk' b' lo'|whs wcur lo hi wV wxs wxts|so shi]|]; [discriminate|discriminate| |discriminate|discriminate].
    destruct (nth_error whs nh) as [wT|]; [|discriminate].
    destruct (if Z.eqb (pc cs) (pc wT) then entails_s A lo (nxt wT) nwh cs wT else None) as [sg|]; [|discriminate].
    destruct (variant_ok (kn cs) sg wV wcur nh && shape_vars_lt nx0 wxs)%bool eqn:Hv; [|discriminate].
    apply with_props_ok in Hc as [_ Hc]. injection Hc as <-. apply andb_prop in Hv as [_ Hv]. exact Hv.
  - (* [comment removed for export] *)
    destruct lc as [[h nx lo hi|j' js' sk' b' lo'|whs wcur lo hi wV wxs wxts|so shi]|]; [discriminate|discriminate| | |discriminate].
    + destruct (nth_error wxts bi) as [[x sx]|]; [|discriminate].
      destruct (entails_s A lo (nxt x) bh cs x); [|discriminate].
      destruct (shape_vars_lt nx0 sx) eqn:Hv; [|discriminate]. apply with_props_ok in Hc as [_ Hc]. injection Hc as <-. exact Hv.
    + (* [comment removed for export] *)
      destruct (nth_error so bi) as [x|]; [|discriminate].
      destruct (entails_s A shi (nxt x) bh cs x); [|discriminate]. injection Hc as <-. reflexivity.
  - (* [comment removed for export] *)
    destruct (xp_sg xp usid) as [SD0|]; [|discriminate].
    destruct (AP.segdef_wf nx0 SD0) eqn:Hwf; [|discriminate]. cbn [negb] in Hc.
    destruct (AP.use_view cs SD0) as [[SD skh]|] eqn:Huv; [|discriminate].   (* [comment removed for export] *)
    match type of Hc with (if ?b then _ else _) = _ => destruct b; [discriminate|] end.
    assert (Hshv : sg_shape SD = sg_shape SD0).
    { unfold AP.use_view in Huv. destruct (AP.skel_free SD0); [destruct (AP.reskel _ _ _ _) as [[L sk]|]; [|discriminate Huv]|]; injection Huv as <- _; reflexivity. }
    destruct (entails_s A _ _ _ cs _) as [sg|]; [|discriminate].
    match type of Hc with (if negb ?b then _ else _) = _ => destruct b; [|discriminate] end. cbn [negb] in Hc.
    match type of Hc with (if negb ?b then _ else _) = _ => destruct b; [|discriminate] end. cbn [negb] in Hc.   (* [comment removed for export] *)
    destruct (AP.use_all _ _ _ _ (sg_outs SD) uks) as [ss|r] eqn:Hua.
    + destruct (forallb _ ss); [|discriminate]. injection Hc as <-. rewrite Hshv. destruct (segdef_wf_facts SD0 Hwf) as (_ & _ & _ & _ & _ & _ & Wsh & _ & _).
      apply splice_vars; [exact Wsh|]. apply Forall_forall. intros s0 Hs0.
      apply In_nth_error in Hs0 as [i Hi]. destruct (use_all_ok _ _ _ _ _ _ _ Hua) as [Hlen Hall].
      destruct (nth_error (sg_outs SD) i) as [x|] eqn:Hx.
      * destruct (Hall i x Hx) as (k & s1 & Hk & Hs1 & Hck). rewrite Hi in Hs1. injection Hs1 as ->. exact (IH _ k _ s1 Hck).
      * exfalso. apply nth_error_None in Hx. assert (Hi' : nth_error ss i <> None) by (rewrite Hi; discriminate). apply nth_error_Some in Hi'. lia.
    + exfalso. exact (use_all_err _ _ _ _ _ _ _ _ Hua Hc).
  - (* [comment removed for export] *)
    destruct (gvars_lt (nxt cs) gg); [|discriminate]. destruct (need1 xp cs (VCAtom gg)); [|match type of Hc with (match ?r with _ => _ end = _) => destruct r; discriminate end]. exact (IH _ gk _ s Hc).
  - (* [comment removed for export] *) exact (IH _ gdk _ s Hc).
  - (* [comment removed for export] *)
    destruct (kentry_vars_lt (nxt cs) gK); [|discriminate]. destruct (need1 xp cs (VCFact gK)); [|match type of Hc with (match ?r with _ => _ end = _) => destruct r; discriminate end]. exact (IH _ gfk _ s Hc).
  - (* [comment removed for export] *)
    destruct (tfact_inst lc cs gtx gti gtK) as [gK|]; [|discriminate].
    destruct (kentry_vars_lt (nxt cs) gK); [|discriminate]. destruct (need1 xp cs (VCFact gK)); [|match type of Hc with (match ?r with _ => _ end = _) => destruct r; discriminate end]. exact (IH _ gtfk _ s Hc).
  - (* [comment removed for export] *)
    apply GW in Hc.
    destruct (HS sh) as [ch|]; [|discriminate].
    destruct (Nat.leb nx0 slo && match s_log (a_ss ch) with [] => true | _ => false end)%bool; [|discriminate].
    destruct (entails_s A slo (nxt ch) shints cs ch); [|discriminate].
    apply with_props_ok in Hc as [_ Hc]. injection Hc as <-. reflexivity.
  - (* [comment removed for export] *)
    apply GW in Hc.
    destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_brk2 A LIMIT cs) as [[csg csf]|]; [|discriminate].
    apply cmerge_ok in Hc as (s1 & s2 & H1 & H2 & Hc). cbn beta in H2.
    match type of Hc with (if ?c then _ else _) = _ => destruct c; [|discriminate] end. injection Hc as <-. exact (IH _ kga _ s1 H1).
  - (* [comment removed for export] *)
    apply GW in Hc.
    destruct (node_casedisjJ A cs jjb1 jjb2) as [[csl [csb|]]|]; [| |discriminate].
    + destruct (run_block_gc_wb_ws SEGS IT _ (AP.WB xp) KC bfuel (jjp :: STOPS A) csl) as [[ca Wa]|]; [|discriminate].
      destruct (run_block_gc_wb_ws SEGS IT _ (AP.WB xp) KC bfuel (jjp :: STOPS A) csb) as [[cb Wb]|]; [|discriminate].
      destruct (node_diamond_join A nx0 (nxt cs) jjp jrs ca cb) as [csj|]; [|discriminate]. exact (IH _ jk _ s Hc).
    + destruct (run_block_gc_wb_ws SEGS IT _ (AP.WB xp) KC bfuel (jjp :: STOPS A) csl) as [[cs1 W1]|]; [|discriminate].
      destruct (Z.eqb (pc cs1) jjp); [|discriminate]. exact (IH _ jk _ s Hc).
Qed.

(* [comment removed for export] *)
Definition reledger_lc (L : ledger) (lc : option loopctx) : option loopctx :=
  match lc with
  | Some (LC p0 inv lo hi) => Some (LC p0 (with_ledger L inv) lo hi)
  | Some (JC j js sk b lo) => Some (JC j (with_ledger L js) sk b lo)
  | Some (WC hs cur lo hi V xs xts) =>
      Some (WC (map (with_ledger L) hs) cur lo hi V xs (map (fun xq => (with_ledger L (fst xq), snd xq)) xts))
  | Some (SC outs hi) => Some (SC (map (with_ledger L) outs) hi)
  | None => None
  end.
Definition lcb (lc : option loopctx) : nat := match lc with Some c => lc_bnd c | None => nx0 end.
Lemma lcb_reledger : forall L lc, lcb (reledger_lc L lc) = lcb lc.
Proof. intros L [[p0 inv lo hi|j js sk b lo|hs cur lo hi V xs xts|outs hi]|]; reflexivity. Qed.
Definition lens_le (L M : ledger) : Prop :=
  (length (lg_maps L) <= length (lg_maps M))%nat /\ (length (lg_vis L) <= length (lg_vis M))%nat
  /\ (length (lg_ghost L) <= length (lg_ghost M))%nat.
(* [comment removed for export] *)
Lemma if_cerr : forall (b : bool) (r : cres) c q x y s, (if b then r else CErr c q x) = COk s -> (if b then r else CErr c q y) = COk s.
Proof. intros [] r c q x y s H; [exact H | discriminate H]. Qed.
Lemma lmap_ledger : forall (f : acs -> option acs) cs cs',
  (forall L, f (with_ledger L cs) = APL.lmap L (f cs)) -> f cs = Some cs' -> ledger_of cs' = ledger_of cs.
Proof.
  intros f cs cs' Hf H. specialize (Hf (ledger_of cs)). rewrite with_ledger_of, H in Hf. cbn [APL.lmap] in Hf.
  apply APL.some_inj in Hf. rewrite Hf at 1. apply ledger_of_with.
Qed.
Lemma limp_ledger : forall (f : acs -> option acs) cs cs',
  (forall L, ledger_vars_lt (nxt cs) L = true -> f cs = Some cs' -> f (with_ledger L cs) = Some (with_ledger L cs')) ->
  ledger_vars_lt (nxt cs) (ledger_of cs) = true -> f cs = Some cs' -> ledger_of cs' = ledger_of cs.
Proof.
  intros f cs cs' Hf HC H. specialize (Hf (ledger_of cs) HC H). rewrite with_ledger_of, H in Hf.
  apply APL.some_inj in Hf. rewrite Hf at 1. apply ledger_of_with.
Qed.
Lemma ledger_of_set_props : forall cs l, ledger_of (set_props cs l) = ledger_of cs.   Proof. reflexivity. Qed.
Lemma ledger_of_set_kn : forall cs k, ledger_of (set_kn cs k) = ledger_of cs.        Proof. reflexivity. Qed.
Lemma ledger_of_gkeep : forall G W cs cs', ledger_of (gkeep G W cs cs') = ledger_of cs'.   Proof. reflexivity. Qed.
Lemma ledger_of_gkeepE : forall G W cs cs', ledger_of (AP.gkeepE G W cs cs') = ledger_of cs'.   Proof. reflexivity. Qed.
Lemma ledger_of_gpures : forall G cs cs', ledger_of (gpures G cs cs') = ledger_of cs'.   Proof. reflexivity. Qed.
Lemma ledger_of_gsuccW : forall ows cs cs', ledger_of (AP.gsuccW xp ows cs cs') = ledger_of cs'.
Proof. intros. unfold AP.gsuccW. destruct ows; [rewrite AP.gkeepEM_eq|]; reflexivity. Qed.
Lemma gsuccW_reL : forall ows L cs cs', AP.gsuccW xp ows (with_ledger L cs) (with_ledger L cs') = with_ledger L (AP.gsuccW xp ows cs cs').
Proof. intros. unfold AP.gsuccW. destruct ows; [apply APL.gkeepEM_reL | apply APL.gpures_reL]. Qed.
Lemma okW_reL : forall ows L cs, AP.okW xp ows (with_ledger L cs) = AP.okW xp ows cs.   Proof. reflexivity. Qed.
Lemma needs_props_reL : forall L cs gs, AP.needs_props xp (with_ledger L cs) gs = AP.needs_props xp cs gs.   Proof. reflexivity. Qed.
Lemma with_props_reL : forall L cs gs r, AP.with_props xp (with_ledger L cs) gs r = AP.with_props xp cs gs r.   Proof. reflexivity. Qed.
Lemma need1_reL : forall L cs c, AP.need1 xp (with_ledger L cs) c = AP.need1 xp cs c.   Proof. reflexivity. Qed.
Lemma template_ok_reL : forall lo x L, template_ok nx0 lo x = true -> ledger_vars_lt (nxt x) L = true -> template_ok nx0 lo (with_ledger L x) = true.
Proof.
  intros lo x L H HL. unfold template_ok in *. repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  change (a_ss (with_ledger L x)) with (a_ss x). change (nxt (with_ledger L x)) with (nxt x).
  rewrite (APL.fresh_ok_reL nx0 L x H HL), X1, X0, X. destruct (s_log (a_ss x)); [|discriminate X2]. reflexivity.
Qed.
Lemma template_ok_nxt : forall lo x, template_ok nx0 lo x = true -> (lo <= nxt x)%nat.
Proof.
  intros lo x H. unfold template_ok in H. repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Nat.leb_le in X. exact X.
Qed.
Lemma head_ok_reL : forall lo V T L, head_ok nx0 lo V T = true -> ledger_vars_lt lo L = true -> head_ok nx0 lo V (with_ledger L T) = true.
Proof.
  intros lo V T L H HL. unfold head_ok in *. apply andb_prop in H as [H1 H2]. change (nxt (with_ledger L T)) with (nxt T).
  rewrite (template_ok_reL lo T L H1 (APL.APS_ledger_mono _ _ _ HL (template_ok_nxt _ _ H1))), H2. reflexivity.
Qed.
Lemma while_okN_reL : forall cs lo hs V xs L, ledger_vars_lt lo L = true ->
  while_okN nx0 cs lo hs V xs = true -> while_okN nx0 (with_ledger L cs) lo (map (with_ledger L) hs) V xs = true.
Proof.
  intros cs lo hs V xs L HL H. unfold while_okN in *. repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  change (nxt (with_ledger L cs)) with (nxt cs). rewrite H, X2, X0, X.
  replace (forallb (head_ok nx0 lo V) (map (with_ledger L) hs)) with true; [reflexivity|]. symmetry.
  apply forallb_forall. intros T' HT'. apply in_map_iff in HT' as (T & <- & HT). apply head_ok_reL; [|exact HL].
  exact (proj1 (forallb_forall _ _) X1 T HT).
Qed.
Lemma chk_exits_reL : forall (chk chk' : acs -> plan -> cres) lo xs L l xts,
  (forall x kx sx, In (x, kx) l -> template_ok nx0 lo x = true -> chk x kx = COk sx -> chk' (with_ledger L x) kx = COk sx) ->
  ledger_vars_lt lo L = true ->
  chk_exits nx0 chk lo xs l = XOk xts ->
  chk_exits nx0 chk' lo xs (map (fun xq => (with_ledger L (fst xq), snd xq)) l) = XOk (map (fun xq => (with_ledger L (fst xq), snd xq)) xts).
Proof.
  intros chk chk' lo xs L l. induction l as [|[x kx] rest IH]; intros xts Hk HL H; cbn [chk_exits map fst snd] in *.
  - injection H as <-. reflexivity.
  - destruct (template_ok nx0 lo x) eqn:Ht; [|discriminate H].
    destruct (chk x kx) as [sx| |] eqn:Hc; [|discriminate H|discriminate H].
    rewrite (template_ok_reL lo x L Ht (APL.APS_ledger_mono _ _ _ HL (template_ok_nxt _ _ Ht))).
    rewrite (Hk x kx sx (or_introl eq_refl) Ht Hc).
    destruct (no_next sx || is_snext xs)%bool; [|discriminate H].
    destruct (chk_exits nx0 chk lo xs rest) as [r|] eqn:Hr; [|discriminate H]. injection H as <-.
    rewrite (IH r (fun x0 kx0 sx0 Hin => Hk x0 kx0 sx0 (or_intror Hin)) HL eq_refl). reflexivity.
Qed.
Lemma chk_heads_reL : forall (chk chk' : option loopctx -> acs -> plan -> cres) hs lo V xs xts L l cur s,
  (forall i T b, nth_error l i = Some (T, b) -> chk (Some (WC hs (cur + i) lo (nxt T) V xs xts)) T b = COk xs ->
      chk' (Some (WC (map (with_ledger L) hs) (cur + i) lo (nxt T) V xs (map (fun xq => (with_ledger L (fst xq), snd xq)) xts))) (with_ledger L T) b = COk xs) ->
  chk_heads chk hs cur lo V xs xts l = COk s ->
  chk_heads chk' (map (with_ledger L) hs) cur lo V xs (map (fun xq => (with_ledger L (fst xq), snd xq)) xts)
            (map (fun hp => (with_ledger L (fst hp), snd hp)) l) = COk s.
Proof.
  intros chk chk' hs lo V xs xts L l. induction l as [|[T b] rest IH]; intros cur s Hk H; cbn [chk_heads map fst snd] in *.
  - exact H.
  - destruct (chk (Some (WC hs cur lo (nxt T) V xs xts)) T b) as [sb| |] eqn:Hb; [|discriminate H|destruct (chk_heads chk hs (Datatypes.S cur) lo V xs xts rest); discriminate H].
    destruct (shape_eqb sb xs) eqn:He; [|discriminate H]. pose proof (shape_eqb_eq _ _ He) as E. subst sb.
    pose proof (Hk 0%nat T b eq_refl) as Hk0. rewrite Nat.add_0_r in Hk0. change (nxt (with_ledger L T)) with (nxt T).
    rewrite (Hk0 Hb), He.
    apply IH; [|exact H]. intros i T' b' Hi. pose proof (Hk (Datatypes.S i) T' b' Hi) as Q. rewrite <- Nat.add_succ_comm in Q. exact Q.
Qed.

(* [comment removed for export] *)
Hypothesis sysws_reL : forall y cs L, xp_sysws xp y (with_ledger L cs) = xp_sysws xp y cs.
Hypothesis xnws_reL : forall id args cs L, xp_xnws xp id args (with_ledger L cs) = xp_xnws xp id args cs.
Hypothesis xews_reL : forall id args cs L, xp_xews xp id args (with_ledger L cs) = xp_xews xp id args cs.
Hypothesis xws_reL : forall x args cs L, xp_xws xp x args (with_ledger L cs) = xp_xws xp x args cs.
Hypothesis XN_reL : forall id args cs cs' L, AP.ext_okW xp id args cs = true -> ledger_vars_lt (nxt cs) L = true ->
  XN id args cs = Some cs' -> XN id args (with_ledger L cs) = Some (with_ledger L cs').
Hypothesis XE_reL : forall id args cs fd ps cs' L, AP.emit_okW xp id args cs = true -> ledger_vars_lt (nxt cs) L = true ->
  XE id args cs = Some (fd, ps, cs') -> XE id args (with_ledger L cs) = Some (fd, ps, with_ledger L cs').

(* [comment removed for export] *)
Definition lcok (b0 : nat) (lc : option loopctx) : Prop :=
  match lc with
  | Some (WC _ _ lo hi _ _ _) => (b0 <= lo)%nat /\ (b0 <= hi)%nat
  | Some (SC _ hi) => (b0 <= hi)%nat
  | _ => False
  end.
Lemma lcok_lcb : forall b0 lc, lcok b0 lc -> (b0 <= lcb lc)%nat.
Proof. intros b0 [[? ? ? ?|? ? ? ? ?|? ? lo hi ? ? ?|? hi]|] H; cbn [lcok lcb lc_bnd] in *; try contradiction; lia. Qed.
Lemma check_reledger : forall bfuel fuel lc p cs s L b0,
  AP.wbb xp = true ->
  APL.ledger_evars L = true -> ledger_vars_lt b0 L = true -> ledger_vars_lt b0 (ledger_of cs) = true ->
  lens_le L (ledger_of cs) -> lcok b0 lc ->
  CHECK bfuel fuel lc cs p = COk s -> CHECK bfuel fuel (reledger_lc L lc) (with_ledger L cs) p = COk s.
Proof.
  intros bfuel fuel. induction fuel as [|fuel IH]; intros lc p cs s L b0 Hw HeL HLL0 HLC0 Hlen Hlc Hc; [discriminate|].
  pose proof (lcok_lcb b0 lc Hlc) as Hb0.
  assert (HLL : ledger_vars_lt (lcb lc) L = true) by exact (APL.APS_ledger_mono _ _ _ HLL0 Hb0).
  assert (HLC : ledger_vars_lt (lcb lc) (ledger_of cs) = true) by exact (APL.APS_ledger_mono _ _ _ HLC0 Hb0).
  cbn [AP.check] in Hc |- *.
  rewrite ?AP.gkeepM_eq, ?AP.gkeepEM_eq, ?AP.gkeepPM_eq, ?AP.node_diamond_joinM_eq, ?AP.entails_hM_eq, ?AP.entails_sM_eq, ?AP.use_exitN_eqf, ?AP.instsN_eqf, ?AP.drop_ixsF_eqf in Hc |- *.
  (* [comment removed for export] *)
  assert (Eg : match reledger_lc L lc with Some c => Nat.leb (lc_bnd c) (nxt (with_ledger L cs)) | None => true end
               = match lc with Some c => Nat.leb (lc_bnd c) (nxt cs) | None => true end)
    by (destruct lc as [[? ? ? ?|? ? ? ? ?|? ? ? ? ? ? ?|? ?]|]; reflexivity).
  rewrite Eg. clear Eg.
  match type of Hc with (if ?g then _ else _) = _ => destruct g eqn:Hg; [discriminate|] end. cbn [negb] in Hc |- *.
  assert (Hbn : (lcb lc <= nxt cs)%nat).
  { destruct lc as [c|]; cbn [lcb]; [apply Bool.negb_false_iff in Hg; apply Nat.leb_le in Hg; exact Hg|]. cbn [lcok] in Hlc. contradiction. }
  assert (Egcb : match reledger_lc L lc with Some c => lc_bnd c | None => nx0 end = lcb lc)
    by (destruct lc as [[? ? ? ?|? ? ? ? ?|? ? ? ? ? ? ?|? ?]|]; reflexivity).
  rewrite Egcb. change (match lc with Some c => lc_bnd c | None => nx0 end) with (lcb lc) in Hc.
  assert (HLn : ledger_vars_lt (nxt cs) L = true) by exact (APL.APS_ledger_mono _ _ _ HLL Hbn).
  assert (HCn : ledger_vars_lt (nxt cs) (ledger_of cs) = true) by exact (APL.APS_ledger_mono _ _ _ HLC Hbn).
  (* [comment removed for export] *)
  assert (RW : forall r : cres, (if AP.wbb xp then CErr 11 p cs else r) = COk s -> False) by (intros r Hr; rewrite Hw in Hr; discriminate Hr).
  rewrite Hw. rewrite Hw in Hc.
  (* [comment removed for export] *)
  assert (NEXT : forall lc' cs1 k s1, CHECK bfuel fuel lc' cs1 k = COk s1 -> ledger_of cs1 = ledger_of cs -> lcok b0 lc' ->
            CHECK bfuel fuel (reledger_lc L lc') (with_ledger L cs1) k = COk s1).
  { intros lc' cs1 k s1 H1 E1 E2. apply (IH lc' k cs1 s1 L b0 Hw HeL HLL0); [rewrite E1; exact HLC0 | rewrite E1; exact Hlen | exact E2 | exact H1]. }
  destruct p as [stops k|e mid k1 k2|ce cmid ck1 ck2|db1 db2 dk1 dk2|sb1 sn1 sb2 sn2 k| |K k|jb joff jn k|ixs k|db dn k|gws k|bm k|hrs k|hbK k|r logc fb k|y k|ma|ib|qb|ka|x args k|xid xargs k|eid eargs k|bid bargs kb1 kb2|lJ lN linv lbody lk| |h| | |fi fsz fk|gi gsz gk|gb gn gk2|ub un uk|hlo hhi hk|ilo ihi ik|djp drs dk|rnm rnk|cpk|vj vjs vlo vka vk|mj|ab an ak|hws hwk|rsr rse rsk|wlo wheads wV wxs wexits|nh nwh|bi bh|usid uhints uks|gg gk|gi gdk|gK gfk|gtx gti gtK gtfk|sh slo shints|kga kgf|jjb1 jjb2 jjp jrs jk].
  - (* [comment removed for export] *)
    destruct (run_block_gc_wb_ws SEGS IT (lcb lc) (AP.WB xp) KC bfuel (stops ++ STOPS A) cs) as [[cs1 W]|] eqn:Hrb; [|discriminate].
    rewrite (APL.run_block_gc_wb_ws_reL SEGS IT (lcb lc) _ _ _ _ L cs cs1 W HLL HLC Hrb).
    assert (E1 : ledger_of cs1 = ledger_of cs).
    { pose proof (APL.run_block_gc_wb_ws_reL SEGS IT (lcb lc) _ _ _ _ (ledger_of cs) cs cs1 W HLC HLC Hrb) as Q.
      rewrite with_ledger_of, Hrb in Q. apply APL.some_inj in Q. apply (f_equal fst) in Q. cbn [fst] in Q. rewrite Q at 1. apply ledger_of_with. }
    change (pc (with_ledger L cs1)) with (pc cs1). change (pc (with_ledger L cs)) with (pc cs).
    unfold AP.rerun_block in *. change (pc (with_ledger L cs1)) with (pc cs1). change (pc (with_ledger L cs)) with (pc cs).
    rewrite APL.gkeep_reL.
    lazymatch type of Hc with (if ?c then _ else _) = _ => destruct c end.
    + exact (NEXT lc _ (PRun stops k) s Hc (eq_trans (ledger_of_gkeep _ _ _ _) E1) Hlc).
    + exact (NEXT lc _ k s Hc (eq_trans (ledger_of_gkeep _ _ _ _) E1) Hlc).
  - (* [comment removed for export] *)
    destruct (AP.expr_vars_lt nx0 e) eqn:Hv; [|discriminate].
    change (kn (with_ledger L cs)) with (kn cs).
    destruct (erange (kn cs) e) as [[lo hi]|]; [|discriminate].
    destruct (Z.leb lo mid && Z.ltb mid hi)%bool.
    2: { destruct (Z.leb hi mid); [exact (NEXT lc _ k1 s Hc eq_refl Hlc) | exact (NEXT lc _ k2 s Hc eq_refl Hlc)]. }
    apply cmerge_ok in Hc as (s1 & s2 & H1 & H2 & Hc). cbn beta in H2.
    rewrite !APL.set_kn_reL. unfold cmerge.
    rewrite (NEXT lc _ k1 s1 H1 eq_refl Hlc). cbn beta. rewrite (NEXT lc _ k2 s2 H2 eq_refl Hlc). exact Hc.
  - (* [comment removed for export] *)
    change (kn (with_ledger L cs)) with (kn cs).
    destruct (AP.erange_any (kn cs) ce) as [[lo hi]|]; [|discriminate].
    destruct (Z.leb lo cmid && Z.ltb cmid hi)%bool.
    2: { cbn [negb] in Hc |- *. destruct (Z.leb hi cmid); [exact (NEXT lc _ ck1 s Hc eq_refl Hlc) | exact (NEXT lc _ ck2 s Hc eq_refl Hlc)]. }
    cbn [negb] in Hc |- *. cbv zeta in Hc. cbv zeta. rewrite !APL.set_kn_reL.
    change (kn (with_ledger L (set_kn cs (KRange ce lo cmid :: kn cs)))) with (kn (set_kn cs (KRange ce lo cmid :: kn cs))).
    change (kn (with_ledger L (set_kn cs (KRange ce (cmid + 1) hi :: kn cs)))) with (kn (set_kn cs (KRange ce (cmid + 1) hi :: kn cs))).
    destruct (kn_contra (kn (set_kn cs (KRange ce lo cmid :: kn cs)))); [exact (NEXT lc _ ck2 s Hc eq_refl Hlc)|].
    destruct (kn_contra (kn (set_kn cs (KRange ce (cmid + 1) hi :: kn cs)))); [exact (NEXT lc _ ck1 s Hc eq_refl Hlc)|].
    apply cmerge_ok in Hc as (s1 & s2 & H1 & H2 & Hc). cbn beta in H2. unfold cmerge.
    rewrite (NEXT lc _ ck1 s1 H1 eq_refl Hlc). cbn beta. rewrite (NEXT lc _ ck2 s2 H2 eq_refl Hlc).
    match type of Hc with (if ?c then _ else _) = _ => destruct c; [exact Hc | discriminate Hc] end.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    destruct (node_casedisj A cs db1 db2) as [[csa csb]|] eqn:Hn; [|discriminate].
    rewrite APL.node_casedisj_reL, Hn.
    assert (Ea : ledger_of csa = ledger_of cs /\ ledger_of csb = ledger_of cs).
    { pose proof (APL.node_casedisj_reL A (ledger_of cs) cs db1 db2) as Q. rewrite with_ledger_of, Hn in Q.
      injection Q as Qa Qb. split; [rewrite Qa at 1 | rewrite Qb at 1]; apply ledger_of_with. }
    destruct Ea as [Ea Eb].
    apply cmerge_ok in Hc as (s1 & s2 & H1 & H2 & Hc). cbn beta in H2. unfold cmerge.
    rewrite (NEXT lc _ dk1 s1 H1 Ea Hlc). cbn beta. rewrite (NEXT lc _ dk2 s2 H2 Eb Hlc).
    match type of Hc with (if ?c then _ else _) = _ => destruct c; [exact Hc | discriminate Hc] end.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    destruct (node_shdisj A cs sb1 sn1 sb2 sn2) as [cs1|] eqn:Hn; [|discriminate].
    rewrite APL.node_shdisj_reL, Hn. cbn [APL.lmap].
    exact (NEXT lc _ k s Hc (lmap_ledger (fun c => node_shdisj A c sb1 sn1 sb2 sn2) _ _ (fun L0 => APL.node_shdisj_reL A L0 cs sb1 sn1 sb2 sn2) Hn) Hlc).
  - (* [comment removed for export] *) change (kn (with_ledger L cs)) with (kn cs). destruct (kn_contra (kn cs)); [exact Hc | discriminate Hc].
  - (* [comment removed for export] *) change (kn (with_ledger L cs)) with (kn cs).
    destruct (fact_ok (kn cs) K || AP.fact_okL (kn cs) K)%bool; [|discriminate]. rewrite APL.add_kn_reL. exact (NEXT lc _ k s Hc eq_refl Hlc).
  - (* [comment removed for export] *) discriminate Hc.
  - (* [comment removed for export] *) change (kn (with_ledger L cs)) with (kn cs). rewrite APL.set_kn_reL. exact (NEXT lc _ k s Hc eq_refl Hlc).
  - (* [comment removed for export] *) rewrite APL.node_droprange_reL.
    assert (Ed : ledger_of (node_droprange cs db dn) = ledger_of cs) by (unfold node_droprange; destruct (split_lit db); reflexivity).
    exact (NEXT lc _ k s Hc Ed Hlc).
  - (* [comment removed for export] *) change (kn (with_ledger L cs)) with (kn cs). rewrite APL.set_kn_reL. exact (NEXT lc _ k s Hc eq_refl Hlc).
  - (* [comment removed for export] *) destruct (node_bump cs bm) as [cs1|] eqn:Hn; [|discriminate]. rewrite APL.node_bump_reL, Hn. cbn [APL.lmap].
    exact (NEXT lc _ k s Hc (lmap_ledger (fun c => node_bump c bm) _ _ (fun L0 => APL.node_bump_reL L0 cs bm) Hn) Hlc).
  - (* [comment removed for export] *) destruct (node_havoc nx0 cs hrs) as [cs1|] eqn:Hn; [|discriminate].
    rewrite (APL.node_havoc_reL nx0 L cs hrs cs1 HLn Hn). rewrite APL.gkeepE_reL.
    exact (NEXT lc _ k s Hc (eq_trans (ledger_of_gkeepE _ _ _ _) (limp_ledger (fun c => node_havoc nx0 c hrs) _ _ (fun L0 => APL.node_havoc_reL nx0 L0 cs hrs cs1) HCn Hn)) Hlc).
  - (* [comment removed for export] *) destruct (node_havocbig nx0 cs hbK) as [cs1|] eqn:Hn; [|discriminate].
    rewrite (APL.node_havocbig_reL nx0 L cs hbK cs1 HLn Hn). rewrite APL.gkeepE_reL.
    exact (NEXT lc _ k s Hc (eq_trans (ledger_of_gkeepE _ _ _ _) (limp_ledger (fun c => node_havocbig nx0 c hbK) _ _ (fun L0 => APL.node_havocbig_reL nx0 L0 cs hbK cs1) HCn Hn)) Hlc).
  - (* [comment removed for export] *) discriminate Hc.
  - (* [comment removed for export] *)
    unfold AP.sys_okW in *. rewrite sysws_reL, okW_reL.
    destruct (AP.okW xp (xp_sysws xp y cs) cs); [|discriminate]. cbn [negb andb] in Hc |- *.
    destruct y; cbn [andb] in Hc |- *; try discriminate Hc.
    change (is_ecall_at SEGS (with_ledger L cs)) with (is_ecall_at SEGS cs). destruct (is_ecall_at SEGS cs); [|discriminate].
    change (node_sys A nx0 YSetTid (with_ledger L cs)) with (node_settid nx0 (with_ledger L cs)).
    change (node_sys A nx0 YSetTid cs) with (node_settid nx0 cs) in Hc.
    destruct (node_settid nx0 cs) as [cs1|] eqn:Hn; [|discriminate].
    rewrite (APL.node_settid_reL nx0 L cs cs1 HLn Hn). cbn [AP.sys_frame] in Hc |- *.
    assert (E1 : ledger_of cs1 = ledger_of cs) by exact (limp_ledger (fun c => node_settid nx0 c) _ _ (fun L0 => APL.node_settid_reL nx0 L0 cs cs1) HCn Hn).
    destruct (xp_sysws xp YSetTid cs);
      [rewrite APL.gkeepE_reL; exact (NEXT lc _ k s Hc (eq_trans (ledger_of_gkeepE _ _ _ _) E1) Hlc)
      |rewrite APL.gpures_reL; exact (NEXT lc _ k s Hc (eq_trans (ledger_of_gpures _ _ _) E1) Hlc)].
  - (* [comment removed for export] *) discriminate Hc.
  - (* [comment removed for export] *) discriminate Hc.
  - (* [comment removed for export] *) discriminate Hc.
  - (* [comment removed for export] *) discriminate Hc.
  - (* [comment removed for export] *)
    unfold AP.x_okW in *. rewrite xws_reL, okW_reL.
    destruct (AP.okW xp (xp_xws xp x args cs) cs); [|discriminate]. cbn [negb] in Hc |- *.
    destruct (node_x SEGS A nx0 x args cs) as [cs1|] eqn:Hn; [|discriminate].
    rewrite (APL.node_x_reL SEGS nx0 A x args L cs cs1 HLn Hn). rewrite gsuccW_reL.
    exact (NEXT lc _ k s Hc (eq_trans (ledger_of_gsuccW _ _ _) (limp_ledger (fun c => node_x SEGS A nx0 x args c) _ _ (fun L0 => APL.node_x_reL SEGS nx0 A x args L0 cs cs1) HCn Hn)) Hlc).
  - (* [comment removed for export] *)
    destruct (AP.ext_okW xp xid xargs cs) eqn:Hok; [|discriminate]. cbn [negb] in Hc.
    assert (Hok' : AP.ext_okW xp xid xargs (with_ledger L cs) = true) by (unfold AP.ext_okW in *; rewrite xnws_reL, okW_reL; exact Hok).
    rewrite Hok'. cbn [negb].
    destruct (xp_extG xp xid); [discriminate Hc|].
    destruct (XN xid xargs cs) as [cs1|] eqn:Hn; [|discriminate].
    rewrite (XN_reL xid xargs cs cs1 L Hok HLn Hn).
    assert (E1 : ledger_of cs1 = ledger_of cs) by exact (limp_ledger (fun c => XN xid xargs c) _ _ (fun L0 HL0 => XN_reL xid xargs cs cs1 L0 Hok HL0) HCn Hn).
    rewrite xnws_reL, APL.gkeepE_reL, gsuccW_reL.
    destruct (xp_extF xp xid).
    + exact (NEXT lc _ k s Hc (eq_trans (ledger_of_gkeepE _ _ _ _) E1) Hlc).
    + exact (NEXT lc _ k s Hc (eq_trans (ledger_of_gsuccW _ _ _) E1) Hlc).
  - (* [comment removed for export] *)
    destruct (AP.emit_okW xp eid eargs cs) eqn:Hok; [|discriminate]. cbn [negb] in Hc.
    assert (Hok' : AP.emit_okW xp eid eargs (with_ledger L cs) = true) by (unfold AP.emit_okW in *; rewrite xews_reL, okW_reL; exact Hok).
    rewrite Hok'. cbn [negb].
    destruct (XE eid eargs cs) as [[[fd ps] cs1]|] eqn:Hn; [|discriminate].
    rewrite (XE_reL eid eargs cs fd ps cs1 L Hok HLn Hn). rewrite xews_reL, gsuccW_reL.
    assert (E1 : ledger_of cs1 = ledger_of cs).
    { pose proof (XE_reL eid eargs cs fd ps cs1 (ledger_of cs) Hok HCn Hn) as Q. rewrite with_ledger_of, Hn in Q.
      injection Q as Q. rewrite Q at 1. apply ledger_of_with. }
    destruct (CHECK bfuel fuel lc (AP.gsuccW xp (xp_xews xp eid eargs cs) cs cs1) k) as [s1| |] eqn:H1; [|discriminate|discriminate].
    rewrite (NEXT lc _ k s1 H1 (eq_trans (ledger_of_gsuccW _ _ _) E1) Hlc). exact Hc.
  - (* [comment removed for export] *) discriminate Hc.
  - (* [comment removed for export] *) discriminate Hc.
  - (* [comment removed for export] *)
    destruct lc as [[h nx lo hi|j' js' sk' b' lo'|[|wT whs] wcur lo hi wV wxs wxts|so shi]|]; cbn [reledger_lc map lcok] in *; try discriminate Hc; try contradiction.
    destruct Hlc as [Hlo Hhi].
    change (pc (with_ledger L cs)) with (pc cs). change (pc (with_ledger L wT)) with (pc wT). change (nxt (with_ledger L wT)) with (nxt wT).
    change (kn (with_ledger L cs)) with (kn cs).
    destruct (Z.eqb (pc cs) (pc wT)); [|discriminate].
    destruct (entails_s A lo (nxt wT) [] cs wT) as [sg|] eqn:He; [|discriminate].
    rewrite (APL.entails_s_reL A lo (nxt wT) [] L cs wT sg HeL (APL.APS_ledger_mono _ _ _ HLL0 Hlo) He).
    rewrite with_props_reL, APL.props_reL. exact (if_cerr _ _ _ _ _ _ _ Hc).
  - (* [comment removed for export] *) discriminate Hc.
  - (* [comment removed for export] *) change (is_ecall_at SEGS (with_ledger L cs)) with (is_ecall_at SEGS cs). change (node_exit (with_ledger L cs)) with (node_exit cs).
    destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_exit cs); [exact Hc|discriminate].
  - (* [comment removed for export] *) change (node_spin SEGS (with_ledger L cs)) with (node_spin SEGS cs). destruct (node_spin SEGS cs); [exact Hc|discriminate].
  - (* [comment removed for export] *) discriminate Hc.
  - (* [comment removed for export] *) discriminate Hc.
  - (* [comment removed for export] *) discriminate Hc.
  - (* [comment removed for export] *) discriminate Hc.
  - (* [comment removed for export] *) destruct (node_havocbrk nx0 cs hlo hhi) as [cs1|] eqn:Hn; [|discriminate].
    rewrite (APL.node_havocbrk_reL nx0 L cs hlo hhi cs1 HLn Hn). rewrite APL.gpures_reL.
    exact (NEXT lc _ hk s Hc (eq_trans (ledger_of_gpures _ _ _) (limp_ledger (fun c => node_havocbrk nx0 c hlo hhi) _ _ (fun L0 => APL.node_havocbrk_reL nx0 L0 cs hlo hhi cs1) HCn Hn)) Hlc).
  - (* [comment removed for export] *) destruct (node_intro nx0 cs ilo ihi) as [cs1|] eqn:Hn; [|discriminate].
    rewrite (APL.node_intro_reL nx0 L cs ilo ihi cs1 HLn Hn). rewrite APL.gkeepE_reL.
    exact (NEXT lc _ ik s Hc (eq_trans (ledger_of_gkeepE _ _ _ _) (limp_ledger (fun c => node_intro nx0 c ilo ihi) _ _ (fun L0 => APL.node_intro_reL nx0 L0 cs ilo ihi cs1) HCn Hn)) Hlc).
  - (* [comment removed for export] *) discriminate Hc.
  - (* [comment removed for export] *) discriminate Hc.
  - (* [comment removed for export] *) discriminate Hc.
  - (* [comment removed for export] *) discriminate Hc.
  - (* [comment removed for export] *)
    destruct lc as [[h nx lo hi|j' js' sk' b' lo'|whs' wcur' wlo' whi' wV' wxs' wxts'|so shi]|]; cbn [reledger_lc lcok] in *; try discriminate Hc; contradiction.
  - (* [comment removed for export] *) destruct (node_abstractcell A cs ab an) as [cs1|] eqn:Hn; [|discriminate]. rewrite APL.node_abstractcell_reL, Hn. cbn [APL.lmap].
    rewrite APL.gpures_reL. exact (NEXT lc _ ak s Hc (eq_trans (ledger_of_gpures _ _ _) (lmap_ledger (fun c => node_abstractcell A c ab an) _ _ (fun L0 => APL.node_abstractcell_reL A L0 cs ab an) Hn)) Hlc).
  - (* [comment removed for export] *) destruct (node_havocwords nx0 cs hws) as [cs1|] eqn:Hn; [|discriminate].
    rewrite (APL.node_havocwords_reL nx0 L cs hws cs1 HLn Hn). rewrite APL.gpures_reL.
    exact (NEXT lc _ hwk s Hc (eq_trans (ledger_of_gpures _ _ _) (limp_ledger (fun c => node_havocwords nx0 c hws) _ _ (fun L0 => APL.node_havocwords_reL nx0 L0 cs hws cs1) HCn Hn)) Hlc).
  - (* [comment removed for export] *) destruct (node_respell cs rsr rse) as [cs1|] eqn:Hn; [|discriminate]. rewrite APL.node_respell_reL, Hn. cbn [APL.lmap].
    rewrite APL.gkeepE_reL. exact (NEXT lc _ rsk s Hc (eq_trans (ledger_of_gkeepE _ _ _ _) (lmap_ledger (fun c => node_respell c rsr rse) _ _ (fun L0 => APL.node_respell_reL L0 cs rsr rse) Hn)) Hlc).
  - (* [comment removed for export] *)
    unfold AP.normT in Hc |- *. rewrite Hw in Hc |- *. rewrite APL.ledger_of_reL.
    set (G := fun hp : acs * plan => (with_ledger L (fst hp), snd hp)).
    set (hA := map (fun hp : acs * plan => (with_ledger (ledger_of cs) (fst hp), snd hp)) wheads) in Hc.
    set (xA := map (fun hp : acs * plan => (with_ledger (ledger_of cs) (fst hp), snd hp)) wexits) in Hc.
    assert (EhB : map G wheads = map G hA).
    { unfold hA, G. rewrite map_map. apply map_ext. intros [T b]. cbn [fst snd]. rewrite with_ledger_twice. reflexivity. }
    assert (ExB : map G wexits = map G xA).
    { unfold xA, G. rewrite map_map. apply map_ext. intros [T b]. cbn [fst snd]. rewrite with_ledger_twice. reflexivity. }
    rewrite EhB, ExB. clear EhB ExB.
    assert (LA : forall T b, In (T, b) hA -> ledger_of T = ledger_of cs).
    { intros T b Hin. unfold hA in Hin. apply in_map_iff in Hin as ([T0 b0'] & E & _). cbn [fst snd] in E. injection E as <- <-. apply ledger_of_with. }
    assert (LX : forall x kx, In (x, kx) xA -> ledger_of x = ledger_of cs).
    { intros x kx Hin. unfold xA in Hin. apply in_map_iff in Hin as ([x0 k0] & E & _). cbn [fst snd] in E. injection E as <- <-. apply ledger_of_with. }
    clearbody hA xA.
    destruct hA as [|[T0 b0'] hrest]; [discriminate|]. cbn [map G fst snd] in Hc |- *.
    assert (EF : map fst (map G hrest) = map (with_ledger L) (map fst hrest)) by (rewrite !map_map; apply map_ext; intros [T b]; reflexivity).
    rewrite EF.
    change (with_ledger L T0 :: map (with_ledger L) (map fst hrest)) with (map (with_ledger L) (T0 :: map fst hrest)).
    destruct (while_okN nx0 cs wlo (T0 :: map fst hrest) wV wxs) eqn:Hwk; [|discriminate]. cbn [andb] in Hc.
    destruct (while_okN_facts cs wlo _ wV wxs Hwk) as (Wn0 & Wnxt & Wheads & _ & _).
    assert (Hlo : (b0 <= wlo)%nat) by lia.
    rewrite (while_okN_reL cs wlo (T0 :: map fst hrest) wV wxs L (APL.APS_ledger_mono _ _ _ HLL0 Hlo) Hwk). cbn [andb].
    change (pc (with_ledger L cs)) with (pc cs). change (pc (with_ledger L T0)) with (pc T0). change (nxt (with_ledger L T0)) with (nxt T0).
    destruct (Z.eqb (pc cs) (pc T0)); [|discriminate].
    destruct (entails_s A wlo (nxt T0) [] cs T0) as [sg0|] eqn:He; [|discriminate].
    rewrite (APL.entails_s_reL A wlo (nxt T0) [] L cs T0 sg0 HeL (APL.APS_ledger_mono _ _ _ HLL0 Hlo) He).
    rewrite needs_props_reL, APL.props_reL.
    destruct (AP.needs_props xp cs (map (ginst sg0) (a_props T0))); [|discriminate].
    destruct (chk_exits nx0 (CHECK bfuel fuel lc) wlo wxs xA) as [xts|e] eqn:Hxts; [|exfalso; exact (chk_exits_err _ _ _ _ _ Hxts _ Hc)].
    subst G. rewrite (chk_exits_reL (CHECK bfuel fuel lc) (CHECK bfuel fuel (reledger_lc L lc)) wlo wxs L xA xts); [| |exact (APL.APS_ledger_mono _ _ _ HLL0 Hlo)|exact Hxts].
    2:{ intros x kx sx Hin Htx Hck. exact (NEXT lc x kx sx Hck (LX x kx Hin) Hlc). }
    set (G := fun hp : acs * plan => (with_ledger L (fst hp), snd hp)).
    change ((with_ledger L T0, b0') :: map G hrest) with (map G ((T0, b0') :: hrest)).
    apply (chk_heads_reL (CHECK bfuel fuel) (CHECK bfuel fuel) (T0 :: map fst hrest) wlo wV wxs xts L ((T0, b0') :: hrest) 0 s); [|exact Hc].
    intros i T b Hi Hck. cbn [Nat.add] in Hck |- *.
    assert (HT : In (T, b) ((T0, b0') :: hrest)) by exact (nth_error_In _ _ Hi).
    assert (Hhok : head_ok nx0 wlo wV T = true).
    { apply Wheads. destruct HT as [E|HT]; [injection E as -> ->; left; reflexivity | right; apply in_map_iff; exists (T, b); split; [reflexivity | exact HT]]. }
    destruct (head_ok_facts wlo wV T Hhok) as (_ & _ & _ & HloT & _).
    apply (IH (Some (WC (T0 :: map fst hrest) i wlo (nxt T) wV wxs xts)) b T wxs L b0 Hw HeL HLL0); [rewrite (LA T b HT); exact HLC0 | rewrite (LA T b HT); exact Hlen | cbn [lcok]; lia | exact Hck].
  - (* [comment removed for export] *)
    destruct lc as [[h nx lo hi|j' js' sk' b' lo'|whs wcur lo hi wV wxs wxts|so shi]|]; cbn [reledger_lc lcok] in *; try discriminate Hc; try contradiction.
    destruct Hlc as [Hlo Hhi].
    rewrite nth_error_map. destruct (nth_error whs nh) as [wT|]; [|discriminate]. cbn [option_map].
    change (pc (with_ledger L cs)) with (pc cs). change (pc (with_ledger L wT)) with (pc wT). change (nxt (with_ledger L wT)) with (nxt wT).
    change (kn (with_ledger L cs)) with (kn cs).
    destruct (Z.eqb (pc cs) (pc wT)); [|discriminate].
    destruct (entails_s A lo (nxt wT) nwh cs wT) as [sg|] eqn:He; [|discriminate].
    rewrite (APL.entails_s_reL A lo (nxt wT) nwh L cs wT sg HeL (APL.APS_ledger_mono _ _ _ HLL0 Hlo) He).
    rewrite with_props_reL, APL.props_reL. exact (if_cerr _ _ _ _ _ _ _ Hc).
  - (* [comment removed for export] *)
    destruct lc as [[h nx lo hi|j' js' sk' b' lo'|whs wcur lo hi wV wxs wxts|so shi]|]; cbn [reledger_lc lcok] in *; try discriminate Hc; try contradiction.
    + destruct Hlc as [Hlo Hhi].
      rewrite nth_error_map. destruct (nth_error wxts bi) as [[x sx]|]; [|discriminate]. cbn [option_map fst snd].
      change (nxt (with_ledger L x)) with (nxt x).
      destruct (entails_s A lo (nxt x) bh cs x) as [sg|] eqn:He; [|discriminate].
      rewrite (APL.entails_s_reL A lo (nxt x) bh L cs x sg HeL (APL.APS_ledger_mono _ _ _ HLL0 Hlo) He).
      rewrite with_props_reL, APL.props_reL. exact (if_cerr _ _ _ _ _ _ _ Hc).
    + rewrite nth_error_map. destruct (nth_error so bi) as [x|]; [|discriminate]. cbn [option_map].
      change (nxt (with_ledger L x)) with (nxt x).
      destruct (entails_s A shi (nxt x) bh cs x) as [sg|] eqn:He; [|discriminate].
      rewrite (APL.entails_s_reL A shi (nxt x) bh L cs x sg HeL (APL.APS_ledger_mono _ _ _ HLL0 Hlc) He). exact Hc.
  - (* [comment removed for export] *)
    destruct (xp_sg xp usid) as [SD0|] eqn:Hsg; [|discriminate].
    destruct (AP.segdef_wf nx0 SD0) eqn:Hwf0; [|discriminate]. cbn [negb] in Hc |- *.
    unfold AP.use_view in Hc |- *. rewrite APL.ledger_of_reL.
    destruct (AP.skel_free SD0) eqn:Hsf; [|discriminate Hc].
    destruct (AP.reskel (sg_lo SD0) (sg_hi SD0) (ledger_of (sg_in SD0)) (ledger_of cs)) as [[Lc skh]|] eqn:Hrc; [|discriminate].
    destruct Hlen as (Hl1 & Hl2 & Hl3).
    destruct (APL.reskel_mono _ _ _ _ _ _ L Hrc Hl1 Hl2 Hl3) as (La & ska & Hra). rewrite Hra.
    cbn [andb negb] in Hc |- *.
    rewrite !APL.sg_top_reledger in Hc |- *.
    cbn [sg_lo sg_hi sg_in sg_w sg_outs sg_shape AP.reledger_sd] in Hc |- *.
    change (nxt (with_ledger L cs)) with (nxt cs). change (kn (with_ledger L cs)) with (kn cs). change (a_props (with_ledger L cs)) with (a_props cs).
    match goal with |- context [map ?f ska ++ uhints] =>
      change (map f ska) with (APL.shiftk (Nat.max (sg_lo SD0) (nxt cs) - sg_lo SD0)%nat ska);
      change (map f skh) with (APL.shiftk (Nat.max (sg_lo SD0) (nxt cs) - sg_lo SD0)%nat skh) in Hc end.
    (* [comment removed for export] *)
    pose proof Hsf as Hsf'. unfold AP.skel_free in Hsf'.
    destruct (AP.skel_lo (ledger_of (sg_in SD0))) as [b|] eqn:Hb; [|discriminate Hsf'].
    apply andb_prop in Hsf' as [Hsf' Hnd]. apply andb_prop in Hsf' as [Hsf' Hle]. apply andb_prop in Hsf' as [Hsf' HcW]. apply andb_prop in Hsf' as [HcI HcO].
    destruct (entails_s A _ _ _ cs _) as [sg|] eqn:He; [|discriminate].
    destruct (APL.use_site_reL A SD0 _ _ _ b cs L Lc La skh ska uhints sg Hb HcI HcO HcW Hle Hnd Hrc Hra
                (APL.APS_ledger_mono _ _ _ HLn (Nat.le_max_r _ _)) He) as (X & E1 & E2 & E3 & E4 & E5).
    rewrite E2. cbv iota beta. rewrite okW_reL.
    match type of Hc with (if negb ?t then _ else _) = _ => destruct t eqn:Hfa; [|discriminate Hc] end.
    apply andb_prop in Hfa as [Hfr Hfa]. rewrite (APL.fresh_ok_reL nx0 L cs Hfr HLn), (E3 Hfa). cbn [andb negb] in Hc |- *.
    rewrite E4.
    match type of Hc with (if negb ?t then _ else _) = _ => destruct t; [|discriminate Hc] end. cbn [negb] in Hc |- *.
    change (map (with_ledger La) (sg_outs SD0)) with (map (fun x => with_ledger La (with_ledger Lc x)) (sg_outs SD0)).
    rewrite <- (map_map (with_ledger Lc) (with_ledger La) (sg_outs SD0)).
    match type of Hc with match ?u with LOk _ => _ | LErr _ => _ end = _ => destruct u as [ss|r] eqn:Hua end.
    + erewrite (APL.use_all_transfer _ _ _ _ _ _ _ _ (with_ledger La) _ uks ss); [destruct (forallb (shape_eqb (nth 0 ss SNil)) ss); [exact Hc|discriminate Hc] | | exact Hua].
      intros x k s1 Hin Hck. apply in_map_iff in Hin as (x0 & <- & Hin0).
      change (with_ledger La (with_ledger Lc x0)) with (with_ledger La x0).
      match goal with |- CHECK _ _ _ (use_exit _ _ _ ?FR ?KP _) _ = _ => destruct (E5 FR KP x0 Hin0) as [Q1' Q2']; rewrite Q1' ; exact (NEXT lc _ k s1 Hck Q2' Hlc) end.
    + exfalso. exact (use_all_err _ _ _ _ _ _ _ _ Hua Hc).
  - (* [comment removed for export] *) change (nxt (with_ledger L cs)) with (nxt cs). rewrite need1_reL, APL.props_reL, APL.set_props_reL.
    destruct (gvars_lt (nxt cs) gg); [|discriminate].
    destruct (AP.need1 xp cs (VCAtom gg)); [exact (NEXT lc _ gk s Hc eq_refl Hlc)|].
    destruct (CHECK bfuel fuel lc (set_props cs (gg :: a_props cs)) gk) as [s1| |] eqn:H1; try discriminate Hc.
  - (* [comment removed for export] *) rewrite APL.props_reL, APL.set_props_reL. exact (NEXT lc _ gdk s Hc eq_refl Hlc).
  - (* [comment removed for export] *) change (nxt (with_ledger L cs)) with (nxt cs). rewrite need1_reL, APL.add_kn_reL.
    destruct (kentry_vars_lt (nxt cs) gK); [|discriminate].
    destruct (AP.need1 xp cs (VCFact gK)); [exact (NEXT lc _ gfk s Hc eq_refl Hlc)|].
    destruct (CHECK bfuel fuel lc (add_kn cs [gK]) gfk) as [s1| |] eqn:H1; try discriminate Hc.
  - (* [comment removed for export] *)
    assert (Et : AP.tfact_inst (reledger_lc L lc) (with_ledger L cs) gtx gti gtK = AP.tfact_inst lc cs gtx gti gtK).
    { unfold AP.tfact_inst. destruct lc as [[? ? ? ?|? ? ? ? ?|whs wcur wlo whi wV wxs wxts|? ?]|]; cbn [reledger_lc]; try reflexivity.
      destruct gtx; [rewrite nth_error_map; destruct (nth_error wxts gti) as [[T sx]|]; reflexivity | rewrite nth_error_map; destruct (nth_error whs gti) as [T|]; reflexivity]. }
    rewrite Et. destruct (AP.tfact_inst lc cs gtx gti gtK) as [gKi|]; [|discriminate].
    change (nxt (with_ledger L cs)) with (nxt cs). rewrite need1_reL. unfold AP.add_kn_end in *. change (kn (with_ledger L cs)) with (kn cs). rewrite APL.set_kn_reL.
    destruct (kentry_vars_lt (nxt cs) gKi); [|discriminate].
    destruct (AP.need1 xp cs (VCFact gKi)); [exact (NEXT lc _ gtfk s Hc eq_refl Hlc)|].
    destruct (CHECK bfuel fuel lc (set_kn cs (kn cs ++ [gKi])) gtfk) as [s1| |] eqn:H1; try discriminate Hc.
  - (* [comment removed for export] *) discriminate Hc.   (* [comment removed for export] *)
  - (* [comment removed for export] *) discriminate Hc.   (* [comment removed for export] *)
  - (* [comment removed for export] *) discriminate Hc.   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
Lemma list_set_nth_maps_match : forall E ms l i m sz,
  nth_error ms i = Some m -> is_fog m = false -> 0 <= sz < two64 ->
  bv_unsigned (edenot E (am_len m)) <= sz ->
  maps_match E ms l -> maps_match E (list_set_nth i (fog_token sz) ms) l.
Proof.
  intros E ms. induction ms as [|m0 ms IH]; intros l i m sz Hn Hf Hsz Hle HM; [destruct i; discriminate|].
  destruct i as [|i]; cbn [nth_error] in Hn; cbn [list_set_nth maps_match] in *.
  - injection Hn as ->. rewrite Hf in HM. destruct HM as (l' & -> & HM).
    unfold fog_token, is_fog. cbn [am_kind am_len mkind_eqb]. right. exists (amap_den E m), l'.
    split; [reflexivity|]. split; [|exact HM]. unfold uE, amap_den. cbn [snd edenot]. rewrite u64_lit by (unfold two64 in Hsz; lia). exact Hle.
  - destruct (is_fog m0).
    + destruct HM as [HM|(iv & l' & -> & Hs & HM)]; [left; eapply IH; eassumption | right].
      exists iv, l'. split; [reflexivity|]. split; [exact Hs | eapply IH; eassumption].
    + destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | eapply IH; eassumption].
Qed.

Lemma list_insert_nth_maps_match : forall E ms l i sz,
  maps_match E ms l -> maps_match E (list_insert_nth i (fog_token sz) ms) l.
Proof.
  intros E ms. induction ms as [|m0 ms IH]; intros l i sz HM.
  - destruct i; cbn [list_insert_nth maps_match]; unfold fog_token, is_fog; cbn [am_kind mkind_eqb]; left; exact HM.
  - destruct i as [|i]; cbn [list_insert_nth].
    + cbn [maps_match]. unfold fog_token at 1. unfold is_fog at 1. cbn [am_kind mkind_eqb]. left. exact HM.
    + cbn [maps_match] in *. destruct (is_fog m0).
      * destruct HM as [HM|(iv & l' & -> & Hs & HM)]; [left; apply IH; exact HM | right].
        exists iv, l'. split; [reflexivity|]. split; [exact Hs | apply IH; exact HM].
      * destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | apply IH; exact HM].
Qed.

Lemma In_list_set_nth : forall {T} (l : list T) i x y, In y (list_set_nth i x l) -> y = x \/ In y l.
Proof.
  intros T l. induction l as [|a l IH]; intros i x y H; [destruct i; cbn in H; destruct H|].
  destruct i; cbn in H; destruct H as [H|H]; try (right; left; exact H); try (left; symmetry; exact H).
  - right. right. exact H.
  - destruct (IH _ _ _ H) as [->|H']; [left; reflexivity | right; right; exact H'].
Qed.
Lemma In_list_insert_nth : forall {T} (l : list T) i x y, In y (list_insert_nth i x l) -> y = x \/ In y l.
Proof.
  intros T l. induction l as [|a l IH]; intros i x y H.
  - destruct i; cbn in H; destruct H as [H|[]]; left; symmetry; exact H.
  - destruct i; cbn in H; destruct H as [H|H]; try (left; symmetry; exact H); try (right; left; exact H).
    + right. exact H.
    + destruct (IH _ _ _ H) as [->|H']; [left; reflexivity | right; right; exact H'].
Qed.

Lemma cs_ok_with_maps : forall E cs R FULL model ms',
  cs_ok E cs R FULL model ->
  maps_match E ms' (vm_maps (m_vmmaps model)) ->
  (forall m, In m ms' -> m = fog_token (match am_len m with ELit z => z | _ => 0 end) \/ In m (a_maps cs)) ->
  cs_ok E (with_maps cs ms') R FULL model.
Proof.
  intros E cs R FULL model ms' HC HM Hsub.
  assert (HMr : Mr E (with_maps cs ms') model FULL = Mr E cs model FULL) by reflexivity.
  assert (HA : allowA E (with_maps cs ms') = allowA E cs) by reflexivity.
  destruct HC; constructor; unfold with_maps; rewrite ?HMr, ?HA;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn] in *; try assumption.
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk. destruct (Hsub m Hin) as [Hm|Hm].
    + rewrite Hm in Hk. cbn in Hk. discriminate.
    + exact (proj1 (Forall_forall _ _) co_holes0 m Hm Hk).
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk. destruct (Hsub m Hin) as [Hm|Hm].
    + rewrite Hm in Hk. cbn in Hk. destruct Hk; discriminate.
    + exact (proj1 (Forall_forall _ _) co_none0 m Hm Hk).
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk. destruct (Hsub m Hin) as [Hm|Hm].
    + rewrite Hm in Hk. cbn in Hk. discriminate.
    + exact (proj1 (Forall_forall _ _) co_kinds0 m Hm Hk).
Qed.

Lemma fog_sound : forall E cs R FULL model i sz cs',
  cs_ok E cs R FULL model -> node_fog cs i sz = Some cs' -> cs_ok E cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model i sz cs' HC H. unfold node_fog in H.
  destruct (nth_error (a_maps cs) i) as [m|] eqn:Hn; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-. split; [|reflexivity].
  apply andb_prop in Hc as [Hc Hx]. apply andb_prop in Hc as [Hc Hs2]. apply andb_prop in Hc as [Hnf Hs1].
  apply negb_true_iff in Hnf. apply Z.leb_le in Hs1. apply Z.ltb_lt in Hs2.
  destruct (xhi (kn cs) (am_len m)) as [h|] eqn:Hh; [|discriminate]. apply Z.leb_le in Hx.
  pose proof (xhi_sound SEGS E _ (kn cs) (am_len m) h (co_know _ _ _ _ _ HC) Hh) as Hh'.
  apply cs_ok_with_maps; [exact HC | |].
  - eapply list_set_nth_maps_match; [exact Hn | exact Hnf | lia | lia | exact (co_maps _ _ _ _ _ HC)].
  - intros m' Hin. destruct (In_list_set_nth _ _ _ _ Hin) as [->|Hin']; [left; reflexivity | right; exact Hin'].
Qed.

Lemma fognew_sound : forall E cs R FULL model i sz cs',
  cs_ok E cs R FULL model -> node_fognew cs i sz = Some cs' -> cs_ok E cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model i sz cs' HC H. unfold node_fognew in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-. split; [|reflexivity].
  apply cs_ok_with_maps; [exact HC | apply list_insert_nth_maps_match; exact (co_maps _ _ _ _ _ HC) |].
  intros m' Hin. destruct (In_list_insert_nth _ _ _ _ Hin) as [->|Hin']; [left; reflexivity | right; exact Hin'].
Qed.

Lemma page_allowedb_app_l : forall l1 l2 p, page_allowedb l1 p = true -> page_allowedb (l1 ++ l2) p = true.
Proof. intros. unfold page_allowedb in *. rewrite existsb_app, H. reflexivity. Qed.
Lemma MInv_app_r : forall l1 l2 m, MInv l1 m -> eager_used m + A_bytes (l1 ++ l2) <= vm_limit (m_vmmaps m) -> MInv (l1 ++ l2) m.
Proof.
  intros l1 l2 m [N1 N2 N3 N4 N5] Hb. constructor; try assumption.
  intros p Hp. apply page_allowedb_app_l. apply N3. exact Hp.
Qed.
Lemma allow1_cost : forall E b n nhi, bv_unsigned (edenot E n) <= nhi -> A_bytes (allow1 E (b, n)) <= vis_cost nhi.
Proof.
  intros E b n nhi Hn. unfold allow1, vis_cost. cbn [A_bytes fst snd]. unfold sh_lo, sh_hi. cbn [fst snd].
  pose proof (u64_range (edenot E b)) as Rb. pose proof (u64_range (edenot E n)) as Rn. unfold uE in *. pose proof SHADOW_ok as So. unfold shadow_ok in So.
  pose proof (pageup_pagedown_gap (bv_unsigned (edenot E b)) (bv_unsigned (edenot E b) + bv_unsigned (edenot E n)) ltac:(lia)) as G1.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  pose proof (pageup_pagedown_gap (shadow_off A + bv_unsigned (edenot E b) / 8)
                (shadow_off A + (bv_unsigned (edenot E b) + bv_unsigned (edenot E n)) / 8) ltac:(lia)) as G2.
  assert (G3 : (bv_unsigned (edenot E b) + bv_unsigned (edenot E n)) / 8 - bv_unsigned (edenot E b) / 8 <= nhi / 8 + 1) by lia.
  lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma ghost_sound : forall E cs R FULL model b n cs',
  cs_ok E cs R FULL model -> node_ghost LIMIT cs b n = Some cs' -> cs_ok E cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model b n cs' HC H. unfold node_ghost in H.
  destruct (xhi (kn cs) n) as [nhi|] eqn:Hx; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-. split; [|reflexivity].
  apply andb_prop in Hc as [Hc Hb]. apply Z.leb_le in Hb.
  pose proof (xhi_sound SEGS E _ (kn cs) n nhi (co_know _ _ _ _ _ HC) Hx) as Hn.
  set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _).
  assert (HMr : Mr E cs' model FULL = Mr E cs model FULL) by reflexivity.
  assert (HA : allowA E cs' = allowA E cs ++ allow1 E (b, n)).
  { unfold allowA, cs'. cbn [a_vis a_ghost]. rewrite app_assoc, !flat_map_app. cbn [flat_map]. rewrite app_nil_r. reflexivity. }
  assert (HAB : A_bytes (allowA E cs') <= A_bytes (allowA E cs) + vis_cost nhi).
  { rewrite HA, A_bytes_app. pose proof (allow1_cost E b n nhi Hn). lia. }
  pose proof (co_limit _ _ _ _ _ HC) as HL. pose proof (co_eager _ _ _ _ _ HC) as HE. pose proof (co_abytes _ _ _ _ _ HC) as HAB0.
  destruct HC; constructor; unfold cs'; rewrite ?HMr;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn] in *; try assumption.
  - fold cs'. lia.
  - fold cs'. rewrite HA. apply MInv_app_r; [exact co_minv0|]. rewrite <- HA. fold cs' in HAB. rewrite HL. lia.
  - intros a H1 H2 H3 H4 H5. apply (co_zero0 a H1 H2 H3 H4).
    unfold in_ghost in H5 |- *. cbn [a_ghost] in H5. rewrite existsb_app in H5. apply orb_false_iff in H5 as [H5 _]. exact H5.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma kzero_x_sound0 : forall E M allkn k b off n,
  know_ok SEGS E M allkn ->
  know_ok SEGS E M k -> kzero_x allkn k b off n = true ->
  (forall i, 0 <= i < elenZ E n -> M (Z_to_bv 64 (estart E (SA b off) + i)) = Some (Z_to_bv 8 0))
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64.
Proof.
  intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest].
  destruct K; try exact (IH Hrest H).
  lazymatch type of H with context [KZero ?za ?zl :: rest] => destruct za as [zb zk]; rename zl into zn end.
  cbn [kzero_x] in H.
  assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kzero_x allkn rest b off n) = true ->
                 (c1 || c2)%bool = true \/ kzero_x allkn rest b off n = true)
    by (intros [|] [|]; cbn; auto).
  apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hz]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in Hz, F1, F2, F4 |- *. cbn [a_base a_off] in Hz, F1, F2, F4 |- *.
  pose proof (u64_range (edenot E n)) as Hnr.
  assert (CORE : bv_unsigned (edenot E zb) + zk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E zb) + zk + elenZ E zn ->
                 (forall i, 0 <= i < elenZ E n -> M (Z_to_bv 64 (bv_unsigned (edenot E b) + off + i)) = Some (Z_to_bv 8 0))
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
  { intros A0 B0. split; [|unfold elenZ in *; lia]. intros i Hi.
    replace (bv_unsigned (edenot E b) + off + i) with (bv_unsigned (edenot E zb) + zk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E zb) + zk) + i)) by lia.
    apply Hz. lia. }
  apply orb_prop in H as [H|H].
  - destruct (expr_eqb b zb && Z.leb zk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst zb.
    destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
    destruct (xlo allkn zn) as [zl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
    pose proof (xhi_sound SEGS E M allkn n nh Hall Hxh). pose proof (xlo_sound SEGS E M allkn zn zl Hall Hxl).
    apply CORE; unfold elenZ in *; lia.
  - pose proof (xinside_sound SEGS E M allkn b off n zb zk zn Hall H) as [A0 B0].
    unfold estart in A0, B0. cbn [a_base a_off] in A0, B0. apply CORE; lia.
Qed.

Lemma A_bytes_fm_split : forall E (f : expr * expr -> bool) l,
  A_bytes (flat_map (allow1 E) l)
  = A_bytes (flat_map (allow1 E) (List.filter f l)) + A_bytes (flat_map (allow1 E) (List.filter (fun p => negb (f p)) l)).
Proof.
  intros E f l. induction l as [|p l IH]; cbn [flat_map List.filter]; [reflexivity|].
  rewrite A_bytes_app, IH. destruct (f p); cbn [negb flat_map]; rewrite ?A_bytes_app; lia.
Qed.

Lemma A_bytes_allow1_nonneg : forall E p, 0 <= A_bytes (allow1 E p).
Proof.
  intros E p. unfold allow1. cbn [A_bytes fst snd].
  pose proof (pagedown_le (uE E (fst p))). pose proof (pageup_ge (uE E (fst p) + uE E (snd p))).
  pose proof (pagedown_le (sh_lo E p)). pose proof (pageup_ge (sh_hi E p)).
  pose proof (u64_range (edenot E (snd p))). unfold sh_lo, sh_hi, uE in *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma vis_here_eq : forall b n p, vis_here b n p = true -> p = (b, n).
Proof.
  intros b n [pb pn] H. unfold vis_here in H. cbn [fst snd] in H. apply andb_prop in H as [H1 H2].
  apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. subst. reflexivity.
Qed.

Lemma A_bytes_fm_here : forall E b n l,
  Forall (fun p => p = (b, n)) l -> A_bytes (flat_map (allow1 E) l) = Z.of_nat (length l) * A_bytes (allow1 E (b, n)).
Proof.
  intros E b n l H. induction l as [|p l IH]; [reflexivity|].
  apply Forall_cons_iff in H as [-> H]. cbn [flat_map length]. rewrite A_bytes_app, (IH H). rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma unvis_sound : forall E cs R FULL model b n cs',
  cs_ok E cs R FULL model -> node_unvis A cs b n = Some cs' -> cs_ok E cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model b n cs' HC H. rewrite node_unvis_eq in H. (* [comment removed for export] *) unfold node_unvis_ref in H.
  destruct (split_lit b) as [bb bk] eqn:Hsp.
  destruct (shadow_of A (kn cs) b n) as [[sb sk] sn] eqn:Hsh.
  destruct (xhi (kn cs) b) as [bh|] eqn:Hbh; [|discriminate].
  destruct (xhi (kn cs) n) as [nh|] eqn:Hnh; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  match type of H with Some ?x = Some _ => assert (Hcs : cs' = x) by congruence end. subst cs'. clear H.
  split; [|reflexivity].
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  rename Hc into Hex.
  match goal with Hl : Z.leb 3 (ealign (kn cs) b) = true |- _ => apply Z.leb_le in Hl; rename Hl into Hab end.
  match goal with Hl : Z.leb 3 (ealign (kn cs) n) = true |- _ => apply Z.leb_le in Hl; rename Hl into Han end.
  match goal with Hl : flat_x (kn cs) bb bk n = true |- _ => rename Hl into Hfl end.
  match goal with Hl : Z.leb (bh + nh) CEIL = true |- _ => apply Z.leb_le in Hl; rename Hl into Hceil end.
  match goal with Hl : flat_x (kn cs) sb sk sn = true |- _ => rename Hl into Hfls end.
  match goal with Hl : kzero_x (kn cs) (kn cs) sb sk sn = true |- _ => rename Hl into Hkz end.
  pose proof (co_know _ _ _ _ _ HC) as HK.
  set (M := Mr E cs model FULL) in *.
  (* [comment removed for export] *)
  pose proof (xhi_sound SEGS E M (kn cs) b bh HK Hbh) as Hbh'. pose proof (xhi_sound SEGS E M (kn cs) n nh HK Hnh) as Hnh'.
  pose proof (flat_x_sound E M (kn cs) bb bk n HK Hfl) as (F1 & F2 & F3).
  pose proof (split_lit_denot E b bb bk Hsp) as Hbd.
  set (ub := bv_unsigned (edenot E b)) in *. set (un := bv_unsigned (edenot E n)) in *.
  assert (HB : estart E (SA bb bk) = ub).
  { unfold ub. rewrite Hbd. unfold estart. cbn [a_base a_off]. rewrite u64_lit; [reflexivity|]. unfold estart in F1, F2; cbn [a_base a_off] in F1, F2. lia. }
  rewrite HB in *.
  pose proof (shadow_of_val E M (kn cs) b n sb sk sn HK Hsh Hfls) as [HS0 HSn]. fold ub in HS0. fold un in HSn.
  pose proof SHADOW_ok as So; unfold shadow_ok in So. pose proof (u64_range (edenot E b)) as Rb. fold ub in Rb.
  assert (HSS : estart E (SA sb sk) = shadow_off A + ub / 8).
  { rewrite HS0. rewrite Z.mod_small; [lia|]. unfold CEIL in Hceil.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  set (S := shadow_off A + ub / 8) in *.
  pose proof (ealign_sound SEGS E M (kn cs) b HK) as [Hrb0 Hdb]. pose proof (ealign_sound SEGS E M (kn cs) n HK) as [Hrn0 Hdn].
  fold ub in Hdb. fold un in Hdn.
  assert (D8b : (8 | ub)). { eapply Z.divide_trans; [|exact Hdb]. exists (2 ^ (ealign (kn cs) b - 3)). change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (D8n : (8 | un)). { eapply Z.divide_trans; [|exact Hdn]. exists (2 ^ (ealign (kn cs) n - 3)). change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (Hshhi : shadow_off A + (ub + un) / 8 = S + un / 8).
  { unfold S. destruct D8b as [qb ->]. destruct D8n as [qn ->].
    rewrite Z.div_mul, <- Z.mul_add_distr_r, !Z.div_mul by lia. lia. }
  pose proof (kzero_x_sound0 E M (kn cs) (kn cs) sb sk sn HK HK Hkz) as (Hzero & _ & _). rewrite HSS, HSn in Hzero.
  (* [comment removed for export] *)
  assert (GONE : Forall (fun p => p = (b, n)) (List.filter (vis_here b n) (a_vis cs))).
  { apply Forall_forall. intros p Hp. apply filter_In in Hp as [_ Hp]. apply vis_here_eq. exact Hp. }
  set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _).
  (* [comment removed for export] *)
  assert (ALLOW_sub : forall z, in_allow E cs' z = true -> in_allow E cs z = true).
  { intros z Hz. unfold in_allow, in_vis, in_sh in *. unfold cs' in Hz; cbn [a_vis] in Hz.
    apply orb_true_iff in Hz. apply orb_true_iff.
    destruct Hz as [Hz|Hz]; [left|right]; apply existsb_exists in Hz as [q [Hq Hzq]]; apply filter_In in Hq as [Hq _];
      apply existsb_exists; exists q; split; assumption. }
  assert (ALLOW_eq : forall z, ~ (ub <= z < ub + un) -> ~ (S <= z < S + un / 8) -> in_allow E cs' z = in_allow E cs z).
  { intros z Hz1 Hz2. destruct (in_allow E cs' z) eqn:Ha'; [symmetry; apply ALLOW_sub; exact Ha'|].
    destruct (in_allow E cs z) eqn:Ha; [|reflexivity]. exfalso.
    unfold in_allow, in_vis, in_sh in Ha, Ha'. unfold cs' in Ha'; cbn [a_vis] in Ha'.
    apply orb_false_iff in Ha' as [Hv' Hs'].
    assert (Q : forall q, In q (a_vis cs) -> vis_here b n q = false ->
                 In q (List.filter (fun p => negb (vis_here b n p)) (a_vis cs))).
    { intros q Hq Hh. apply filter_In. split; [exact Hq | rewrite Hh; reflexivity]. }
    apply orb_true_iff in Ha. destruct Ha as [Ha|Ha]; apply existsb_exists in Ha as [q [Hq Hzq]].
    - destruct (vis_here b n q) eqn:Hh.
      + apply vis_here_eq in Hh. subst q. cbn [fst snd] in Hzq. apply andb_prop in Hzq as [Z1 Z2].
        apply Z.leb_le in Z1. apply Z.ltb_lt in Z2. apply Hz1. unfold ub, un. unfold uE in Z1, Z2. lia.
      + assert (X : existsb (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool
                      (List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) = true).
        { apply existsb_exists. exists q. split; [apply Q; assumption | exact Hzq]. }
        rewrite X in Hv'. discriminate.
    - destruct (vis_here b n q) eqn:Hh.
      + apply vis_here_eq in Hh. subst q. apply andb_prop in Hzq as [Z1 Z2].
        apply Z.leb_le in Z1. apply Z.ltb_lt in Z2. unfold sh_lo, sh_hi in Z1, Z2. cbn [fst snd] in Z1, Z2.
        apply Hz2. unfold S. unfold ub, un in *. unfold uE in Z1, Z2. rewrite Hshhi in Z2. unfold S in Z2. lia.
      + assert (X : existsb (fun p => (sh_lo E p <=? z) && (z <? sh_hi E p))%bool
                      (List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) = true).
        { apply existsb_exists. exists q. split; [apply Q; assumption | exact Hzq]. }
        rewrite X in Hs'. discriminate. }
  assert (HID_mono : forall a, hid E cs model a = true -> hid E cs' model a = true).
  { intros a Ha. unfold hid in *. apply orb_true_iff in Ha. apply orb_true_iff. destruct Ha as [Ha|Ha]; [left; exact Ha|right].
    apply negb_true_iff in Ha. apply negb_true_iff. destruct (vis E cs' model a) eqn:Hv; [|reflexivity].
    rewrite (vis_mono E cs' cs model a ALLOW_sub Hv) in Ha. discriminate. }
  assert (HID_eq : forall a, ~ (ub <= bv_unsigned a < ub + un) -> ~ (S <= bv_unsigned a < S + un / 8) ->
                   hid E cs' model a = hid E cs model a).
  { intros a H1 H2. unfold hid, vis. change (a_maps cs') with (a_maps cs). rewrite (ALLOW_eq _ H1 H2). reflexivity. }
  set (M' := Mr E cs' model FULL).
  assert (M_none : forall x, M x = None -> M' x = None).
  { intros x Hx. unfold M, M', Mr, mrestrict in *. destruct (hid E cs model x) eqn:Hh.
    - rewrite (HID_mono x Hh). reflexivity.
    - destruct (hid E cs' model x); [reflexivity | exact Hx]. }
  assert (M_eq : forall x, ~ (ub <= bv_unsigned x < ub + un) -> ~ (S <= bv_unsigned x < S + un / 8) -> M' x = M x).
  { intros x H1 H2. unfold M, M', Mr, mrestrict. rewrite (HID_eq x H1 H2). reflexivity. }
  (* [comment removed for export] *)
  set (k1 := kn_unfill (kn cs) bb bk n).
  set (Mmid := fun x : word => if ((ub <=? bv_unsigned x) && (bv_unsigned x <? ub + un))%bool then M' x else M x).
  assert (Mmid_out : forall x : word, bv_unsigned x < ub \/ ub + elenZ E n <= bv_unsigned x -> Mmid x = M x).
  { intros x Hx. unfold Mmid. unfold elenZ in Hx. fold un in Hx.
    destruct ((ub <=? bv_unsigned x) && (bv_unsigned x <? ub + un))%bool eqn:Hb; [|reflexivity].
    apply andb_prop in Hb as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2. lia. }
  assert (IMG : forall lo hi Mx, (forall x, M x = None -> Mx x = None) ->
            kentry_ok SEGS E M (KImg lo hi) -> kentry_ok SEGS E Mx (KImg lo hi)).
  { intros lo hi Mx Hn HKi. cbn [kentry_ok] in *. destruct HKi as (I1 & I2 & I3). split; [exact I1|]. split; [exact I2|].
    intros i Hi. apply Hn. apply I3. exact Hi. }
  assert (Mmid_none : forall x, M x = None -> Mmid x = None).
  { intros x Hx. unfold Mmid. destruct (_ && _)%bool; [apply M_none; exact Hx | exact Hx]. }
  assert (HK1 : know_ok SEGS E Mmid k1).
  { unfold k1, kn_unfill. cbv zeta. apply Forall_forall. intros K HinK. apply filter_In in HinK as [HinK Hkeep].
    pose proof (proj1 (Forall_forall _ _) HK K HinK) as HKK.
    apply orb_prop in Hkeep as [Himg|Hap].
    - destruct K; try discriminate. apply (IMG _ _ Mmid Mmid_none HKK).
    - rewrite kentry_apart_bp_eq in Hap. eapply kentry_apart_keep; [exact HK | exact HKK | exact Hap |]. rewrite HB. exact Mmid_out. }
  assert (HK2 : know_ok SEGS E M' (kn_unfill k1 sb sk sn)).
  { unfold kn_unfill. cbv zeta. apply Forall_forall. intros K HinK. apply filter_In in HinK as [HinK Hkeep].
    pose proof (proj1 (Forall_forall _ _) HK1 K HinK) as HKK.
    assert (HinK0 : In K (kn cs)) by (unfold k1, kn_unfill in HinK; apply filter_In in HinK as [HinK _]; exact HinK).
    apply orb_prop in Hkeep as [Himg|Hap].
    - destruct K; try discriminate. apply (IMG _ _ M' M_none). exact (proj1 (Forall_forall _ _) HK _ HinK0).
    - rewrite kentry_apart_bp_eq in Hap. eapply kentry_apart_keep; [exact HK1 | exact HKK | exact Hap |].
      rewrite HSS, HSn. intros x Hx. unfold Mmid.
      destruct ((ub <=? bv_unsigned x) && (bv_unsigned x <? ub + un))%bool eqn:Hb; [reflexivity|].
      apply M_eq; [|lia]. intros Hin. assert (X : ((ub <=? bv_unsigned x) && (bv_unsigned x <? ub + un))%bool = true); [|rewrite X in Hb; discriminate].
      apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  (* [comment removed for export] *)
  assert (HA : allowA E cs' = flat_map (allow1 E) (List.filter (fun p => negb (vis_here b n p)) (a_vis cs))
                               ++ flat_map (allow1 E) (a_ghost cs) ++ allow1 E (b, n)).
  { unfold allowA, cs'. cbn [a_vis a_ghost]. rewrite !flat_map_app. cbn [flat_map]. rewrite app_nil_r, app_assoc. reflexivity. }
  assert (HA0 : allowA E cs = flat_map (allow1 E) (a_vis cs) ++ flat_map (allow1 E) (a_ghost cs)).
  { unfold allowA. rewrite flat_map_app. reflexivity. }
  assert (HAB : A_bytes (allowA E cs') <= A_bytes (allowA E cs)).
  { rewrite HA, HA0, !A_bytes_app.
    rewrite (A_bytes_fm_split E (fun p => negb (vis_here b n p)) (a_vis cs)).
    assert (FF : List.filter (fun p => negb (negb (vis_here b n p))) (a_vis cs) = List.filter (vis_here b n) (a_vis cs)).
    { apply filter_ext. intros q. apply negb_involutive. }
    rewrite FF, (A_bytes_fm_here E b n _ GONE).
    assert (L1 : (1 <= length (List.filter (vis_here b n) (a_vis cs)))%nat).
    { apply existsb_exists in Hex as [q [Hq Hh]].
      assert (Hin : In q (List.filter (vis_here b n) (a_vis cs))) by (apply filter_In; split; assumption).
      destruct (List.filter (vis_here b n) (a_vis cs)); [destruct Hin | cbn; lia]. }
    pose proof (A_bytes_allow1_nonneg E (b, n)). nia. }
  assert (HPG : forall pg, page_allowedb (allowA E cs) pg = true -> page_allowedb (allowA E cs') pg = true).
  { intros pg Hp. unfold page_allowedb in *. apply existsb_exists in Hp as [iv [Hiv Hpg]]. apply existsb_exists.
    exists iv. split; [|exact Hpg]. rewrite HA. rewrite HA0 in Hiv. rewrite !in_app_iff in *.
    destruct Hiv as [Hiv|Hiv]; [|right; left; exact Hiv].
    apply in_flat_map in Hiv as [q [Hq Hiv]]. destruct (vis_here b n q) eqn:Hh.
    - apply vis_here_eq in Hh. subst q. right; right. exact Hiv.
    - left. apply in_flat_map. exists q. split; [|exact Hiv]. apply filter_In. split; [exact Hq | rewrite Hh; reflexivity]. }
  pose proof (co_minv _ _ _ _ _ HC) as HMI. pose proof (co_abytes _ _ _ _ _ HC) as HAB0. pose proof (co_zero _ _ _ _ _ HC) as HZ0.
  destruct HC; constructor; unfold cs'; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn s_regs s_log s_know mk_ss]; try assumption; try reflexivity.
  all: fold cs'.
  all: match goal with
       | |- know_ok _ _ _ _ => change (Mr E cs' model FULL) with M'; exact HK2
       | |- A_bytes _ <= _ => lia
       | |- MInv _ _ => destruct HMI as [N1 N2 N3 N4 N5]; constructor; try assumption; [intros pg Hpg; apply HPG; apply N3; exact Hpg | lia]
       | |- _ => idtac
       end.
  (* [comment removed for export] *) intros a H1 H2 H3 H4 H5.
    unfold in_ghost in H5. unfold cs' in H5; cbn [a_ghost] in H5. rewrite existsb_app in H5. apply orb_false_iff in H5 as [H5 H6].
    cbn [existsb fst snd] in H6. rewrite orb_false_r in H6.
    assert (NA : ~ (ub <= bv_unsigned a < ub + un)).
    { intros Hin. assert (X : ((uE E b <=? bv_unsigned a) && (bv_unsigned a <? uE E b + uE E n))%bool = true); [|rewrite X in H6; discriminate].
      unfold uE. fold ub un. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    destruct (hid E cs model a) eqn:Hh.
    + apply (HZ0 a Hh H2 H3 H4). unfold in_ghost. exact H5.
    + destruct (Z_le_dec S (bv_unsigned a)) as [L1|L1]; [destruct (Z_lt_dec (bv_unsigned a) (S + un / 8)) as [L2|L2]|].
      * (* [comment removed for export] *)
        pose proof (Hzero (bv_unsigned a - S) ltac:(lia)) as Z0.
        replace (S + (bv_unsigned a - S)) with (bv_unsigned a) in Z0 by lia. rewrite Z_to_bv_bv_unsigned in Z0.
        unfold M, Mr, mrestrict in Z0. rewrite Hh in Z0. exact Z0.
      * rewrite (HID_eq a NA ltac:(lia)) in H1. rewrite Hh in H1. discriminate.
      * rewrite (HID_eq a NA ltac:(lia)) in H1. rewrite Hh in H1. discriminate.
Qed.

Lemma havocbrk_sound : forall E cs R FULL model lo hi cs',
  cs_ok E cs R FULL model -> node_havocbrk nx0 cs lo hi = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model lo hi cs' HC H. unfold node_havocbrk in H.
  destruct (xlo (kn cs) (a_brk cs)) as [l|] eqn:Hl; [|discriminate].
  destruct (xhi (kn cs) (a_brk cs)) as [h|] eqn:Hh; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-.
  apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [Hf H1]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (xlo_sound SEGS E _ (kn cs) (a_brk cs) l (co_know _ _ _ _ _ HC) Hl) as L1.
  pose proof (xhi_sound SEGS E _ (kn cs) (a_brk cs) h (co_know _ _ _ _ _ HC) Hh) as L2.
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (v := nxt cs). set (E' := ext1 E v (vm_brk (m_vmmaps model))).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  pose proof (cs_ok_agree E E' cs R FULL model Hag Hf HC) as HC'.
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  assert (Hv : edenot E' (EVar v) = vm_brk (m_vmmaps model)) by (cbn [edenot]; unfold E'; apply ext1_at).
  pose proof (co_brk _ _ _ _ _ HC) as HB0.
  set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _).
  assert (HMr : Mr E' cs' model FULL = Mr E' cs model FULL) by reflexivity.
  assert (HA : allowA E' cs' = allowA E' cs) by reflexivity.
  destruct HC'; constructor; unfold cs'; rewrite ?HMr, ?HA;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know s_pc s_next] in *;
    try assumption; try reflexivity.
  - (* [comment removed for export] *) constructor; [|exact co_know0]. cbn [kentry_ok]. rewrite Hv, HB0. lia.
  - (* [comment removed for export] *) symmetry. exact Hv.
Qed.

(* [comment removed for export] *)
Lemma intro_sound : forall E cs R FULL model lo hi cs',
  cs_ok E cs R FULL model -> node_intro nx0 cs lo hi = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model lo hi cs' HC H. unfold node_intro in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-.
  apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [Hf H1].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (v := nxt cs). set (E' := ext1 E v (Z_to_bv 64 lo)).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  pose proof (cs_ok_agree E E' cs R FULL model Hag Hf HC) as HC'.
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  assert (Hv : bv_unsigned (edenot E' (EVar v)) = lo).
  { cbn [edenot]. unfold E'. rewrite ext1_at. unfold two64 in H3. apply u_small. lia. }
  set (cs' := with_ss _ _).
  assert (HMr : Mr E' cs' model FULL = Mr E' cs model FULL) by reflexivity.
  assert (HA : allowA E' cs' = allowA E' cs) by reflexivity.
  destruct HC'; constructor; unfold cs'; rewrite ?HMr, ?HA;
    cbn [with_ss a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know s_pc s_next] in *;
    try assumption; try reflexivity.
  - (* [comment removed for export] *) constructor; [|exact co_know0]. cbn [kentry_ok]. rewrite Hv. lia.
Qed.

(* [comment removed for export] *)
Section Rename.
  Variable m : list (nat * nat).
  Variables fw bw : list (option nat).
  Hypothesis Hfw : mk_fwd m = Some fw.
  Hypothesis Hbw : mk_bwd m = Some bw.

  Lemma mk_fwd_spec_gen : forall m0 t, mk_fwd m0 = Some t -> forall s d, nt_get t s = Some d <-> In (s, d) m0.
  Proof.
    induction m0 as [|[s0 d0] rest IH]; intros t H s d; cbn [mk_fwd] in H.
    - injection H as <-. unfold nt_get. cbn. split; [destruct s; discriminate | tauto].
    - destruct (mk_fwd rest) as [t0|] eqn:E0; [|discriminate].
      destruct (nt_get t0 s0) eqn:Eg; [discriminate|]. injection H as <-.
      rewrite nt_get_set. specialize (IH t0 eq_refl).
      destruct (Nat.eqb_spec s s0) as [->|NE].
      + split.
        * intros X. injection X as <-. left. reflexivity.
        * intros [X|X]; [congruence|]. apply IH in X. congruence.
      + rewrite IH. cbn. split; [tauto|]. intros [X|X]; [congruence|exact X].
  Qed.
  Lemma mk_bwd_spec_gen : forall m0 t, mk_bwd m0 = Some t -> forall s d, nt_get t d = Some s <-> In (s, d) m0.
  Proof.
    induction m0 as [|[s0 d0] rest IH]; intros t H s d; cbn [mk_bwd] in H.
    - injection H as <-. unfold nt_get. cbn. split; [destruct d; discriminate | tauto].
    - destruct (mk_bwd rest) as [t0|] eqn:E0; [|discriminate].
      destruct (nt_get t0 d0) eqn:Eg; [discriminate|]. injection H as <-.
      rewrite nt_get_set. specialize (IH t0 eq_refl).
      destruct (Nat.eqb_spec d d0) as [->|NE].
      + split.
        * intros X. injection X as <-. left. reflexivity.
        * intros [X|X]; [congruence|]. apply IH in X. congruence.
      + rewrite IH. cbn. split; [tauto|]. intros [X|X]; [congruence|exact X].
  Qed.
  Lemma fw_in : forall s d, nt_get fw s = Some d <-> In (s, d) m.
  Proof. exact (mk_fwd_spec_gen m fw Hfw). Qed.
  Lemma bw_in : forall s d, nt_get bw d = Some s <-> In (s, d) m.
  Proof. exact (mk_bwd_spec_gen m bw Hbw). Qed.

  Definition ren_env (E : env) : env :=
    Env (fun w => match nt_get bw w with Some s => ev E s | None => ev E w end) (eb E).
  Definition ren_ok (v : nat) : bool :=
    match nt_get fw v with Some _ => true | None => match nt_get bw v with Some _ => false | None => true end end.

  Lemma edenot_rename : forall E e, evars_all ren_ok e = true -> edenot (ren_env E) (erename fw e) = edenot E e.
  Proof.
    intros E e. induction e; cbn [evars_all erename edenot]; intros H;
      try reflexivity;
      try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity);
      try (rewrite (IHe H); reflexivity).
    unfold ren_ok in H. destruct (nt_get fw n) as [d|] eqn:Ef.
    - cbn [edenot ren_env ev]. destruct (nt_get bw d) as [s|] eqn:Eb.
      + apply bw_in in Eb. apply fw_in in Ef. pose proof (proj2 (fw_in _ _) Eb) as Ef'.
        assert (s = n) by (apply bw_in in Eb; apply bw_in in Ef; congruence). subst s. reflexivity.
      + exfalso. apply fw_in in Ef. apply (proj2 (bw_in _ _)) in Ef. congruence.
    - cbn [edenot ren_env ev]. destruct (nt_get bw n) as [s|] eqn:Eb; [discriminate|reflexivity].
  Qed.
End Rename.

Section RenameCS.
  Variable m : list (nat * nat).
  Variables fw bw : list (option nat).
  Hypothesis Hfw : mk_fwd m = Some fw.
  Hypothesis Hbw : mk_bwd m = Some bw.
  Variable gb : nat.
  Hypothesis Hgb : (nx0 <= gb)%nat.
  Hypothesis Hm : forallb (fun p => Nat.leb gb (fst p) && Nat.leb gb (snd p)) m = true.

  Let ER := edenot_rename m fw bw Hfw Hbw.

  Lemma ren_agree : forall E, env_agree gb E (ren_env bw E).
  Proof.
    intros E. split; [|reflexivity]. intros n Hn. cbn [ren_env ev].
    destruct (nt_get bw n) as [s|] eqn:Eb; [|reflexivity].
    apply (bw_in m bw Hbw) in Eb. exfalso.
    pose proof (proj1 (forallb_forall _ _) Hm (s, n) Eb) as X. cbn [fst snd] in X.
    apply andb_prop in X as [_ X]. apply Nat.leb_le in X. clear Hgb. lia.
  Qed.

  Lemma uE_rename : forall E e, evars_all (ren_ok fw bw) e = true -> uE (ren_env bw E) (erename fw e) = uE E e.
  Proof. intros. unfold uE. rewrite (ER E e H). reflexivity. Qed.

  Lemma regs_ok_rename : forall E sr R, forallb (evars_all (ren_ok fw bw)) sr = true -> regs_ok E sr R -> regs_ok (ren_env bw E) (map (erename fw) sr) R.
  Proof.
    intros E sr R Hsr HR r. rewrite (HR r). unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
    revert Hsr. generalize (ridx r) as i. clear HR r.
    induction sr as [|e t IH]; intros i Hsr; [destruct i; reflexivity|].
    cbn [forallb] in Hsr. apply andb_prop in Hsr as [He Ht].
    destruct i as [|i]; cbn [map nth]; [symmetry; exact (ER E e He) | apply IH; exact Ht].
  Qed.

  Lemma eb_ren : forall E, eb (ren_env bw E) = eb E.
  Proof. reflexivity. Qed.

  Lemma kentry_ok_rename : forall E M K, kvars_all (ren_ok fw bw) K = true -> kentry_ok SEGS E M K -> kentry_ok SEGS (ren_env bw E) M (krename fw K).
  Proof.
    intros E M K HK Hk.
    destruct K as [[ab ak] w v|[ab ak] n|[ab ak] n k|lo hi|ae am|re rlo rhi|[ab ak] wn|[b1 k1] dn1 [b2 k2] dn2|[ab ak] n fc|[ab ak] n];
      unfold krename, arename in *; cbn [kvars_all kentry_ok a_base a_off] in *;
      repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H as [? H] end;
      unfold flat, estart, elenZ, adenot in *; cbn [a_base a_off] in *;
      rewrite ?eb_ren; rewrite ?(ER E) by assumption; exact Hk.
  Qed.

  Lemma know_ok_rename : forall E M k, forallb (kvars_all (ren_ok fw bw)) k = true ->
    know_ok SEGS E M k -> know_ok SEGS (ren_env bw E) M (map (krename fw) k).
  Proof.
    intros E M k. induction k as [|K rest IH]; intros Hv Hk; [constructor|].
    cbn [forallb] in Hv. apply andb_prop in Hv as [H1 H2]. apply Forall_cons_iff in Hk as [HK Hr].
    cbn [map]. constructor; [apply kentry_ok_rename; assumption | apply IH; assumption].
  Qed.

  Definition pvars_all (l : list (expr * expr)) : bool :=
    forallb (fun p => evars_all (ren_ok fw bw) (fst p) && evars_all (ren_ok fw bw) (snd p)) l.

  Lemma allowA_rename : forall E cs nx,
    pvars_all (a_vis cs) = true -> pvars_all (a_ghost cs) = true ->
    allowA (ren_env bw E) (rename_cs fw cs nx) = allowA E cs.
  Proof.
    intros E cs nx Hv Hg. unfold allowA. cbn [rename_cs a_vis a_ghost]. rewrite <- map_app, !flat_map_concat_map, map_map. f_equal.
    apply map_ext_in. intros p Hin.
    assert (Hp : (evars_all (ren_ok fw bw) (fst p) && evars_all (ren_ok fw bw) (snd p))%bool = true).
    { apply in_app_iff in Hin as [Hin|Hin]; [exact (proj1 (forallb_forall _ _) Hv p Hin) | exact (proj1 (forallb_forall _ _) Hg p Hin)]. }
    apply andb_prop in Hp as [H1 H2].
    unfold allow1, sh_lo, sh_hi, prename. cbn [fst snd]. rewrite !(uE_rename E) by assumption. reflexivity.
  Qed.

  Lemma existsb_map : forall (X Y : Type) (f : X -> Y) (P : Y -> bool) l, existsb P (map f l) = existsb (fun x => P (f x)) l.
  Proof. intros X Y f P l. induction l as [|x r IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
  Lemma existsb_ext_in : forall (X : Type) (P Q : X -> bool) l, (forall x, In x l -> P x = Q x) -> existsb P l = existsb Q l.
  Proof. intros X P Q l H. induction l as [|x r IH]; [reflexivity|]. cbn. rewrite (H x (or_introl eq_refl)), IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy. Qed.

  Lemma in_allow_rename : forall E cs nx, pvars_all (a_vis cs) = true ->
    in_allow (ren_env bw E) (rename_cs fw cs nx) = in_allow E cs.
  Proof.
    intros E cs nx Hv. apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh. cbn [rename_cs a_vis].
    rewrite !existsb_map. f_equal; apply existsb_ext_in; intros p Hin;
      pose proof (proj1 (forallb_forall _ _) Hv p Hin) as Hp; apply andb_prop in Hp as [H1 H2];
      unfold sh_lo, sh_hi, prename; cbn [fst snd]; rewrite !(uE_rename E) by assumption; reflexivity.
  Qed.

  Lemma in_ghost_rename : forall E cs nx, pvars_all (a_ghost cs) = true ->
    in_ghost (ren_env bw E) (rename_cs fw cs nx) = in_ghost E cs.
  Proof.
    intros E cs nx Hg. apply functional_extensionality. intros z. unfold in_ghost. cbn [rename_cs a_ghost].
    rewrite existsb_map. apply existsb_ext_in. intros p Hin.
    pose proof (proj1 (forallb_forall _ _) Hg p Hin) as Hp. apply andb_prop in Hp as [H1 H2].
    unfold prename. cbn [fst snd]. rewrite !(uE_rename E) by assumption. reflexivity.
  Qed.

  Lemma hid_rename : forall E cs nx model, pvars_all (a_vis cs) = true ->
    hid (ren_env bw E) (rename_cs fw cs nx) model = hid E cs model.
  Proof.
    intros E cs nx model Hv. apply functional_extensionality. intros a. unfold hid, vis.
    rewrite (in_allow_rename E cs nx Hv). rewrite <- (argH_agree E (ren_env bw E) a); [reflexivity|].
    eapply env_agree_le; [apply ren_agree | exact Hgb].
  Qed.

  Lemma maps_match_rename : forall E ms l,
    forallb (fun m0 => evars_all (ren_ok fw bw) (am_base m0) && evars_all (ren_ok fw bw) (am_len m0)) ms = true ->
    maps_match E ms l -> maps_match (ren_env bw E) (map (mrename fw) ms) l.
  Proof.
    intros E ms. induction ms as [|[mb ml mk] ms IH]; intros l H HM; cbn [maps_match map] in *; [exact HM|].
    cbn [forallb am_base am_len] in H. apply andb_prop in H as [Hm0 Hr]. apply andb_prop in Hm0 as [H1 H2].
    unfold mrename, is_fog, amap_den in *. cbn [am_kind am_base am_len] in *.
    rewrite ?(uE_rename E) by assumption. rewrite ?(ER E) by assumption.
    destruct (is_tok_kind mk).
    - destruct HM as [HM|(iv & l' & -> & Hsz & HM)]; [left; exact (IH _ Hr HM) | right].
      exists iv, l'. split; [reflexivity|]. split; [exact Hsz | exact (IH _ Hr HM)].
    - destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | exact (IH _ Hr HM)].
  Qed.
  (* [comment removed for export] *)
  Lemma holes_rename : forall E y l ms,
    forallb (fun m0 => evars_all (ren_ok fw bw) (am_base m0) && evars_all (ren_ok fw bw) (am_len m0)) ms = true ->
    Forall (hole_ok E y l) ms -> Forall (hole_ok (ren_env bw E) y l) (map (mrename fw) ms).
  Proof.
    intros E y l ms H HF. apply Forall_forall. intros m0 Hin Hk. apply in_map_iff in Hin as (m1 & <- & Hin).
    pose proof (proj1 (forallb_forall _ _) H m1 Hin) as Hmm. apply andb_prop in Hmm as [H1 H2].
    unfold hole_ok, is_hole, mrename in *. cbn [am_base am_len am_kind] in *. rewrite !(uE_rename E) by assumption.
    exact (proj1 (Forall_forall _ _) HF m1 Hin Hk).
  Qed.

  Lemma fds_ok_rename : forall E f model,
    match f with FdFile _ l o => evars_all (ren_ok fw bw) l && evars_all (ren_ok fw bw) o | _ => true end%bool = true ->
    fds_ok E f model -> fds_ok (ren_env bw E) (frename fw f) model.
  Proof.
    intros E f model Hv H. destruct f as [|k len off|]; try exact H.
    apply andb_prop in Hv as [Hl Ho]. cbn [frename].
    destruct H as [p [c (H1 & H2 & H3 & H4 & H5)]]. exists p, c.
    rewrite !(uE_rename E) by assumption. rewrite !(ER E) by assumption. rewrite eb_ren. repeat split; assumption.
  Qed.

  Lemma cs_ok_rename : forall E cs R FULL model nx,
    csvars_all (ren_ok fw bw) cs = true -> s_log (a_ss cs) = [] ->
    cs_ok E cs R FULL model -> cs_ok (ren_env bw E) (rename_cs fw cs nx) R FULL model.
  Proof.
    intros E cs R FULL model nx Hv Hlog HC.
    unfold csvars_all in Hv. apply andb_prop in Hv as [Hv Hprops].   (* [comment removed for export] *)
    apply andb_prop in Hv as [Hv Hfd]. apply andb_prop in Hv as [Hv Hbrk]. apply andb_prop in Hv as [Hv Hgh].
    apply andb_prop in Hv as [Hv Hvis]. apply andb_prop in Hv as [Hv Hmaps]. apply andb_prop in Hv as [Hregs Hkn].
    pose proof (hid_rename E cs nx model Hvis) as HH.
    pose proof (allowA_rename E cs nx Hvis Hgh) as HA.
    assert (HMr : Mr (ren_env bw E) (rename_cs fw cs nx) model FULL = Mr E cs model FULL) by (unfold Mr; rewrite HH; reflexivity).
    destruct HC; constructor; cbn [rename_cs a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know s_pc s_next] in *;
      rewrite ?HA, ?HMr; try assumption.
    - apply regs_ok_rename; assumption.
    - reflexivity.
    - apply know_ok_rename; assumption.
    - apply fds_ok_rename; assumption.
    - apply maps_match_rename; assumption.
    - apply holes_rename; assumption.
    - (* [comment removed for export] *) apply Forall_forall. intros m0 Hin Hk. apply in_map_iff in Hin as (m1 & <- & Hin).
      pose proof (proj1 (forallb_forall _ _) Hmaps m1 Hin) as Hmm. apply andb_prop in Hmm as [H1 H2].
      unfold amap_den, mrename in *. cbn [am_base am_len am_kind] in *. rewrite !(ER E) by assumption.
      exact (proj1 (Forall_forall _ _) co_none0 m1 Hin Hk).
    - (* [comment removed for export] *) apply Forall_forall. intros m0 Hin Hk a Ha. apply in_map_iff in Hin as (m1 & <- & Hin).
      pose proof (proj1 (forallb_forall _ _) Hmaps m1 Hin) as Hmm. apply andb_prop in Hmm as [H1 H2].
      unfold mrename in *. cbn [am_base am_len am_kind] in *. rewrite !(ER E) in Ha by assumption.
      exact (proj1 (Forall_forall _ _) co_kinds0 m1 Hin Hk a Ha).
    - (* [comment removed for export] *) rewrite (e_sp0_agree _ _ _ (ren_agree E) Hgb). assumption.
    - rewrite (ER E) by assumption. assumption.
    - intros a. rewrite HH, (in_ghost_rename E cs nx Hgh). exact (co_zero0 a).
    - eapply SINV_agree; [eapply env_agree_le; [apply ren_agree | exact Hgb] | assumption].
  Qed.

  (* [comment removed for export] *)
  Lemma props_ok_rename : forall E M ps,
    forallb (fun g => forallb (evars_all (ren_ok fw bw)) (g_args g)) ps = true ->
    props_ok E M ps -> props_ok (ren_env bw E) M (map (grename fw) ps).
  Proof.
    intros E M ps Hv HP. unfold props_ok in *. apply Forall_forall. intros g' Hin.
    apply in_map_iff in Hin as (g & <- & Hin).
    pose proof (proj1 (Forall_forall _ _) HP g Hin) as Hg. pose proof (proj1 (forallb_forall _ _) Hv g Hin) as Hvg.
    unfold gholds, grename in *. cbn [g_id g_args].
    replace (map (uE (ren_env bw E)) (map (erename fw) (g_args g))) with (map (uE E) (g_args g)); [exact Hg|].
    rewrite map_map. apply map_ext_in. intros a Ha. symmetry. apply uE_rename.
    exact (proj1 (forallb_forall _ _) Hvg a Ha).
  Qed.
  Lemma Mr_rename : forall E cs nx model FULL,
    forallb (fun p => evars_all (ren_ok fw bw) (fst p) && evars_all (ren_ok fw bw) (snd p)) (a_vis cs) = true ->
    Mr (ren_env bw E) (rename_cs fw cs nx) model FULL = Mr E cs model FULL.
  Proof. intros E cs nx model FULL Hvis. unfold Mr. rewrite (hid_rename E cs nx model Hvis). reflexivity. Qed.
End RenameCS.

Lemma rename_sound : forall gb E cs R FULL model m cs',
  (nx0 <= gb)%nat -> cs_ok E cs R FULL model -> node_rename gb cs m = Some cs' ->
  exists E', env_agree gb E E' /\ cs_ok E' cs' R FULL model /\ pc cs' = pc cs
    /\ (props_ok E (Mr E cs model FULL) (a_props cs) -> props_ok E' (Mr E' cs' model FULL) (a_props cs')).   (* [comment removed for export] *)
Proof.
  intros gb E cs R FULL model m cs' Hgb HC H. unfold node_rename in H.
  destruct (forallb (fun p => Nat.leb gb (fst p) && Nat.leb gb (snd p)) m) eqn:Hm; [|discriminate].
  destruct (mk_fwd m) as [fw|] eqn:Hfw; [|discriminate].
  destruct (mk_bwd m) as [bw|] eqn:Hbw; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-. apply andb_prop in Hc as [Hv Hlog].
  exists (ren_env bw E). split; [exact (ren_agree m bw Hbw gb Hm E)|].
  match goal with |- cs_ok _ (with_ss _ (mk_ss _ _ _ ?NX)) _ _ _ /\ _ =>
    change (with_ss _ (mk_ss _ _ _ NX)) with (rename_cs fw cs NX) end.
  split; [|split; [reflexivity|]].
  - apply (cs_ok_rename m fw bw Hfw Hbw gb Hgb Hm); [exact Hv | exact (co_log _ _ _ _ _ HC) | exact HC].
  - intros HP. pose proof Hv as Hv'. unfold csvars_all in Hv'. apply andb_prop in Hv' as [Hv' Hprops].
    apply andb_prop in Hv' as [Hv' _]. apply andb_prop in Hv' as [Hv' _]. apply andb_prop in Hv' as [Hv' _].
    apply andb_prop in Hv' as [Hv' Hvis].
    first [ rewrite (Mr_rename m fw bw Hfw Hbw gb E cs _ model FULL Hvis) | rewrite (Mr_rename m fw bw Hfw Hbw gb Hgb E cs _ model FULL Hvis) | rewrite (Mr_rename m fw bw Hfw Hbw gb Hgb Hm E cs _ model FULL Hvis) | rewrite (Mr_rename m fw bw Hfw Hbw gb Hm E cs _ model FULL Hvis) ]. cbn [rename_cs a_props].
    first [ apply (props_ok_rename m fw bw Hfw Hbw); [exact Hprops | exact HP] | apply (props_ok_rename m fw bw Hfw Hbw gb); [exact Hprops | exact HP] | apply (props_ok_rename m fw bw Hfw Hbw gb Hgb Hm); [exact Hprops | exact HP] | apply (props_ok_rename m fw bw Hfw Hbw gb Hm); [exact Hprops | exact HP] ].
Qed.

Lemma compact_sound : forall gb E cs R FULL model cs',
  (nx0 <= gb)%nat -> cs_ok E cs R FULL model -> node_compact gb cs = Some cs' ->
  exists E', env_agree gb E E' /\ cs_ok E' cs' R FULL model /\ pc cs' = pc cs
    /\ (props_ok E (Mr E cs model FULL) (a_props cs) -> props_ok E' (Mr E' cs' model FULL) (a_props cs')).
Proof. intros gb E cs R FULL model cs' Hgb HC H. unfold node_compact in H. eapply rename_sound; eassumption. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma abstractcell_sound : forall E cs R FULL model b n cs',
  cs_ok E cs R FULL model -> node_abstractcell A cs b n = Some cs' -> cs_ok E cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model b n cs' HC H. unfold node_abstractcell in H.
  destruct (split_lit b) as [bb bo]. cbv zeta in H.
  destruct (kunk_covered A (kn cs) (KUnk (SA bb bo) (ELit n))) eqn:Hcov; [|discriminate].
  injection H as <-. split; [|apply pc_set_kn].
  apply cs_ok_set_kn; [exact HC|]. constructor.
  - eapply kunk_covered_sound; [exact (co_know _ _ _ _ _ HC) | exact Hcov].
  - eapply know_ok_cutout; [exact (co_know _ _ _ _ _ HC) | intros; reflexivity].
Qed.

Lemma hw_apply_true_incl : forall r a x K, In K (hw_apply r a x true) -> In K r.
Proof.
  induction r as [|X r IH]; intros a x K H; [exact H|]. cbn [hw_apply] in H.
  destruct X as [a' w v| | | | | | | | |]; cbn in H;
    try (destruct H as [H|H]; [left; exact H | right; eapply IH; exact H]).
  destruct (saddr_eqb a' a); [right; eapply IH; exact H|].
  destruct H as [H|H]; [left; exact H | right; eapply IH; exact H].
Qed.

Lemma hw_apply_true_vars : forall r a x b, AP.kn_vars_lt b r = true -> AP.kn_vars_lt b (hw_apply r a x true) = true.
Proof.
  induction r as [|X r IH]; intros a x b H; [reflexivity|]. cbn [AP.kn_vars_lt] in H. apply andb_prop in H as [HX Hr].
  cbn [hw_apply]. destruct X as [a' w v| | | | | | | | |]; cbn [AP.kn_vars_lt]; rewrite ?HX, ?(IH a x b Hr); try reflexivity.
  destruct (saddr_eqb a' a); [exact (IH a x b Hr)|]. cbn [AP.kn_vars_lt]. rewrite HX, (IH a x b Hr). reflexivity.
Qed.

Lemma hw_apply_ok : forall E M k a x,
  know_ok SEGS E M k -> AP.kn_vars_lt x k = true ->
  know_ok SEGS (upd E x (edenot E (hw_val k a))) M (hw_apply k a x false)
  /\ AP.kn_vars_lt (Datatypes.S x) (hw_apply k a x false) = true.
Proof.
  intros E M k a x. induction k as [|X r IH]; intros HK Hv.
  - split; [constructor | reflexivity].
  - apply Forall_cons_iff in HK as [HX Hr]. cbn [AP.kn_vars_lt] in Hv. apply andb_prop in Hv as [HvX Hvr].
    assert (AG : forall e, env_agree x E (upd E x e)) by (intros; apply upd_agree).
    assert (KEEP : forall e, kentry_ok SEGS (upd E x e) M X).
    { intros e. apply (@Forall_inv _ (kentry_ok SEGS (upd E x e) M) X []).
      eapply (know_ok_agree' x); [apply AG | | constructor; [exact HX | constructor]].
      cbn [AP.kn_vars_lt]. rewrite HvX. reflexivity. }
    assert (KEEPV : AP.kentry_vars_lt (Datatypes.S x) X = true) by (eapply kentry_vars_lt_mono; [exact HvX | lia]).
    cbn [hw_apply hw_val].
    destruct X as [a' w v| | | | | | | | |];
      try (destruct (IH Hr Hvr) as [IH1 IH2]; split; [constructor; [apply KEEP | exact IH1] | cbn [AP.kn_vars_lt]; rewrite KEEPV, IH2; reflexivity]).
    destruct (saddr_eqb a' a) eqn:Hs.
    + (* [comment removed for export] *)
      split.
      * constructor.
        -- cbn [kentry_ok] in HX |- *. destruct HX as (Hw & Hf & Hrd).
           cbn [AP.kentry_vars_lt AP.saddr_vars_lt] in HvX. apply andb_prop in HvX as [Hva Hvv].
           assert (Ea : adenot (upd E x (edenot E v)) a' = adenot E a').
           { unfold adenot. rewrite <- (edenot_agree' x E _ (a_base a') (AG _) Hva). reflexivity. }
           assert (Es : estart (upd E x (edenot E v)) a' = estart E a').
           { unfold estart. rewrite <- (edenot_agree' x E _ (a_base a') (AG _) Hva). reflexivity. }
           split; [exact Hw|]. split; [unfold flat in *; rewrite ?Es; exact Hf|].
           rewrite Ea. cbn [edenot]. rewrite upd_at. exact Hrd.
        -- eapply (know_ok_agree' x); [apply AG | apply hw_apply_true_vars; exact Hvr |].
           apply Forall_forall. intros K HK'. apply hw_apply_true_incl in HK'. exact (proj1 (Forall_forall _ _) Hr K HK').
      * cbn [AP.kn_vars_lt AP.kentry_vars_lt]. cbn [AP.kentry_vars_lt] in KEEPV. apply andb_prop in KEEPV as [Ka _].
        rewrite Ka. cbn [AP.expr_vars_lt]. replace (Nat.ltb x (Datatypes.S x)) with true by (symmetry; apply Nat.ltb_lt; lia). cbn [andb].
        eapply kn_vars_lt_mono'; [apply hw_apply_true_vars; exact Hvr | lia].
    + destruct (IH Hr Hvr) as [IH1 IH2]. split; [constructor; [apply KEEP | exact IH1] | cbn [AP.kn_vars_lt]; rewrite KEEPV, IH2; reflexivity].
Qed.

Lemma hw_go_ok : forall bs E M k x,
  know_ok SEGS E M k -> AP.kn_vars_lt x k = true ->
  exists E', env_agree x E E' /\ know_ok SEGS E' M (hw_go k bs x) /\ AP.kn_vars_lt (x + length bs)%nat (hw_go k bs x) = true.
Proof.
  induction bs as [|b r IH]; intros E M k x HK Hv.
  - exists E. split; [apply env_agree_refl|]. cbn [hw_go length]. rewrite Nat.add_0_r. split; assumption.
  - cbn [hw_go length]. destruct (hw_apply_ok E M k (sa_of b) x HK Hv) as [H1 H2].
    destruct (IH _ M _ (Datatypes.S x) H1 H2) as (E' & Hag & HK' & Hv').
    exists E'. split; [|split; [exact HK' | rewrite <- Nat.add_succ_comm; exact Hv']].
    apply (env_agree_trans _ _ (upd E x (edenot E (hw_val k (sa_of b)))) _); [apply upd_agree | eapply env_agree_le; [exact Hag | lia]].
Qed.

Lemma havocwords_sound : forall E cs R FULL model bs cs',
  cs_ok E cs R FULL model -> node_havocwords nx0 cs bs = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model bs cs' HC H. unfold node_havocwords in H.
  destruct (fresh_ok nx0 cs) eqn:Hf; [|discriminate]. injection H as <-.
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  destruct (hw_go_ok bs E (Mr E cs model FULL) (kn cs) (nxt cs) (co_know _ _ _ _ _ HC)) as (E' & Hag & HK' & _).
  { rewrite kn_vars_lt_eq. rewrite <- kn_vars_lt_eq. exact Fkn. }
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  pose proof (cs_ok_agree E E' cs R FULL model Hag Hf HC) as HC2.
  replace (with_ss cs (mk_ss (s_pc (a_ss cs)) (s_regs (a_ss cs)) (hw_go (s_know (a_ss cs)) bs (s_next (a_ss cs))) (s_next (a_ss cs) + length bs)))
    with (set_kn (bump cs (length bs)) (hw_go (kn cs) bs (nxt cs))) by reflexivity.
  apply cs_ok_set_kn.
  - destruct HC2; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset];
      try assumption; reflexivity.
  - unfold Mr. change (hid E' (bump cs (length bs)) model) with (hid E' cs model).
    rewrite (hid_agree (nxt cs) E E' cs model Hag Fle Fallow). exact HK'.
Qed.

(* [comment removed for export] *)
Lemma respell_ok_sound : forall E M k a e,
  know_ok SEGS E M k -> respell_ok k a e = true -> edenot E a = edenot E e.
Proof.
  intros E M k a e HK H. unfold respell_ok in H.
  destruct (decide_branch k BC_EQ a e) as [[|]|] eqn:Hd.
  - pose proof (decide_branch_sound SEGS E M k BC_EQ a e true HK Hd) as Heq. cbn [branch_taken] in Heq. apply bv_eqb_eq in Heq. exact Heq.
  - destruct (erange k (mkAlu ALU_SUB a e)) as [[lo hi]|] eqn:Hr; [|discriminate].
    apply andb_prop in H as [H0 H1]. apply Z.eqb_eq in H0. apply Z.eqb_eq in H1. subst lo hi.
    pose proof (erange_sound SEGS E M k _ 0 0 HK Hr) as Hb. rewrite mkAlu_denot in Hb.
    cbn [alu64 alu] in Hb. rewrite bv_sub_unsigned in Hb. unfold bv_wrap in Hb.
    pose proof (u64_range (edenot E a)) as Ra. pose proof (u64_range (edenot E e)) as Re.
    apply bv_eq. change (bv_modulus 64) with (2 ^ 64)%Z in Hb. unfold two64 in *.
    assert (Hm : ((bv_unsigned (edenot E a) - bv_unsigned (edenot E e)) mod 2 ^ 64 = 0)%Z) by lia.
    apply Z.mod_divide in Hm; [|lia]. destruct Hm as [q Hq]. assert (q = 0)%Z by nia. subst q. lia.
  - destruct (erange k (mkAlu ALU_SUB a e)) as [[lo hi]|] eqn:Hr; [|discriminate].
    apply andb_prop in H as [H0 H1]. apply Z.eqb_eq in H0. apply Z.eqb_eq in H1. subst lo hi.
    pose proof (erange_sound SEGS E M k _ 0 0 HK Hr) as Hb. rewrite mkAlu_denot in Hb.
    cbn [alu64 alu] in Hb. rewrite bv_sub_unsigned in Hb. unfold bv_wrap in Hb.
    pose proof (u64_range (edenot E a)) as Ra. pose proof (u64_range (edenot E e)) as Re.
    apply bv_eq. change (bv_modulus 64) with (2 ^ 64)%Z in Hb. unfold two64 in *.
    assert (Hm : ((bv_unsigned (edenot E a) - bv_unsigned (edenot E e)) mod 2 ^ 64 = 0)%Z) by lia.
    apply Z.mod_divide in Hm; [|lia]. destruct Hm as [q Hq]. assert (q = 0)%Z by nia. subst q. lia.
Qed.
Lemma respell_sound : forall E cs R FULL model r e cs',
  cs_ok E cs R FULL model -> node_respell cs r e = Some cs' -> cs_ok E cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model r e cs' HC H. unfold node_respell in H.
  destruct (Nat.ltb 0 r && Nat.ltb r 32 && AP.expr_vars_lt (nxt cs) e && respell_ok (kn cs) (reg cs r) e)%bool eqn:Hc; [|discriminate].
  injection H as <-.
  apply andb_prop in Hc as [Hc Hok]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [H1 H2]. apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2.
  pose proof (respell_ok_sound E _ (kn cs) (reg cs r) e (co_know _ _ _ _ _ HC) Hok) as Heq.
  split; [|reflexivity].
  destruct HC; constructor; cbn [set_reg with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset]; try assumption; try reflexivity.
  apply regs_ok_respell; [assumption | lia | unfold reg in Heq; symmetry; exact Heq].
Qed.

Lemma self_jump_word : forall ms,
  ms_svc_pending ms = None -> fetch_word SEGS (ms_pc ms) = Some (Z_to_bv 32 SPIN_WORD) ->
  is_self_jump SEGS ms = true.
Proof. intros ms Hs Hf. unfold is_self_jump. rewrite Hs, Hf. vm_compute. reflexivity. Qed.

Lemma node_spin_sound : forall cs E R FULL model,
  cs_ok E cs R FULL model -> node_spin SEGS cs = true ->
  srealizes SEGS (cfg R (pc cs) FULL model) t_nil.
Proof.
  intros cs E R FULL model HC Hn. unfold node_spin in Hn.
  apply andb_prop in Hn as [Hsj Hn].
  apply andb_prop in Hn as [Hn Hw]. apply andb_prop in Hn as [H0 H4].
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hf; [|discriminate].
  apply Z.eqb_eq in Hw.
  assert (Hw' : w = Z_to_bv 32 SPIN_WORD).
  { apply bv_eq. rewrite Hw. reflexivity. }
  subst w.
  apply srz_spin.
  - apply is_self_jump_to_spin. apply self_jump_word; [reflexivity | exact Hf].
  - exact (co_halt _ _ _ _ _ HC).
  - exact Hsj.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma regs_match_s_sound : forall E M k rs ts R,
  know_ok SEGS E M k -> regs_match_s k rs ts = true -> regs_ok E rs R -> regs_ok E ts R.
Proof.
  intros E M k rs ts R HK H HR.
  assert (G : forall i, edenot E (nth i rs (ELit 0)) = edenot E (nth i ts (ELit 0))).
  { revert ts H. clear HR. induction rs as [|r rs IH]; intros [|t ts] H i; cbn [regs_match_s] in H; try discriminate.
    - reflexivity.
    - apply andb_prop in H as [H1 H2]. destruct i as [|i]; cbn [nth]; [|exact (IH ts H2 i)].
      destruct (expr_eqb r t) eqn:He; [apply expr_eqb_eq in He; subst; reflexivity|].
      eapply respell_ok_sound; [exact HK | exact H1]. }
  intros r. rewrite (HR r). unfold sr_get. destruct (bv_eqb r 0); [reflexivity | apply G].
Qed.

Lemma entails_t_sound : forall E cs T R FULL model,
  cs_ok E cs R FULL model -> entails_t A cs T = true ->
  cs_ok E T R FULL model /\ pc T = pc cs /\ length (s_regs (a_ss T)) = 32%nat /\ hid E T model = hid E cs model.
Proof.
  intros E cs T R FULL model HC H. unfold entails_t in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  rename H into Hpc. apply Z.eqb_eq in Hpc.
  match goal with Hl : match s_log (a_ss T) with _ => _ end = true |- _ => rename Hl into HL; destruct (s_log (a_ss T)) eqn:HL'; [clear HL; rename HL' into HL|discriminate] end.
  match goal with Hl : match s_resv (a_ss T) with _ => _ end = true |- _ => clear Hl end.
  match goal with Hl : Nat.eqb (length _) 32 = true |- _ => apply Nat.eqb_eq in Hl; rename Hl into Hlen end.
  match goal with Hr : regs_match_s _ _ _ = true |- _ => rename Hr into Hregs end.
  match goal with Hm : list_eqb amap_eqb _ _ = true |- _ => apply (list_eqb_eq amap_eqb amap_eqb_eq) in Hm; rename Hm into Hmaps end.
  match goal with Ha : list_eqb pair_eqb (a_vis cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ha; rename Ha into Hallow end.
  match goal with Hg : list_eqb pair_eqb (a_ghost cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hg; rename Hg into Hghost end.
  match goal with Hb : ematch_s _ (a_brk cs) _ = true |- _ => rename Hb into Hbrk end.
  match goal with Hf : afd_match_s _ _ _ = true |- _ => rename Hf into Hfd end.
  match goal with Ht : Bool.eqb _ _ = true |- _ => apply eqb_prop in Ht; rename Ht into Htid end.
  match goal with Hk : kn_incl_s _ _ (kn T) = true |- _ => rename Hk into Hkn end.
  repeat match goal with Hz : Z.leb _ _ = true |- _ => apply Z.leb_le in Hz end.
  assert (HA : allowA E T = allowA E cs) by (unfold allowA; rewrite Hallow, Hghost; reflexivity).
  assert (HH : hid E T model = hid E cs model) by (apply hid_ext; symmetry; exact Hallow).
  (* [comment removed for export] *)
  assert (EM : forall a e, ematch_s (kn cs) a e = true -> edenot E a = edenot E e).
  { intros a e Hm. unfold ematch_s in Hm. destruct (expr_eqb a e) eqn:He; [apply expr_eqb_eq in He; subst; reflexivity|].
    eapply respell_ok_sound; [exact (co_know _ _ _ _ _ HC) | exact Hm]. }
  pose proof (EM _ _ Hbrk) as Ebrk.
  assert (Efd : fds_ok E (a_fd T) model).
  { pose proof (co_fds _ _ _ _ _ HC) as F. destruct (a_fd cs) as [|fk fl fo|]; destruct (a_fd T) as [|fk' fl' fo'|]; try discriminate Hfd; try exact F.
    cbn [afd_match_s] in Hfd. apply andb_prop in Hfd as [Hfd Ho]. apply andb_prop in Hfd as [Hk Hl]. apply Nat.eqb_eq in Hk. subst fk'.
    unfold fds_ok in F |- *. unfold uE in *. rewrite <- (EM _ _ Hl), <- (EM _ _ Ho). exact F. }
  split; [|split; [symmetry; exact Hpc | split; [exact Hlen | exact HH]]].
  destruct HC; constructor; rewrite <- ?Hmaps, <- ?Hallow, <- ?Hghost, <- ?Ebrk, <- ?Htid, ?HA; try assumption.
  - eapply regs_match_s_sound; [exact co_know0 | exact Hregs | exact co_regs0].
  - unfold Mr. rewrite HH. eapply kn_incl_s_sound; [exact co_know0 | exact Hkn].
  - eapply holes_mono; [exact co_holes0 | lia].
  - lia.
  - lia.
  - lia.
  - intros a. rewrite HH. replace (in_ghost E T) with (in_ghost E cs) by (unfold in_ghost; rewrite Hghost; reflexivity). exact (co_zero0 a).
Qed.

Lemma entails_s_sound : forall lo hi hints E cs inv sg R FULL model,
  cs_ok E cs R FULL model -> entails_s A lo hi hints cs inv = Some sg -> (nx0 <= lo)%nat -> s_log (a_ss inv) = [] ->
  env_agree lo E (updl E sg) /\ cs_ok (updl E sg) inv R FULL model /\ pc inv = pc cs /\ length (s_regs (a_ss inv)) = 32%nat
  /\ hid (updl E sg) inv model = hid E cs model.
Proof.
  intros lo hi hints E cs inv sg R FULL model HC H Hlo Hlog. unfold entails_s in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection H as Hsg. rewrite Hsg in Hc.
  apply andb_prop in Hc as [Hdom Hent].
  pose proof (sg_dom_in_ge lo hi sg Hdom) as Hge.
  destruct (entails_t_sound E cs (insts sg inv) R FULL model HC Hent) as (HC' & Hpc & Hlen & HH).
  assert (Hdg : sg_dom_ge nx0 sg = true).
  { unfold sg_dom_ge in *; apply forallb_forall; intros p Hp;
    pose proof (proj1 (forallb_forall _ _) Hge p Hp) as X; apply Nat.leb_le in X; apply Nat.leb_le; lia. }
  split; [apply updl_agree; exact Hge|].
  split; [|split; [exact Hpc | split; [unfold insts in Hlen; cbn [a_ss s_regs mk_ss] in Hlen; rewrite length_map in Hlen; exact Hlen
                                  | rewrite <- (insts_hid E sg inv model Hdg); exact HH]]].
  apply (proj1 (cs_ok_insts E sg inv R FULL model Hdg Hlog)).
  exact HC'.
Qed.


End Fixed.

(* [comment removed for export] *)
Hypothesis node_sys_sound : forall (fy : FPState) y, @sys_stmt fy y.
Hypothesis node_brk2_sound : forall (fy : FPState), @brk2d_stmt fy (node_brk2 A LIMIT).   (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis node_mmap_sound : forall (fy : FPState), @mmap_stmtW fy.     (* [comment removed for export] *)
Hypothesis node_mmapin_sound : forall (fy : FPState), @node1_stmt fy (is_ecall_at SEGS) (node_mmapin A LIMIT).
Hypothesis node_mprotect_sound : forall (fy : FPState), @node1_stmt fy (is_ecall_at SEGS) (node_mprotect A LIMIT).
Hypothesis node_exit_sound : forall (fy : FPState), @exit_stmt fy.
Hypothesis node_x_sound : forall (fy : FPState) x, @x_stmt fy x.
Hypothesis node_join_sound : forall (fy : FPState), @join_stmt fy.
Hypothesis node_ext_sound : forall (fy : FPState) id, xp_extG xp id = false -> @ext_stmt_at fy id.   (* [comment removed for export] *)
Hypothesis node_emit_sound : forall (fy : FPState), @emit_stmt fy.
Hypothesis node_ext2_sound : forall (fy : FPState), @ext2_stmt fy.
(* [comment removed for export] *)
Hypothesis HS_sound : forall (fy : FPState), frm_zero (@fp_csr fy) -> @holes_stmt fy.
(* [comment removed for export] *)
Hypothesis node_extF_sound : forall (fy : FPState) id, xp_extF xp id = true -> @ext_stmtF fy id.
(* [comment removed for export] *)
Hypothesis node_sysW_sound : forall (fy : FPState) y cs ws, xp_sysws xp y cs = Some ws ->
  @node1_stmtW_at fy (is_ecall_at SEGS) (node_sys A nx0 y) cs ws.
Hypothesis node_extW_sound : forall (fy : FPState) id args cs ws, xp_xnws xp id args cs = Some ws ->
  @node1_stmtW_at fy always (XN id args) cs ws.
Hypothesis node_emitW_sound : forall (fy : FPState) id args cs ws, xp_xews xp id args cs = Some ws ->
  @emit_stmtW_at fy id args cs ws.
Hypothesis node_xW_sound : forall (fy : FPState) x args cs ws, xp_xws xp x args cs = Some ws ->
  @node1_stmtW_at fy always (node_x SEGS A nx0 x args) cs ws.

(* [comment removed for export] *)
Definition vc_holds (c : vc) : Prop :=
  forall E M, know_ok SEGS E M (vc_kn c) -> Forall (gholds E M) (vc_hyps c) ->
  match vc_concl c with VCAtom g => gholds E M g | VCFact K => kentry_ok SEGS E M K end.
(* [comment removed for export] *)
Definition in_fp (E : env) (fp : list (expr * expr)) (a : word) : bool :=
  existsb (fun r => Z.leb (estart E (SA (fst r) 0)) (bv_unsigned a) && Z.ltb (bv_unsigned a) (estart E (SA (fst r) 0) + elenZ E (snd r)))%bool fp.
Hypothesis GP_frame : forall id args E M M',
  (forall a, in_fp E (g_fp (xp_gh xp) id args) a = true -> M' a = M a) ->
  GP id (map (uE E) args) M -> GP id (map (uE E) args) M'.
Lemma GP_pure : forall g E M M', gpure (xp_gh xp) g = true -> gholds E M g -> gholds E M' g.
Proof.
  intros [i args] E M M' Hp H. unfold gholds in *. cbn [g_id g_args] in *. unfold gpure in Hp. cbn [g_id g_args] in Hp.
  eapply GP_frame; [|exact H]. intros a Ha. destruct (g_fp (xp_gh xp) i args); [discriminate Ha | discriminate Hp].
Qed.
(* [comment removed for export] *)
Hypothesis G_ok : forall v, g_vcok (xp_gh xp) v = true -> vc_holds v.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ext_stmtG {fy : FPState} (id : nat) : Prop :=
  forall args cs cs' E R FULL model T,
    cs_ok E cs R FULL model -> props_ok E (Mr E cs model FULL) (a_props cs) -> XN id args cs = Some cs' ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' ->
        props_ok E' (Mr E' cs' model' FULL') (a_props cs') -> m_fs model' = m_fs model ->
        srealizes SEGS (@cfg_of fy SEGS R' (pc cs') FULL' model') T) ->
    srealizes SEGS (@cfg_of fy SEGS R (pc cs) FULL model) T.
Hypothesis node_extG_sound : forall (fy : FPState) id, xp_extG xp id = true -> @ext_stmtG fy id.

(* [comment removed for export] *)
#[local] Notation CHECK := (AP.check SEGS IT A nx0 LIMIT XN XE XB HS KC xp).
#[local] Notation cfgF fy := (@cfg_of fy SEGS) (only parsing).

(* [comment removed for export] *)
Definition in_windows (E : env) (W : list (saddr * expr)) (a : word) : bool :=
  existsb (fun w => Z.leb (estart E (fst w)) (bv_unsigned a) && Z.ltb (bv_unsigned a) (estart E (fst w) + elenZ E (snd w)))%bool W.
Definition WI (E0 : env) (M0 : word -> option byte) (m0 : Model) (E : env) (FULL : word -> option byte) (model : Model) : Prop :=
  match xp_wb xp with
  | None => True
  | Some (W, wlo) => env_agree wlo E0 E /\ (forall a, in_windows E0 W a = false -> FULL a = M0 a)
                     /\ mvis_eq m0 model           (* [comment removed for export] *)
  end.
(* [comment removed for export] *)
Definition lc_lo (c : loopctx) : nat := match c with LC _ _ lo _ => lo | JC _ _ _ b _ => b | WC _ _ lo _ _ _ _ => lo | SC _ hi => hi end.
Definition WBOK (lc : option loopctx) : Prop :=
  match xp_wb xp with
  | None => True
  | Some (W, wlo) => AP.wvars_lt wlo W = true /\ match lc with Some c => (wlo <= lc_lo c)%nat | None => False end
  end.

(* [comment removed for export] *)
Lemma log_flat_In : forall E log a w v, log_flat E log -> In (SE a w v) log -> (w <= 8)%nat /\ flat E a (Z.of_nat w).
Proof.
  intros E log a w v. induction log as [|[sa sw sv] rest IH]; intros Hlf Hin; [destruct Hin|].
  cbn [log_flat] in Hlf. destruct Hlf as (Hw & Hfl & Hrest). destruct Hin as [Heq|Hin].
  - injection Heq as -> -> ->. split; assumption.
  - exact (IH Hrest Hin).
Qed.
Lemma log_inside_out : forall E0 E' M fk W wlo log a,
  know_ok SEGS E' M fk -> log_flat E' log -> log_inside fk W log = true ->
  AP.wvars_lt wlo W = true -> env_agree wlo E0 E' ->
  in_windows E0 W a = false -> log_out E' log a.
Proof.
  intros E0 E' M fk W wlo log a Hfk Hlf Hli HWv Hag Hout s Hs.
  unfold log_inside in Hli. pose proof (proj1 (forallb_forall _ _) Hli s Hs) as Hx. destruct s as [[sb sk] w v]. cbn beta in Hx.
  apply existsb_exists in Hx as ([[wb wk] wl] & Hin & Hx). cbn [fst snd a_base a_off] in Hx.
  set (sa := SA sb sk) in *. set (wa := SA wb wk) in *.
  pose proof (xinside_sound SEGS E' M fk sb sk (elen w) wb wk wl Hfk Hx) as [X1 X2]. fold sa wa in X1, X2.
  destruct (log_flat_In E' log sa w v Hlf Hs) as [Hw8 Hfl].
  assert (Hel : elenZ E' (elen w) = Z.of_nat w).
  { unfold elenZ, elen. cbn [edenot]. apply u_small. lia. }
  rewrite Hel in X2.
  unfold AP.wvars_lt in HWv. pose proof (proj1 (forallb_forall _ _) HWv (wa, wl) Hin) as Hvw. cbn [fst snd] in Hvw.
  apply andb_prop in Hvw as [Hvb Hvl].
  assert (Eb : estart E0 wa = estart E' wa).
  { unfold estart. rewrite (edenot_agree' wlo E0 E' (a_base wa) Hag Hvb). reflexivity. }
  assert (El : elenZ E0 wl = elenZ E' wl).
  { unfold elenZ. rewrite (edenot_agree' wlo E0 E' wl Hag Hvl). reflexivity. }
  unfold in_windows in Hout.
  destruct (Z.leb (estart E0 wa) (bv_unsigned a) && Z.ltb (bv_unsigned a) (estart E0 wa + elenZ E0 wl))%bool eqn:Ht.
  { exfalso. assert (Hex : existsb (fun w0 : saddr * expr => (estart E0 (fst w0) <=? bv_unsigned a) && (bv_unsigned a <? estart E0 (fst w0) + elenZ E0 (snd w0)))%bool W = true).
    { apply existsb_exists. exists (wa, wl). split; [exact Hin | exact Ht]. }
    rewrite Hex in Hout. discriminate. }
  rewrite Eb, El in Ht. lia.
Qed.

(* [comment removed for export] *)
Lemma ws_inside_out : forall E0 E M fk ws W wlo a,
  know_ok SEGS E M fk -> ws_inside fk ws W = true ->
  AP.wvars_lt wlo W = true -> env_agree wlo E0 E ->
  in_windows E0 W a = false -> ws_out E ws a.
Proof.
  intros E0 E M fk ws W wlo a Hfk Hwi HWv Hag Hout [[sb sk] sl] Hs.
  unfold ws_inside in Hwi. pose proof (proj1 (forallb_forall _ _) Hwi _ Hs) as Hx. cbn beta in Hx.
  apply existsb_exists in Hx as ([[wb wk] wl] & Hin & Hx). cbn [fst snd a_base a_off] in Hx.
  pose proof (xinside_sound SEGS E M fk sb sk sl wb wk wl Hfk Hx) as [X1 X2].
  unfold AP.wvars_lt in HWv. pose proof (proj1 (forallb_forall _ _) HWv (SA wb wk, wl) Hin) as Hvw. cbn [fst snd a_base] in Hvw.
  apply andb_prop in Hvw as [Hvb Hvl].
  assert (Eb : estart E0 (SA wb wk) = estart E (SA wb wk)).
  { unfold estart. cbn [a_base a_off]. rewrite (edenot_agree' wlo E0 E wb Hag Hvb). reflexivity. }
  assert (El : elenZ E0 wl = elenZ E wl).
  { unfold elenZ. rewrite (edenot_agree' wlo E0 E wl Hag Hvl). reflexivity. }
  unfold in_windows in Hout.
  destruct (Z.leb (estart E0 (SA wb wk)) (bv_unsigned a) && Z.ltb (bv_unsigned a) (estart E0 (SA wb wk) + elenZ E0 wl))%bool eqn:Ht.
  { exfalso. assert (Hex : existsb (fun w0 : saddr * expr => (estart E0 (fst w0) <=? bv_unsigned a) && (bv_unsigned a <? estart E0 (fst w0) + elenZ E0 (snd w0)))%bool W = true).
    { apply existsb_exists. exists (SA wb wk, wl). split; [exact Hin | exact Ht]. }
    rewrite Hex in Hout. discriminate. }
  cbn [fst snd]. rewrite Eb, El in Ht. lia.
Qed.

Lemma run_block_gc_wb_sound : forall (fy : FPState) gb bfuel stops cs cs' E R FULL model T E0 M0 m0,
  frm_zero (@fp_csr fy) -> (nx0 <= gb)%nat ->
  run_block_gc_wb SEGS IT gb (AP.WB xp) KC bfuel stops cs = Some cs' -> cs_ok E cs R FULL model ->
  WI E0 M0 m0 E FULL model ->
  match xp_wb xp with Some (W, wlo) => (wlo <= gb)%nat /\ AP.wvars_lt wlo W = true | None => True end ->
  (forall (fy' : FPState) E' R' FULL' model', frm_zero (@fp_csr fy') ->
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> WI E0 M0 m0 E' FULL' model' ->
      m_fs model' = m_fs model -> srealizes SEGS (cfgF fy' R' (pc cs') FULL' model') T) ->
  srealizes SEGS (cfgF fy R (pc cs) FULL model) T.
Proof.
  intros fy gb bfuel stops cs cs' E R FULL model T E0 M0 m0 Hz Hgb Hrb HC HW HWB Hk.
  unfold run_block_gc_wb, run_block_wb, AP.WB in Hrb. unfold WI in HW, Hk |- *.
  destruct (xp_wb xp) as [[W wlo]|] eqn:HXW.
  - destruct HWB as [Hwlo HWv]. destruct HW as (Hag0 & HM0 & Hm0).
    destruct (fresh_ok gb cs) eqn:Hf0; [|discriminate]. cbv zeta in Hrb.
    rewrite AX2FE.sym_execTXFBI5_eq in Hrb.
    rewrite (AX2FB.sym_execTXFBI_eq SEGS (s_know (a_ss cs))) in Hrb by reflexivity.
    set (ss' := AX2F.sym_execTXF SEGS IT KC bfuel true stops (SS (s_pc (a_ss cs)) (s_regs (a_ss cs)) [] (s_know (a_ss cs)) (s_next (a_ss cs)))) in Hrb.
    destruct (log_inside (facts_of (s_know (a_ss cs))) W (s_log ss')) eqn:Hli; [|discriminate].
    assert (HF : facts_of (s_know (a_ss cs)) = facts_of (kunwrap_head (s_know ss'))).
    { unfold ss'. rewrite AX2B.facts_of_kunwrap_head, AX2FB.sym_execTXF_facts. reflexivity. }
    rewrite HF, AX2C.carryK3_eq in Hrb.
    destruct (carry (s_log ss') (kunwrap_head (s_know ss')) []) as [[kn' scs] hs] eqn:Hc. destruct scs; [|discriminate].
    injection Hrb as <-.
    eapply (@run_block_soundX fy gb bfuel stops cs kn' hs E R FULL model T Hz Hgb Hf0 Hc HC).
    intros fy' E' R' FULL' model' Hz' Hag HC1 Hfs Hlf HK' Hfr _ Hmv. rewrite <- (pc_cs_gc gb).
    assert (Fle : (gb <= nxt cs)%nat) by (unfold fresh_ok in Hf0; apply andb_prop in Hf0 as [_ Fle]; apply Nat.leb_le in Fle; exact Fle).
    assert (HagE : env_agree wlo E0 E').
    { eapply env_agree_trans; [exact Hag0 | eapply env_agree_le; [exact (proj2 Hag) | lia]]. }
    apply (Hk fy' E' R' FULL' model' Hz' Hag (cs_gc_ok _ _ _ _ _ _ HC1)); [|exact Hfs].
    split; [exact HagE|]. split; [|eapply mvis_trans; [exact Hm0 | exact Hmv]]. intros a Ha. rewrite <- (HM0 a Ha). apply Hfr.
    eapply (log_inside_out E0 E' _ (facts_of (s_know ss')) W wlo); [apply facts_of_ok; exact HK' | exact Hlf | | exact HWv | exact HagE | exact Ha].
    unfold ss'. rewrite AX2FB.sym_execTXF_facts. exact Hli.
  - unfold run_block_gc_wb, run_block_wb in Hrb.
    eapply (@run_block_gc_sound fy); [exact Hz | exact Hgb | exact Hrb | exact HC |].
    intros fy' E' R' FULL' model' Hz' Hag HC1 Hfs. exact (Hk fy' E' R' FULL' model' Hz' Hag HC1 I Hfs).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wout (E : env) (W : list (saddr * nat)) (a : word) : Prop :=
  forall w, In w W -> (bv_unsigned a < estart E (fst w) \/ estart E (fst w) + Z.of_nat (snd w) <= bv_unsigned a)%Z.
Lemma wout_log_out : forall E log a, wout E (log_windows log) a -> log_out E log a.
Proof.
  intros E log a H s Hs. destruct s as [sa w v]. apply (H (sa, w)). unfold log_windows. apply in_map_iff.
  exists (SE sa w v). split; [reflexivity | exact Hs].
Qed.
Lemma Mr_cs_gc : forall gb E cs model F, Mr E (cs_gc gb cs) model F = Mr E cs model F.
Proof. intros. unfold Mr. rewrite (hid_ext E cs (cs_gc gb cs) model); [reflexivity|]. unfold cs_gc. destruct (split_lit (reg cs 2)); reflexivity. Qed.
Lemma Mr_entails : forall E cs ch model F, entails cs ch = true -> Mr E ch model F = Mr E cs model F.
Proof.
  intros E cs ch model F H. unfold Mr. rewrite (hid_ext E cs ch model); [reflexivity|].
  unfold entails in H. repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  match goal with Ha : list_eqb pair_eqb (a_vis cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ha; symmetry; exact Ha end.
Qed.
(* [comment removed for export] *)
Lemma Mr_entails_h : forall lo hi E E' cs ch model F,
  entails_h A lo hi cs ch = true -> (nx0 <= lo)%nat -> env_agree lo E E' -> Mr E' ch model F = Mr E cs model F.
Proof.
  intros lo hi E E' cs ch model F H Hlo Hag. unfold entails_h in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  match goal with Ha : list_eqb pair_eqb (a_vis cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ha; rename Ha into Hvis end.
  match goal with Hv : pairs_vars_lt lo (a_vis ch) = true |- _ => rename Hv into Hpv end.
  match goal with Hg : pairs_vars_lt lo (a_ghost ch) = true |- _ => rename Hg into Hpg end.
  unfold Mr. rewrite (hid_agree lo E E' ch model Hag Hlo) by (unfold pairs_vars_lt in *; rewrite forallb_app, Hpv, Hpg; reflexivity).
  rewrite (hid_ext E cs ch model) by (symmetry; exact Hvis). reflexivity.
Qed.

Lemma log_windows_w8 : forall E log, log_flat E log -> Forall (fun w : saddr * nat => (snd w <= 8)%nat) (log_windows log).
Proof.
  intros E log. induction log as [|[sa w v] rest IH]; intros Hlf; [constructor|].
  cbn [log_flat] in Hlf. destruct Hlf as (Hw & _ & Hrest). unfold log_windows. cbn [map]. constructor; [exact Hw | exact (IH Hrest)].
Qed.

(* [comment removed for export] *)
Lemma run_block_gc_wb_ws_sound : forall (fy : FPState) gb bfuel stops cs cs' W E R FULL model T E0 M0 m0,
  frm_zero (@fp_csr fy) -> (nx0 <= gb)%nat ->
  run_block_gc_wb_ws SEGS IT gb (AP.WB xp) KC bfuel stops cs = Some (cs', W) -> cs_ok E cs R FULL model ->
  WI E0 M0 m0 E FULL model ->
  match xp_wb xp with Some (W0, wlo) => (wlo <= gb)%nat /\ AP.wvars_lt wlo W0 = true | None => True end ->
  (forall (fy' : FPState) E' R' FULL' model', frm_zero (@fp_csr fy') ->
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> WI E0 M0 m0 E' FULL' model' ->
      m_fs model' = m_fs model ->
      Forall (fun w => (snd w <= 8)%nat) W ->
      (forall a, wout E' W a -> Mr E' cs' model' FULL' a = Mr E cs model FULL a) ->
      srealizes SEGS (cfgF fy' R' (pc cs') FULL' model') T) ->
  srealizes SEGS (cfgF fy R (pc cs) FULL model) T.
Proof.
  intros fy gb bfuel stops cs cs' W E R FULL model T E0 M0 m0 Hz Hgb Hrb HC HW HWB Hk.
  unfold run_block_gc_wb_ws, run_block_wb_ws, AP.WB in Hrb. unfold WI in HW, Hk |- *.
  destruct (fresh_ok gb cs) eqn:Hf0; [|destruct (xp_wb xp) as [[? ?]|]; discriminate]. cbv zeta in Hrb.
  rewrite AX2FE.sym_execTXFBI5_eq in Hrb.
  rewrite (AX2FB.sym_execTXFBI_eq SEGS (s_know (a_ss cs))) in Hrb by reflexivity.
  set (ss' := AX2F.sym_execTXF SEGS IT KC bfuel true stops (SS (s_pc (a_ss cs)) (s_regs (a_ss cs)) [] (s_know (a_ss cs)) (s_next (a_ss cs)))) in Hrb.
  assert (HF : facts_of (s_know (a_ss cs)) = facts_of (kunwrap_head (s_know ss'))).
  { unfold ss'. rewrite AX2B.facts_of_kunwrap_head, AX2FB.sym_execTXF_facts. reflexivity. }
  assert (Fle : (gb <= nxt cs)%nat) by (unfold fresh_ok in Hf0; apply andb_prop in Hf0 as [_ Fle]; apply Nat.leb_le in Fle; exact Fle).
  destruct (xp_wb xp) as [[W0 wlo]|] eqn:HXW.
  - destruct HWB as [Hwlo HWv]. destruct HW as (Hag0 & HM0 & Hm0).
    destruct (log_inside (facts_of (s_know (a_ss cs))) W0 (s_log ss')) eqn:Hli; [|discriminate].
    rewrite HF, AX2C.carryK3_eq in Hrb.
    destruct (carry (s_log ss') (kunwrap_head (s_know ss')) []) as [[kn' scs] hs] eqn:Hc. destruct scs; [|discriminate].
    injection Hrb as <- <-.
    eapply (@run_block_soundX fy gb bfuel stops cs kn' hs E R FULL model T Hz Hgb Hf0 Hc HC).
    intros fy' E' R' FULL' model' Hz' Hag HC1 Hfs Hlf HK' Hfr Hmr Hmv. rewrite <- (pc_cs_gc gb).
    assert (HagE : env_agree wlo E0 E').
    { eapply env_agree_trans; [exact Hag0 | eapply env_agree_le; [exact (proj2 Hag) | lia]]. }
    apply (Hk fy' E' R' FULL' model' Hz' Hag (cs_gc_ok _ _ _ _ _ _ HC1)); [| exact Hfs | exact (log_windows_w8 _ _ Hlf) |].
    + split; [exact HagE|]. split; [|eapply mvis_trans; [exact Hm0 | exact Hmv]]. intros a Ha. rewrite <- (HM0 a Ha). apply Hfr.
      eapply (log_inside_out E0 E' _ (facts_of (s_know ss')) W0 wlo); [apply facts_of_ok; exact HK' | exact Hlf | | exact HWv | exact HagE | exact Ha].
      unfold ss'. rewrite AX2FB.sym_execTXF_facts. exact Hli.
    + intros a Ha. rewrite Mr_cs_gc. apply Hmr. apply wout_log_out. exact Ha.
  - rewrite HF, AX2C.carryK3_eq in Hrb.
    destruct (carry (s_log ss') (kunwrap_head (s_know ss')) []) as [[kn' scs] hs] eqn:Hc. destruct scs; [|discriminate].
    injection Hrb as <- <-.
    eapply (@run_block_soundX fy gb bfuel stops cs kn' hs E R FULL model T Hz Hgb Hf0 Hc HC).
    intros fy' E' R' FULL' model' Hz' Hag HC1 Hfs Hlf HK' Hfr Hmr Hmv. rewrite <- (pc_cs_gc gb).
    apply (Hk fy' E' R' FULL' model' Hz' Hag (cs_gc_ok _ _ _ _ _ _ HC1) I Hfs (log_windows_w8 _ _ Hlf)).
    intros a Ha. rewrite Mr_cs_gc. apply Hmr. apply wout_log_out. exact Ha.
Qed.


Definition LCOK (E0 : env) (M0 : word -> option byte) (m0 : Model) (lc : option loopctx) (D : TSet) (E : env) (fs : Fs.Fs) : Prop :=
  WBOK lc /\
  match lc with
  | None => True
  | Some (LC h nx lo hi) => ((nx0 <= lo)%nat /\ (lo <= hi)%nat /\ length (s_regs (a_ss nx)) = 32%nat) /\
              forall (fy : FPState) E' R' F' m', frm_zero (@fp_csr fy) -> env_agree lo E E' -> cs_ok E' nx R' F' m' -> WI E0 M0 m0 E' F' m' -> m_fs m' = fs ->
                srealizes SEGS (cfgF fy R' h F' m') D
  (* [comment removed for export] *)
  | Some (JC j js sk b lo) => ((nx0 <= b)%nat /\ (b <= lo)%nat /\ (length (s_regs (a_ss js)) = 32%nat /\ forallb (gvars_lt b) (a_props js) = true)) /\
              forall (fy : FPState) E' R' F' m', frm_zero (@fp_csr fy) -> env_agree b E E' -> cs_ok E' js R' F' m' -> WI E0 M0 m0 E' F' m' -> m_fs m' = fs ->
                props_ok E' (Mr E' js m' F') (a_props js) ->       (* [comment removed for export] *)
                srealizes SEGS (cfgF fy R' (pc js) F' m') (sd D E' fs sk)
  (* [comment removed for export] *)
  | Some (WC hs cur lo hi V xs xts) =>
      ((nx0 <= lo)%nat /\ (lo <= hi)%nat /\ AP.expr_vars_lt hi V = true) /\
      (forall h T, nth_error hs h = Some T -> s_log (a_ss T) = [] /\ (lo <= nxt T)%nat /\
         forall (fy : FPState) E' R' F' m', frm_zero (@fp_csr fy) -> env_agree lo E E' -> cs_ok E' T R' F' m' -> WI E0 M0 m0 E' F' m' -> m_fs m' = fs ->
           props_ok E' (Mr E' T m' F') (a_props T) ->
           (uE E' V < uE E V \/ (uE E' V <= uE E V /\ (cur < h)%nat)) ->
           srealizes SEGS (cfgF fy R' (pc T) F' m') (sd D E' fs xs)) /\
      (forall i x sx, nth_error xts i = Some (x, sx) -> (lo <= nxt x)%nat /\ s_log (a_ss x) = [] /\
         forall (fy : FPState) E' R' F' m', frm_zero (@fp_csr fy) -> env_agree lo E E' -> cs_ok E' x R' F' m' -> WI E0 M0 m0 E' F' m' -> m_fs m' = fs ->
           props_ok E' (Mr E' x m' F') (a_props x) ->
           srealizes SEGS (cfgF fy R' (pc x) F' m') (sd D E' fs sx))
  (* [comment removed for export] *)
  | Some (SC outs hi) =>
      (nx0 <= hi)%nat /\
      (forall i x, nth_error outs i = Some x -> (hi <= nxt x)%nat /\ s_log (a_ss x) = [] /\ length (s_regs (a_ss x)) = 32%nat /\
         forall (fy : FPState) E' R' F' m', frm_zero (@fp_csr fy) -> env_agree hi E E' -> cs_ok E' x R' F' m' -> WI E0 M0 m0 E' F' m' -> m_fs m' = fs ->
           srealizes SEGS (cfgF fy R' (pc x) F' m') (HOLES 0%nat E' fs))     (* [comment removed for export] *)
  end.

Lemma LCOK_bnd : forall E0 M0 m0 lc D E fs, LCOK E0 M0 m0 lc D E fs -> (nx0 <= match lc with Some c => lc_bnd c | None => nx0 end)%nat.
Proof.
  intros E0 M0 m0 [[h nx lo hi|j js sk b lo|hs cur lo hi V xs xts|so shi]|] D E fs [_ HL]; cbn [lc_bnd] in *;
    [destruct HL as [(H1 & H2 & _) _]; lia | destruct HL as [(H1 & _ & _) _]; lia | destruct HL as [(H1 & H2 & _) _]; lia
    | destruct HL as [H1 _]; lia | lia].
Qed.
Lemma LCOK_wbok : forall E0 M0 m0 lc D E fs, LCOK E0 M0 m0 lc D E fs -> WBOK lc.
Proof. intros E0 M0 m0 lc D E fs [H _]. exact H. Qed.

Definition lc_guard (lc : option loopctx) (cs : acs) : bool :=
  match lc with Some c => Nat.leb (lc_bnd c) (nxt cs) | None => true end.

(* [comment removed for export] *)
Lemma WI_none : forall E0 M0 m0 E F m, xp_wb xp = None -> WI E0 M0 m0 E F m.
Proof. intros E0 M0 m0 E F m H. unfold WI. rewrite H. exact I. Qed.
Lemma LCOK_lo_bnd : forall E0 M0 m0 lc D E fs c, LCOK E0 M0 m0 lc D E fs -> lc = Some c -> (lc_lo c <= lc_bnd c)%nat.
Proof.
  intros E0 M0 m0 lc D E fs c [_ HL] ->. destruct c as [h nx lo hi|j js sk b lo|hs cur lo hi V xs xts|so shi]; cbn [lc_lo lc_bnd LCOK] in *;
    [destruct HL as [(? & ? & _) _]; lia | lia | destruct HL as [(? & ? & _) _]; lia | lia].
Qed.
Lemma WI_agree : forall E0 M0 m0 lc D Ex fs E E' F m cs,
  WI E0 M0 m0 E F m -> LCOK E0 M0 m0 lc D Ex fs -> lc_guard lc cs = true -> env_agree (nxt cs) E E' -> WI E0 M0 m0 E' F m.
Proof.
  intros E0 M0 m0 lc D Ex fs E E' F m cs HW HL Hg Hag. pose proof (proj1 HL) as HB. unfold WI, WBOK in *.
  destruct (xp_wb xp) as [[W wlo]|]; [|exact I]. destruct HB as [_ HB].
  destruct lc as [c|]; [|destruct HB]. cbn [lc_guard] in Hg. apply Nat.leb_le in Hg.
  pose proof (LCOK_lo_bnd _ _ _ _ _ _ _ c HL eq_refl) as Hlb.
  destruct HW as [Hag0 HM]. split; [|exact HM].
  eapply env_agree_trans; [exact Hag0 | eapply env_agree_le; [exact Hag | lia]].
Qed.
(* [comment removed for export] *)
Lemma WI_mv : forall E0 M0 m0 E F m m', WI E0 M0 m0 E F m -> mvis_eq m m' -> WI E0 M0 m0 E F m'.
Proof.
  intros E0 M0 m0 E F m m' HW Hmv. unfold WI in *. destruct (xp_wb xp) as [[W wlo]|]; [|exact I].
  destruct HW as (Hag & HM & Hm). split; [exact Hag|]. split; [exact HM|]. eapply mvis_trans; [exact Hm | exact Hmv].
Qed.
Lemma WBOK_nest : forall E0 M0 m0 lc D E fs c',
  LCOK E0 M0 m0 lc D E fs -> ((match lc with Some c => lc_bnd c | None => nx0 end) <= lc_lo c')%nat -> WBOK (Some c').
Proof.
  intros E0 M0 m0 lc D E fs c' HL Hle. pose proof (proj1 HL) as HB. unfold WBOK in *.
  destruct (xp_wb xp) as [[W wlo]|]; [|exact I]. destruct HB as [HWv HB]. split; [exact HWv|].
  destruct lc as [c|]; [|destruct HB]. pose proof (LCOK_lo_bnd _ _ _ _ _ _ _ c HL eq_refl). lia.
Qed.
Lemma WB_run : forall E0 M0 m0 lc D E fs cs,
  LCOK E0 M0 m0 lc D E fs -> lc_guard lc cs = true ->
  match xp_wb xp with Some (W, wlo) => (wlo <= match lc with Some c => lc_bnd c | None => nx0 end)%nat /\ AP.wvars_lt wlo W = true | None => True end.
Proof.
  intros E0 M0 m0 lc D E fs cs HL Hg. pose proof (proj1 HL) as HB. unfold WBOK in HB.
  destruct (xp_wb xp) as [[W wlo]|]; [|exact I]. destruct HB as [HWv HB].
  destruct lc as [c|]; [|destruct HB]. pose proof (LCOK_lo_bnd _ _ _ _ _ _ _ c HL eq_refl). split; [lia | exact HWv].
Qed.
Lemma WI_agree_lo : forall E0 M0 m0 lc E E' F m,
  WI E0 M0 m0 E F m -> WBOK lc -> env_agree (match lc with Some c => lc_lo c | None => nx0 end) E E' -> WI E0 M0 m0 E' F m.
Proof.
  intros E0 M0 m0 lc E E' F m HW HB Hag. unfold WI, WBOK in *. destruct (xp_wb xp) as [[W wlo]|]; [|exact I]. destruct HB as [_ HB].
  destruct lc as [c|]; [|destruct HB]. destruct HW as [Hag0 HM]. split; [|exact HM].
  eapply env_agree_trans; [exact Hag0 | eapply env_agree_le; [exact Hag | exact HB]].
Qed.
Lemma WI_agree_gb : forall E0 M0 m0 lc D Ex fs E E' F m,
  WI E0 M0 m0 E F m -> LCOK E0 M0 m0 lc D Ex fs -> env_agree (match lc with Some c => lc_bnd c | None => nx0 end) E E' -> WI E0 M0 m0 E' F m.
Proof.
  intros E0 M0 m0 lc D Ex fs E E' F m HW HL Hag. pose proof (proj1 HL) as HB. unfold WI, WBOK in *.
  destruct (xp_wb xp) as [[W wlo]|]; [|exact I]. destruct HB as [_ HB].
  destruct lc as [c|]; [|destruct HB]. pose proof (LCOK_lo_bnd _ _ _ _ _ _ _ c HL eq_refl) as Hlb.
  destruct HW as [Hag0 HM]. split; [|exact HM].
  eapply env_agree_trans; [exact Hag0 | eapply env_agree_le; [exact Hag | lia]].
Qed.
Lemma WI_frame : forall E0 M0 m0 E F F' m,
  WI E0 M0 m0 E F m ->
  (match xp_wb xp with None => True | Some (W, _) => forall a, in_windows E0 W a = false -> F' a = F a end) ->
  WI E0 M0 m0 E F' m.
Proof.
  intros E0 M0 m0 E F F' m HW HF. unfold WI in *. destruct (xp_wb xp) as [[W wlo]|]; [|exact I].
  destruct HW as (Hag & HM & Hm). split; [exact Hag|]. split; [|exact Hm]. intros a Ha. rewrite (HF a Ha). exact (HM a Ha).
Qed.
(* [comment removed for export] *)
Lemma WI_ws : forall E0 M0 m0 lc D Ex fs E E' F F' m m' cs ows ws M,
  WI E0 M0 m0 E F m -> LCOK E0 M0 m0 lc D Ex fs -> lc_guard lc cs = true -> env_agree (nxt cs) E E' ->
  AP.okW xp ows cs = true -> ows = Some ws -> know_ok SEGS E M (facts_of (kn cs)) ->
  (forall a, ws_out E ws a -> F' a = F a) -> mvis_eq m m' ->
  WI E0 M0 m0 E' F' m'.
Proof.
  intros E0 M0 m0 lc D Ex fs E E' F F' m m' cs ows ws M HW HL Hg Hag Hok Hows Hfk Hfr Hmv.
  pose proof (WI_agree _ _ _ _ _ _ _ _ _ _ _ _ HW HL Hg Hag) as HW'. pose proof (proj1 HL) as HB.
  unfold WI, WBOK, AP.okW in *. destruct (xp_wb xp) as [[W wlo]|]; [|exact I]. subst ows.
  destruct HB as [HWv HB]. destruct HW as (Hag0 & HM & Hm). destruct HW' as [Hag0' _]. split; [exact Hag0'|].
  split; [|eapply mvis_trans; [exact Hm | exact Hmv]].
  intros a Ha. rewrite <- (HM a Ha). apply Hfr.
  eapply (ws_inside_out E0 E M (facts_of (kn cs)) ws W wlo a Hfk Hok HWv Hag0 Ha).
Qed.

(* [comment removed for export] *)
Lemma LCOK_WC_agree : forall E0 M0 m0 hs cur lo hi V xs xts D E E' fs,
  LCOK E0 M0 m0 (Some (WC hs cur lo hi V xs xts)) D E fs -> env_agree hi E E' -> LCOK E0 M0 m0 (Some (WC hs cur lo hi V xs xts)) D E' fs.
Proof.
  intros E0 M0 m0 hs cur lo hi V xs xts D E E' fs [HB HL] Hag. split; [exact HB|]. cbn [LCOK] in *. destruct HL as ((Hn0 & Hlh & HV) & HL2 & HL3).
  split; [split; [exact Hn0 | split; [exact Hlh | exact HV]]|].
  assert (AG : forall E2, env_agree lo E' E2 -> env_agree lo E E2).
  { intros E2 H2. eapply env_agree_trans; [eapply env_agree_le; [exact Hag | exact Hlh] | exact H2]. }
  split.
  - intros h T HT. destruct (HL2 h T HT) as (Hlog & Hlo & HL2'). split; [exact Hlog|]. split; [exact Hlo|].
    intros fy2 E2 R' F' m' Hz2 Hag2 HC2 HW2 Hfs HP2 HV2. apply (HL2' fy2 E2 R' F' m' Hz2 (AG E2 Hag2) HC2 HW2 Hfs HP2).
    unfold uE in *. rewrite (edenot_agree' hi E E' V Hag HV). exact HV2.
  - intros i x sx Hi. destruct (HL3 i x sx Hi) as (Hx1 & Hx2 & HL3i). split; [exact Hx1|]. split; [exact Hx2|].
    intros fy2 E2 R' F' m' Hz2 Hag2. apply (HL3i fy2 E2 R' F' m' Hz2). exact (AG E2 Hag2).
Qed.

(* [comment removed for export] *)
Lemma LCOK_SC_agree : forall E0 M0 m0 outs hi D E E' fs,
  LCOK E0 M0 m0 (Some (SC outs hi)) D E fs -> env_agree hi E E' -> LCOK E0 M0 m0 (Some (SC outs hi)) D E' fs.
Proof.
  intros E0 M0 m0 outs hi D E E' fs [HB [Hn0 HL]] Hag. split; [exact HB|]. cbn [LCOK]. split; [exact Hn0|].
  intros i x Hi. destruct (HL i x Hi) as (H1 & H2 & H3 & HLi). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros fy2 E2 R' F' m' Hz2 Hag2. apply (HLi fy2 E2 R' F' m' Hz2). eapply env_agree_trans; [exact Hag | exact Hag2].
Qed.

Lemma LCOK_agree : forall E0 M0 m0 lc D E E' fs cs,
  LCOK E0 M0 m0 lc D E fs -> lc_guard lc cs = true -> env_agree (nxt cs) E E' -> LCOK E0 M0 m0 lc D E' fs.
Proof.
  intros E0 M0 m0 [[h nx lo hi|j js sk b lo|hs cur lo hi V xs xts|so shi]|] D E E' fs cs HL Hg Hag; [| | | |exact HL]; cbn [lc_guard lc_bnd] in Hg;
  apply Nat.leb_le in Hg.
  3: { eapply LCOK_WC_agree; [exact HL | eapply env_agree_le; [exact Hag | exact Hg]]. }
  3: { eapply LCOK_SC_agree; [exact HL | eapply env_agree_le; [exact Hag | exact Hg]]. }
  all: destruct HL as [HB HL]; (split; [exact HB|]); cbn [LCOK] in *; destruct HL as [(Hn0 & Hlh & Hlen) HL];
  (split; [split; [exact Hn0 | split; [exact Hlh | exact Hlen]]|]);
  intros fy2 E2 R' F' m' Hz2 Hag2; (apply HL; [exact Hz2 | eapply env_agree_trans; [eapply env_agree_le; [exact Hag | lia] | exact Hag2]]).
Qed.

(* [comment removed for export] *)
Lemma LCOK_agree_gb : forall E0 M0 m0 lc D E E' fs,
  LCOK E0 M0 m0 lc D E fs -> env_agree (match lc with Some c => lc_bnd c | None => nx0 end) E E' -> LCOK E0 M0 m0 lc D E' fs.
Proof.
  intros E0 M0 m0 [[h nx lo hi|j js sk b lo|hs cur lo hi V xs xts|so shi]|] D E E' fs HL Hag; [| | | |exact HL]; cbn [lc_bnd] in Hag.
  3: { eapply LCOK_WC_agree; [exact HL | exact Hag]. }
  3: { eapply LCOK_SC_agree; [exact HL | exact Hag]. }
  all: destruct HL as [HB HL]; (split; [exact HB|]); cbn [LCOK] in *; destruct HL as [(Hn0 & Hlh & Hlen) HL];
  (split; [split; [exact Hn0 | split; [exact Hlh | exact Hlen]]|]);
  intros fy2 E2 R' F' m' Hz2 Hag2; (apply HL; [exact Hz2 | eapply env_agree_trans; [eapply env_agree_le; [exact Hag | lia] | exact Hag2]]).
Qed.

(* [comment removed for export] *)
Lemma props_ok_nil : forall E M, props_ok E M [].
Proof. intros; constructor. Qed.

Lemma gholds_agree : forall b E E' M g, env_agree b E E' -> gvars_lt b g = true -> gholds E M g <-> gholds E' M g.
Proof.
  intros b E E' M g Hag Hv. unfold gholds.
  replace (map (uE E') (g_args g)) with (map (uE E) (g_args g)); [tauto|].
  apply map_ext_in. intros e He. unfold uE. f_equal. eapply edenot_agree'; [exact Hag|].
  exact (proj1 (forallb_forall _ _) Hv e He).
Qed.

Lemma props_ok_agree : forall b E E' M l,
  props_ok E M l -> forallb (gvars_lt b) l = true -> env_agree b E E' -> props_ok E' M l.
Proof.
  intros b E E' M l HP Hv Hag. unfold props_ok in *. apply Forall_forall. intros g Hg.
  apply (proj1 (gholds_agree b E E' M g Hag (proj1 (forallb_forall _ _) Hv g Hg))). exact (proj1 (Forall_forall _ _) HP g Hg).
Qed.

(* [comment removed for export] *)
Lemma props_ok_pure : forall E M M' l, props_ok E M l -> forallb (gpure (xp_gh xp)) l = true -> props_ok E M' l.
Proof.
  intros E M M' l HP Hp. unfold props_ok in *. apply Forall_forall. intros g Hg.
  eapply GP_pure; [exact (proj1 (forallb_forall _ _) Hp g Hg) | exact (proj1 (Forall_forall _ _) HP g Hg)].
Qed.

(* [comment removed for export] *)
Lemma props_ok_gkeep : forall E E' M M' M'' cs cs' W,
  props_ok E M (a_props cs) -> env_agree (nxt cs) E E' -> know_ok SEGS E' M'' (kn cs') ->
  Forall (fun w => (snd w <= 8)%nat) W ->
  (forall a, wout E' W a -> M' a = M a) ->
  props_ok E' M' (a_props (gkeep (xp_gh xp) W cs cs')).
Proof.
  intros E E' M M' M'' cs cs' W HP Hag HK HW8 Hfr. unfold gkeep, set_props. cbn [a_props]. unfold nxt in Hag.
  unfold props_ok in *. apply Forall_forall. intros g Hg. apply filter_In in Hg as [Hin Hk].
  unfold gkeep1 in Hk. apply andb_prop in Hk as [Hv Hap].
  pose proof (proj1 (Forall_forall _ _) HP g Hin) as G0. apply (proj1 (gholds_agree _ E E' M g Hag Hv)) in G0.
  destruct g as [i args]. unfold gholds in *. cbn [g_id g_args] in *.
  eapply GP_frame; [|exact G0]. intros a Ha. apply Hfr. intros [wa wn] Hw.
  unfold in_fp in Ha. apply existsb_exists in Ha as ([rb rl] & Hr & Ha). cbn [fst snd] in Ha.
  apply andb_prop in Ha as [Ha1 Ha2]. apply Z.leb_le in Ha1. apply Z.ltb_lt in Ha2.
  pose proof (proj1 (forallb_forall _ _) Hap (rb, rl) Hr) as Hw1. unfold fp_apart in Hw1.
  pose proof (proj1 (forallb_forall _ _) Hw1 (wa, wn) Hw) as Hx. cbn [fst snd] in Hx.
  pose proof (ranges_apart_x_sound SEGS E' M'' (kn cs') (a_base wa) (a_off wa) (elen wn) rb 0 rl HK Hx) as X.
  assert (Hel : elenZ E' (elen wn) = Z.of_nat wn).
  { unfold elenZ, elen. cbn [edenot]. apply u_small. pose proof (proj1 (Forall_forall _ _) HW8 (wa, wn) Hw) as H8. cbn [snd] in H8. lia. }
  rewrite Hel in X. cbn [fst snd]. replace (estart E' wa) with (estart E' (SA (a_base wa) (a_off wa))) by (destruct wa; reflexivity). lia.
Qed.

(* [comment removed for export] *)
Lemma props_ok_gkeepE : forall E E' M M' Mk fk W nx props,
  props_ok E M props -> env_agree nx E E' -> know_ok SEGS E Mk fk ->
  (forall a, ws_out E W a -> M' a = M a) ->
  props_ok E' M' (List.filter (AP.gkeep1E (xp_gh xp) fk W nx) props).
Proof.
  intros E E' M M' Mk fk W nx props HP Hag HK Hfr.
  unfold props_ok in *. apply Forall_forall. intros g Hg. apply filter_In in Hg as [Hin Hk].
  unfold AP.gkeep1E in Hk. apply andb_prop in Hk as [Hv Hap].
  pose proof (proj1 (Forall_forall _ _) HP g Hin) as G0.
  apply (proj1 (gholds_agree _ E E' M' g Hag Hv)).
  destruct g as [i args]. unfold gholds in *. cbn [g_id g_args] in *.
  eapply GP_frame; [|exact G0]. intros a Ha. apply Hfr. intros [[wb wk] wl] Hw. cbn [fst snd].
  unfold in_fp in Ha. apply existsb_exists in Ha as ([rb rl] & Hr & Ha). cbn [fst snd] in Ha.
  apply andb_prop in Ha as [Ha1 Ha2]. apply Z.leb_le in Ha1. apply Z.ltb_lt in Ha2.
  pose proof (proj1 (forallb_forall _ _) Hap (rb, rl) Hr) as Hw1. unfold AP.fp_apartE in Hw1.
  pose proof (proj1 (forallb_forall _ _) Hw1 (SA wb wk, wl) Hw) as Hx. cbn [fst snd a_base a_off] in Hx.
  pose proof (ranges_apart_x_sound SEGS E Mk fk wb wk wl rb 0 rl HK Hx) as X. lia.
Qed.
(* [comment removed for export] *)
Lemma hid_memneutral : forall E E' cs cs' model,
  fresh_ok nx0 cs = true -> a_vis cs' = a_vis cs -> env_agree (nxt cs) E E' -> hid E' cs' model = hid E cs model.
Proof.
  intros E E' cs cs' model Hf Hv Hag. destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  eapply hid_extF; [exact Hv | exact Hag | exact Fle | exact Fallow | apply mvis_refl].
Qed.
Lemma node_havoc_neutral : forall cs rs cs', node_havoc nx0 cs rs = Some cs' -> fresh_ok nx0 cs = true /\ a_vis cs' = a_vis cs.
Proof.
  intros cs rs cs' H. unfold node_havoc in H. destruct (fresh_ok nx0 cs) eqn:Hf; [|discriminate H].
  cbn [andb] in H. destruct (forallb _ rs); [|discriminate H]. injection H as <-. split; reflexivity.
Qed.
Lemma node_havocbig_neutral : forall cs K cs', node_havocbig nx0 cs K = Some cs' -> fresh_ok nx0 cs = true /\ a_vis cs' = a_vis cs.
Proof.
  intros cs K cs' H. unfold node_havocbig in H. destruct (node_havoc nx0 cs _) as [cs1|] eqn:Hh; [|discriminate H].
  destruct (node_havoc_neutral _ _ _ Hh) as [Hf Hv]. destruct (fresh_ok nx0 cs1); [|discriminate H].
  destruct (kn_bigsubst _ _ _) as [k' c]. injection H as <-. split; [exact Hf|]. rewrite <- Hv. reflexivity.
Qed.
Lemma node_intro_neutral : forall cs lo hi cs', node_intro nx0 cs lo hi = Some cs' -> fresh_ok nx0 cs = true /\ a_vis cs' = a_vis cs.
Proof.
  intros cs lo hi cs' H. unfold node_intro in H. destruct (fresh_ok nx0 cs) eqn:Hf; [|discriminate H]. cbn [andb] in H.
  destruct (_ && _ && _)%bool; [|discriminate H]. injection H as <-. split; reflexivity.
Qed.
Lemma node_fresh_neutral : forall cs r logc base cs', node_fresh nx0 cs r logc base = Some cs' -> fresh_ok nx0 cs = true /\ a_vis cs' = a_vis cs.
Proof.
  intros cs r logc base cs' H. unfold node_fresh in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate H] end.
  repeat (apply andb_prop in Hc as [Hc ?X]). 
  destruct (xlo2 _ _); [|discriminate H]. destruct (xhi2 _ _); [|discriminate H]. injection H as <-.
  split; [assumption | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma Mr_frameW : forall (P : word -> Prop) E E' cs cs' m m' F F',
  hid E' cs' m' = hid E cs m -> (forall a, P a -> F' a = F a) -> forall a, P a -> Mr E' cs' m' F' a = Mr E cs m F a.
Proof. intros P E E' cs cs' m m' F F' Hh Hf a Ha. unfold Mr, mrestrict. rewrite Hh. destruct (hid E cs m a); [reflexivity | apply Hf; exact Ha]. Qed.

(* [comment removed for export] *)
Lemma props_ok_gkeep_sub : forall E E' M M' Mk k W W' nx props,
  props_ok E M props -> env_agree nx E E' -> know_ok SEGS E' Mk k ->
  incl W' W -> Forall (fun w => (snd w <= 8)%nat) W' ->
  (forall a, wout E' W' a -> M' a = M a) ->
  props_ok E' M' (List.filter (gkeep1 (xp_gh xp) k W nx) props).
Proof.
  intros E E' M M' Mk k W W' nx props HP Hag HK Hincl HW8 Hfr.
  unfold props_ok in *. apply Forall_forall. intros g Hg. apply filter_In in Hg as [Hin Hk].
  unfold gkeep1 in Hk. apply andb_prop in Hk as [Hv Hap].
  pose proof (proj1 (Forall_forall _ _) HP g Hin) as G0. apply (proj1 (gholds_agree _ E E' M g Hag Hv)) in G0.
  destruct g as [i args]. unfold gholds in *. cbn [g_id g_args] in *.
  eapply GP_frame; [|exact G0]. intros a Ha. apply Hfr. intros [wa wn] Hw.
  unfold in_fp in Ha. apply existsb_exists in Ha as ([rb rl] & Hr & Ha). cbn [fst snd] in Ha.
  apply andb_prop in Ha as [Ha1 Ha2]. apply Z.leb_le in Ha1. apply Z.ltb_lt in Ha2.
  pose proof (proj1 (forallb_forall _ _) Hap (rb, rl) Hr) as Hw1. unfold fp_apart in Hw1.
  pose proof (proj1 (forallb_forall _ _) Hw1 (wa, wn) (Hincl _ Hw)) as Hx. cbn [fst snd] in Hx.
  pose proof (ranges_apart_x_sound SEGS E' Mk k (a_base wa) (a_off wa) (elen wn) rb 0 rl HK Hx) as X.
  assert (Hel : elenZ E' (elen wn) = Z.of_nat wn).
  { unfold elenZ, elen. cbn [edenot]. apply u_small. pose proof (proj1 (Forall_forall _ _) HW8 (wa, wn) Hw) as H8. cbn [snd] in H8. lia. }
  rewrite Hel in X. cbn [fst snd]. replace (estart E' wa) with (estart E' (SA (a_base wa) (a_off wa))) by (destruct wa; reflexivity). lia.
Qed.
(* [comment removed for export] *)
Lemma props_ok_gkeep1_agree : forall E E' M k W nx props,
  env_agree nx E E' -> props_ok E M (List.filter (gkeep1 (xp_gh xp) k W nx) props) ->
  props_ok E' M (List.filter (gkeep1 (xp_gh xp) k W nx) props).
Proof.
  intros E E' M k W nx props Hag HP. unfold props_ok in *. apply Forall_forall. intros g Hg.
  pose proof (proj1 (Forall_forall _ _) HP g Hg) as G0. apply filter_In in Hg as [_ Hk].
  unfold gkeep1 in Hk. apply andb_prop in Hk as [Hv _]. exact (proj1 (gholds_agree _ E E' M g Hag Hv) G0).
Qed.
Lemma a_vis_cs_gc : forall gb cs, a_vis (cs_gc gb cs) = a_vis cs /\ a_ghost (cs_gc gb cs) = a_ghost cs.
Proof. intros. unfold cs_gc. destruct (split_lit (reg cs 2)); split; reflexivity. Qed.
(* [comment removed for export] *)
Lemma run_block_gc_wb_ws_vis : forall gb wb bfuel stops cs cs' W,
  run_block_gc_wb_ws SEGS IT gb wb KC bfuel stops cs = Some (cs', W) ->
  a_vis cs' = a_vis cs /\ a_ghost cs' = a_ghost cs /\ fresh_ok gb cs = true.
Proof.
  intros gb wb bfuel stops cs cs' W H. unfold run_block_gc_wb_ws, run_block_wb_ws in H.
  destruct (fresh_ok gb cs) eqn:Hf; [|destruct wb; discriminate]. cbv zeta in H.
  match type of H with context [if ?c then _ else None] => destruct c; [|discriminate] end.
  destruct (AX2C.carryK3 _ _ _ _) as [[kn' scs] hs]. destruct scs; [|discriminate]. injection H as <- _.
  split; [|split]; [ etransitivity; [apply (proj1 (a_vis_cs_gc gb _)) | reflexivity]
                    | etransitivity; [apply (proj2 (a_vis_cs_gc gb _)) | reflexivity] | reflexivity].
Qed.
Lemma a_vis_set_kn : forall cs k, a_vis (set_kn cs k) = a_vis cs /\ a_ghost (set_kn cs k) = a_ghost cs.
Proof. intros; split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma props_ok_gkeepP : forall E E' M M' Mk fk W nx props,
  props_ok E M props -> env_agree nx E E' -> know_ok SEGS E' Mk fk ->
  (forall a, ws_out E' W a -> M' a = M a) ->
  props_ok E' M' (List.filter (AP.gkeep1E (xp_gh xp) fk W nx) props).
Proof.
  intros E E' M M' Mk fk W nx props HP Hag HK Hfr.
  unfold props_ok in *. apply Forall_forall. intros g Hg. apply filter_In in Hg as [Hin Hk].
  unfold AP.gkeep1E in Hk. apply andb_prop in Hk as [Hv Hap].
  pose proof (proj1 (Forall_forall _ _) HP g Hin) as G0.
  apply (proj1 (gholds_agree _ E E' M g Hag Hv)) in G0.
  destruct g as [i args]. unfold gholds in *. cbn [g_id g_args] in *.
  eapply GP_frame; [|exact G0]. intros a Ha. apply Hfr. intros [[wb wk] wl] Hw. cbn [fst snd].
  unfold in_fp in Ha. apply existsb_exists in Ha as ([rb rl] & Hr & Ha). cbn [fst snd] in Ha.
  apply andb_prop in Ha as [Ha1 Ha2]. apply Z.leb_le in Ha1. apply Z.ltb_lt in Ha2.
  pose proof (proj1 (forallb_forall _ _) Hap (rb, rl) Hr) as Hw1. unfold AP.fp_apartE in Hw1.
  pose proof (proj1 (forallb_forall _ _) Hw1 (SA wb wk, wl) Hw) as Hx. cbn [fst snd a_base a_off] in Hx.
  pose proof (ranges_apart_x_sound SEGS E' Mk fk wb wk wl rb 0 rl HK Hx) as X. lia.
Qed.
Lemma Mr_frameWP : forall (P : word -> Prop) E E' cs cs' m m' F F',
  (forall a, P a -> hid E' cs' m' a = hid E cs m a) -> (forall a, P a -> F' a = F a) -> forall a, P a -> Mr E' cs' m' F' a = Mr E cs m F a.
Proof. intros P E E' cs cs' m m' F F' Hh Hf a Ha. unfold Mr, mrestrict. rewrite (Hh a Ha). destruct (hid E cs m a); [reflexivity | apply Hf; exact Ha]. Qed.

Lemma cs_ok_set_props : forall E cs R FULL model l, cs_ok E cs R FULL model -> cs_ok E (set_props cs l) R FULL model.
Proof. intros E cs R FULL model l HC. destruct HC; constructor; assumption. Qed.

(* [comment removed for export] *)
Lemma props_ok_gpures : forall E E' M M' cs cs',
  props_ok E M (a_props cs) -> env_agree (nxt cs) E E' -> props_ok E' M' (a_props (gpures (xp_gh xp) cs cs')).
Proof.
  intros E E' M M' cs cs' HP Hag. unfold gpures, set_props. cbn [a_props]. unfold nxt in Hag.
  destruct (forallb (gvars_lt (s_next (a_ss cs))) (List.filter (gpure (xp_gh xp)) (a_props cs))) eqn:Hv; [|apply props_ok_nil].
  assert (HPf : props_ok E M (List.filter (gpure (xp_gh xp)) (a_props cs))).
  { unfold props_ok in *. apply Forall_forall. intros g Hg. apply (proj1 (Forall_forall _ _) HP g). exact (proj1 (proj1 (filter_In _ _ _) Hg)). }
  eapply props_ok_pure; [eapply props_ok_agree; [exact HPf | exact Hv | exact Hag]|].
  apply forallb_forall. intros g Hg. exact (proj2 (proj1 (filter_In _ _ _) Hg)).
Qed.

Lemma gatom_eqb_eq : forall a b, gatom_eqb a b = true -> a = b.
Proof.
  intros [i xs] [j ys] H. unfold gatom_eqb in H. cbn [g_id g_args] in H. apply andb_prop in H as [Hi Hl].
  apply Nat.eqb_eq in Hi. apply (list_eqb_eq expr_eqb expr_eqb_eq) in Hl. subst. reflexivity.
Qed.

Lemma vconcl_eqb_eq : forall a b, vconcl_eqb a b = true -> a = b.
Proof.
  intros [g|K] [g'|K'] H; cbn [vconcl_eqb] in H; try discriminate.
  - apply gatom_eqb_eq in H. subst. reflexivity.
  - apply kentry_eqb_eq in H. subst. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma need1_sound : forall cs c E M,
  need1 xp cs c = [] -> know_ok SEGS E M (kn cs) -> props_ok E M (a_props cs) ->
  match c with VCAtom g => gholds E M g | VCFact K => kentry_ok SEGS E M K end.
Proof.
  intros cs c E M H HK HP. unfold need1 in H. unfold props_ok in HP.
  assert (REG : forall c', g_vcok (xp_gh xp) (vc_at cs c') = true ->
                     match c' with VCAtom g => gholds E M g | VCFact K => kentry_ok SEGS E M K end).
  { intros c' Hr. pose proof (G_ok _ Hr E M HK) as Hv. cbn [vc_at vc_kn vc_hyps vc_concl] in Hv. exact (Hv HP). }
  destruct c as [g|K].
  - destruct (existsb (gatom_eqb g) (a_props cs)) eqn:Ht.
    + apply existsb_exists in Ht as [g' [Hin Heq]]. apply gatom_eqb_eq in Heq. subst g'. exact (proj1 (Forall_forall _ _) HP g Hin).
    + destruct (g_vcok (xp_gh xp) (vc_at cs (VCAtom g))) eqn:Hr; [|discriminate]. exact (REG (VCAtom g) Hr).
  - destruct (existsb (kentry_eqb K) (kn cs)) eqn:Ht.
    + apply existsb_exists in Ht as [K' [Hin Heq]]. apply kentry_eqb_eq in Heq. subst K'. exact (proj1 (Forall_forall _ _) HK K Hin).
    + destruct (g_vcok (xp_gh xp) (vc_at cs (VCFact K))) eqn:Hr; [|discriminate]. exact (REG (VCFact K) Hr).
Qed.

Lemma needs_props_sound : forall cs gs E M,
  needs_props xp cs gs = [] -> know_ok SEGS E M (kn cs) -> props_ok E M (a_props cs) -> props_ok E M gs.
Proof.
  intros cs gs E M H HK HP. unfold props_ok. apply Forall_forall. intros g Hg.
  assert (H1 : need1 xp cs (VCAtom g) = []).
  { unfold needs_props in H. destruct (need1 xp cs (VCAtom g)) as [|v r] eqn:E1; [reflexivity|]. exfalso.
    assert (X : In v (flat_map (fun g0 => need1 xp cs (VCAtom g0)) gs)) by (apply in_flat_map; exists g; split; [exact Hg | rewrite E1; left; reflexivity]).
    rewrite H in X. exact X. }
  exact (need1_sound cs (VCAtom g) E M H1 HK HP).
Qed.

(* [comment removed for export] *)
Lemma ginst_gholds : forall E M sg g, gholds E M (ginst sg g) <-> gholds (updl E sg) M g.
Proof.
  intros E M sg g. unfold gholds, ginst. cbn [g_id g_args]. rewrite map_map.
  replace (map (fun x => uE E (esubsts sg x)) (g_args g)) with (map (uE (updl E sg)) (g_args g)); [tauto|].
  apply map_ext_in. intros e _. unfold uE. rewrite esubsts_denot. reflexivity.
Qed.

Lemma props_ok_ginst : forall E M sg gs, props_ok E M (map (ginst sg) gs) -> props_ok (updl E sg) M gs.
Proof.
  intros E M sg gs HP. unfold props_ok in *. apply Forall_forall. intros g Hg.
  apply (proj1 (ginst_gholds E M sg g)). exact (proj1 (Forall_forall _ _) HP (ginst sg g) (in_map _ _ _ Hg)).
Qed.

(* [comment removed for export] *)
Lemma template_props_ok : forall cs T sg E R FULL model,
  cs_ok E cs R FULL model -> props_ok E (Mr E cs model FULL) (a_props cs) ->
  needs_props xp cs (map (ginst sg) (a_props T)) = [] ->
  hid (updl E sg) T model = hid E cs model ->
  props_ok (updl E sg) (Mr (updl E sg) T model FULL) (a_props T).
Proof.
  intros cs T sg E R FULL model HC HP Hn HH. unfold Mr. rewrite HH.
  apply props_ok_ginst. eapply needs_props_sound; [exact Hn | exact (co_know _ _ _ _ _ HC) | exact HP].
Qed.

(* [comment removed for export] *)
Lemma node_casedisj_form : forall cs b1 b2 csa csb, node_casedisj A cs b1 b2 = Some (csa, csb) ->
  exists K1 K2, csa = add_kn cs [K1] /\ csb = add_kn cs [K2].
Proof.
  intros cs b1 b2 csa csb H. unfold node_casedisj in H.
  destruct (find_disj2 (kn cs) b1 b2) as [[[[[[c1 o1] n1] c2] o2] n2]|]; [|discriminate].
  destruct (flat_x (kn cs) c1 o1 n1); [|discriminate]. destruct (flat_x (kn cs) c2 o2 n2); [|discriminate].
  destruct (disj_side_fact A (kn cs) c1 o1 n1 c2 o2) as [K1|]; [|discriminate].
  destruct (disj_side_fact A (kn cs) c2 o2 n2 c1 o1) as [K2|]; [|discriminate].
  injection H as <- <-. exists K1, K2. split; reflexivity.
Qed.
Lemma node_shdisj_form : forall cs b1 n1 b2 n2 cs1, node_shdisj A cs b1 n1 b2 n2 = Some cs1 -> exists K, cs1 = add_kn cs [K].
Proof.
  intros cs b1 n1 b2 n2 cs1 H. rewrite node_shdisj_eq in H. unfold node_shdisj_ref in H.
  destruct (split_lit b1) as [c1 o1]. destruct (split_lit b2) as [c2 o2].
  destruct (shadow_of A (kn cs) b1 n1) as [[sb1 sk1] sn1]. destruct (shadow_of A (kn cs) b2 n2) as [[sb2 sk2] sn2].
  match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
  injection H as <-. eexists. reflexivity.
Qed.
Lemma node_bump_form : forall cs m cs1, node_bump cs m = Some cs1 -> cs1 = bump cs (m - nxt cs).
Proof. intros cs m cs1 H. unfold node_bump in H. destruct (Nat.leb (nxt cs) m); [|discriminate]. injection H as <-. reflexivity. Qed.

(* [comment removed for export] *)
Lemma a_props_inst : forall inv J e, a_props (inst inv J e) = [].
Proof. reflexivity. Qed.
Lemma a_props_loop_body_state : forall J N nhi inv, a_props (loop_body_state J N nhi inv) = a_props inv.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cont_agree : forall bfuel fuel lc k cs cs' s E model D E0 M0 m0,
  CHECK bfuel fuel lc cs' k = COk s ->
  LCOK E0 M0 m0 lc D E (m_fs model) -> lc_guard lc cs = true -> D [] ->
  (forall (fy : FPState) E R FULL model, frm_zero (@fp_csr fy) -> cs_ok E cs' R FULL model ->
     props_ok E (Mr E cs' model FULL) (a_props cs') -> WI E0 M0 m0 E FULL model -> LCOK E0 M0 m0 lc D E (m_fs model) -> D [] ->
     srealizes SEGS (cfgF fy R (pc cs') FULL model) (sd D E (m_fs model) s)) ->
  forall (fy' : FPState) E' R' FULL' model',
    frm_zero (@fp_csr fy') ->
    env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' ->
    props_ok E' (Mr E' cs' model' FULL') (a_props cs') -> WI E0 M0 m0 E' FULL' model' -> m_fs model' = m_fs model ->
    srealizes SEGS (cfgF fy' R' (pc cs') FULL' model') (sd D E (m_fs model) s).
Proof.
  intros bfuel fuel lc k cs cs' s E model D E0 M0 m0 Hc HL Hg HD IH fy' E' R' FULL' model' Hz' [Hag Hag2] HC' HP' HW' Hfs.
  rewrite (sd_agree D E E' (m_fs model) s Hag (check_vars _ _ _ _ _ _ Hc)), <- Hfs.
  apply (IH fy' E' R' FULL' model' Hz' HC' HP' HW'); [|exact HD]. rewrite Hfs. eapply LCOK_agree; [exact HL | exact Hg | exact Hag2].
Qed.

(* [comment removed for export] *)
Definition seg_sem (SD : segdef) : Prop :=
  forall (K : nat -> env -> Fs.Fs -> TSet),
    (forall i E E' fs, env_agree nx0 E E' -> K i E fs = K i E' fs) ->
    (forall i E fs, K i E fs []) ->
    forall (fy : FPState) E R FULL model,
      frm_zero (@fp_csr fy) -> cs_ok E (sg_in SD) R FULL model ->
      (forall i x (fy' : FPState) E' R' F' m', nth_error (sg_outs SD) i = Some x -> frm_zero (@fp_csr fy') ->
          env_agree (sg_hi SD) E E' -> cs_ok E' x R' F' m' -> m_fs m' = m_fs model ->
          (forall a, in_windows E (sg_w SD) a = false -> F' a = FULL a) -> mvis_eq model m' ->   (* [comment removed for export] *)
          srealizes SEGS (cfgF fy' R' (pc x) F' m') (K 0%nat E' (m_fs model))) ->     (* [comment removed for export] *)
      srealizes SEGS (cfgF fy R (pc (sg_in SD)) FULL model) (sdK K t_nil E (m_fs model) (sg_shape SD)).
(* [comment removed for export] *)
Hypothesis SEGS_sound : forall sid SD0 cs SD skh, xp_sg xp sid = Some SD0 -> AP.use_view cs SD0 = Some (SD, skh) ->
  seg_sem SD /\ (AP.segdef_wf nx0 SD0 = true -> AP.segdef_wf nx0 SD = true).

(* [comment removed for export] *)
Theorem check_sound : forall fuel bfuel lc p cs s,
  CHECK bfuel fuel lc cs p = COk s ->
  forall (fy : FPState) E R FULL model D E0 M0 m0, frm_zero (@fp_csr fy) ->
  cs_ok E cs R FULL model -> props_ok E (Mr E cs model FULL) (a_props cs) -> WI E0 M0 m0 E FULL model -> LCOK E0 M0 m0 lc D E (m_fs model) -> D [] ->
  srealizes SEGS (cfgF fy R (pc cs) FULL model) (sd D E (m_fs model) s).
Proof.
  induction fuel as [|fuel IH]; intros bfuel lc p cs s Hc fy E R FULL model D E0 M0 m0 Hz HC HP HW HL HD; [discriminate|].
  cbn [AP.check] in Hc. rewrite ?AP.gkeepM_eq, ?AP.gkeepEM_eq, ?AP.gkeepPM_eq, ?AP.node_diamond_joinM_eq, ?AP.entails_hM_eq, ?AP.entails_sM_eq, ?AP.use_exitN_eqf, ?AP.instsN_eqf, ?AP.drop_ixsF_eqf in Hc.   (* [comment removed for export] *)
  match type of Hc with (if negb ?g then _ else _) = _ => destruct g eqn:Hg; [|discriminate] end. cbn [negb] in Hc.
  pose proof (LCOK_wbok _ _ _ _ _ _ _ HL) as HB.
  (* [comment removed for export] *)
  assert (CONTW : forall k cs' s', CHECK bfuel fuel lc cs' k = COk s' ->
            forall (fy' : FPState) E' R' FULL' model', frm_zero (@fp_csr fy') ->
            env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' ->
            props_ok E' (Mr E' cs' model' FULL') (a_props cs') -> WI E0 M0 m0 E' FULL' model' ->
            m_fs model' = m_fs model -> srealizes SEGS (cfgF fy' R' (pc cs') FULL' model') (sd D E (m_fs model) s')).
  { intros k cs' s' Hk. eapply cont_agree; [exact Hk | exact HL | exact Hg | exact HD | intros; eapply IH; eassumption]. }
  (* [comment removed for export] *)
  assert (CONT : xp_wb xp = None -> forall k cs' s', CHECK bfuel fuel lc cs' k = COk s' ->
            forall (fy' : FPState) E' R' FULL' model', frm_zero (@fp_csr fy') ->
            env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' ->
            props_ok E' (Mr E' cs' model' FULL') (a_props cs') ->
            m_fs model' = m_fs model -> srealizes SEGS (cfgF fy' R' (pc cs') FULL' model') (sd D E (m_fs model) s')).
  { intros HN k cs' s' Hk fy' E' R' FULL' model' Hz' Hag HC' HP' Hfs. exact (CONTW k cs' s' Hk fy' E' R' FULL' model' Hz' Hag HC' HP' (WI_none _ _ _ _ _ _ HN) Hfs). }
  (* [comment removed for export] *)
  assert (CONTF : xp_wb xp = None -> forall k cs' s', CHECK bfuel fuel lc cs' k = COk s' ->
            forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' ->
            props_ok E' (Mr E' cs' model' FULL') (a_props cs') ->
            m_fs model' = m_fs model -> srealizes SEGS (cfgF fy R' (pc cs') FULL' model') (sd D E (m_fs model) s')).
  { intros HN k cs' s' Hk E' R' FULL' model'. exact (CONT HN k cs' s' Hk fy E' R' FULL' model' Hz). }
  (* [comment removed for export] *)
  assert (CONTE : forall k cs' s', CHECK bfuel fuel lc cs' k = COk s' ->
            forall E' R' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL model' ->
            props_ok E' (Mr E' cs' model' FULL) (a_props cs') ->
            m_fs model' = m_fs model -> mvis_eq model model' -> srealizes SEGS (cfgF fy R' (pc cs') FULL model') (sd D E (m_fs model) s')).
  { intros k cs' s' Hk E' R' model' Hag HC' HP' Hfs Hmv.
    exact (CONTW k cs' s' Hk fy E' R' FULL model' Hz Hag HC' HP' (WI_mv _ _ _ _ _ _ _ (WI_agree _ _ _ _ _ _ _ _ _ _ _ _ HW HL Hg (proj2 Hag)) Hmv) Hfs). }
  assert (SAME : forall k cs' s', CHECK bfuel fuel lc cs' k = COk s' -> cs_ok E cs' R FULL model ->
            props_ok E (Mr E cs' model FULL) (a_props cs') ->
            srealizes SEGS (cfgF fy R (pc cs') FULL model) (sd D E (m_fs model) s')).
  { intros k cs' s' Hk HC' HP'. refine (CONTE k cs' s' Hk E R model (conj (env_agree_refl _ _) (env_agree_refl _ _)) HC' HP' eq_refl (mvis_refl _)). }
  (* [comment removed for export] *)
  assert (GWa : forall (b : bool) (r : cres), (if (AP.wbb xp && b)%bool then CErr 11 p cs else r) = COk s -> r = COk s)
    by (intros b r Hr; destruct (AP.wbb xp && b)%bool; [discriminate | exact Hr]).
  assert (GW : forall r : cres, (if AP.wbb xp then CErr 11 p cs else r) = COk s -> xp_wb xp = None /\ r = COk s).
  { intros r Hr. unfold AP.wbb in Hr. destruct (xp_wb xp); [discriminate | split; [reflexivity | exact Hr]]. }
  (* [comment removed for export] *)
  assert (GWS : forall ows (r : cres), (if negb (AP.okW xp ows cs) then CErr 11 p cs else r) = COk s ->
            (xp_wb xp = None \/ exists ws, ows = Some ws /\ AP.okW xp ows cs = true) /\ r = COk s).
  { intros ows r Hr. destruct (AP.okW xp ows cs) eqn:Hok; [|discriminate]. split; [|exact Hr].
    unfold AP.okW in Hok. destruct (xp_wb xp) as [[W wlo]|]; [|left; reflexivity]. right.
    destruct ows as [ws|]; [|discriminate]. exists ws. split; reflexivity. }
  (* [comment removed for export] *)
  assert (CONTS : forall ows ws, (xp_wb xp = None \/ exists ws', ows = Some ws' /\ AP.okW xp ows cs = true) -> ows = Some ws ->
            forall k cs' s', CHECK bfuel fuel lc cs' k = COk s' ->
            forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' ->
            props_ok E' (Mr E' cs' model' FULL') (a_props cs') ->
            m_fs model' = m_fs model -> (forall a, ws_out E ws a -> FULL' a = FULL a) -> mvis_eq model model' ->
            srealizes SEGS (cfgF fy R' (pc cs') FULL' model') (sd D E (m_fs model) s')).
  { intros ows ws HNW Hows k cs' s' Hk E' R' FULL' model' Hag HC' HP' Hfs Hfr Hmv.
    assert (Hok : AP.okW xp ows cs = true).
    { destruct HNW as [HN|[ws' [E1 E2]]]; [unfold AP.okW; rewrite HN; reflexivity | exact E2]. }
    exact (CONTW k cs' s' Hk fy E' R' FULL' model' Hz Hag HC' HP'
             (WI_ws _ _ _ _ _ _ _ _ _ _ _ _ _ _ ows ws _ HW HL Hg (proj2 Hag) Hok Hows (facts_of_ok SEGS E _ _ (co_know _ _ _ _ _ HC)) Hfr Hmv) Hfs). }
  destruct p as [stops k|e mid k1 k2|ce cmid ck1 ck2|db1 db2 dk1 dk2|sb1 sn1 sb2 sn2 k| |K k|jb joff jn k|ixs k|db dn k|gws k|bm k|hrs k|hbK k|r logc fb k|y k|ma|ib|qb|ka|x args k|xid xargs k|eid eargs k|bid bargs kb1 kb2|lJ lN linv lbody lk| |h| | |fi fsz fk|gi gsz gk|gb gn gk2|ub un uk|hlo hhi hk|ilo ihi ik|djp drs dk|rnm rnk|cpk|vj vjs vlo vka vk|mj|ab an ak|hws hwk|rsr rse rsk|wlo wheads wV wxs wexits|nh nwh|bi bh|usid uhints uks|gg gk|gi gdk|gK gfk|gtx gti gtK gtfk|sh slo shints|kga kgf|jjb1 jjb2 jjp jrs jk].
  - (* [comment removed for export] *)
    destruct (run_block_gc_wb_ws SEGS IT _ (AP.WB xp) KC bfuel (stops ++ STOPS A) cs) as [[cs1 W]|] eqn:Hrb; [|discriminate].
    pose proof (LCOK_bnd E0 M0 m0 lc D E (m_fs model) HL) as Hgb.
    eapply run_block_gc_wb_ws_sound; [exact Hz | exact Hgb | exact Hrb | exact HC | exact HW | exact (WB_run _ _ _ _ _ _ _ _ HL Hg) |].
    intros fy' E' R' FULL' model' Hz' Hag HC1 HW1 Hfs HW8 Hmr.
    lazymatch type of Hc with (if ?c then _ else _) = _ => destruct c end.   (* [comment removed for export] *)
    + exact (CONTW (PRun stops k) (gkeep (xp_gh xp) W cs cs1) s Hc fy' E' R' FULL' model' Hz' Hag (cs_ok_set_props _ _ _ _ _ _ HC1)
               (props_ok_gkeep _ _ _ _ _ cs cs1 W HP (proj2 Hag) (co_know _ _ _ _ _ HC1) HW8 Hmr) HW1 Hfs).
    + exact (CONTW k (gkeep (xp_gh xp) W cs cs1) s Hc fy' E' R' FULL' model' Hz' Hag (cs_ok_set_props _ _ _ _ _ _ HC1)
               (props_ok_gkeep _ _ _ _ _ cs cs1 W HP (proj2 Hag) (co_know _ _ _ _ _ HC1) HW8 Hmr) HW1 Hfs).
  - (* [comment removed for export] *)
    destruct (AP.expr_vars_lt nx0 e) eqn:Hv; [|discriminate].
    destruct (erange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
    destruct (Z.leb lo mid && Z.ltb mid hi)%bool.
    2: { (* [comment removed for export] *)
         pose proof (erange_sound SEGS E _ (kn cs) e lo hi (co_know _ _ _ _ _ HC) Hr) as Hb.
         destruct (Z.leb_spec hi mid) as [Hle|Hgt]; [exact (SAME k1 _ s Hc HC HP) | exact (SAME k2 _ s Hc HC HP)]. }
    apply cmerge_ok in Hc as (s1 & s2 & H1 & H2 & Hc). cbn beta in H2.
    injection Hc as <-. cbn [sd].
    destruct (split_sound cs e mid lo hi E R FULL model HC Hr) as [HCl HCr].
    destruct (Z.leb_spec (bv_unsigned (edenot E e)) mid) as [Hle|Hgt].
    + exact (SAME k1 _ s1 H1 (HCl Hle) HP).
    + exact (SAME k2 _ s2 H2 (HCr ltac:(lia)) HP).
  - (* [comment removed for export] *)
    destruct (AP.erange_any (kn cs) ce) as [[lo hi]|] eqn:Hr; [|discriminate].
    destruct (Z.leb lo cmid && Z.ltb cmid hi)%bool.
    2: { cbn [negb] in Hc. destruct (Z.leb hi cmid); [exact (SAME ck1 _ s Hc HC HP) | exact (SAME ck2 _ s Hc HC HP)]. }
    cbn [negb] in Hc. cbv zeta in Hc.
    destruct (split_sound_any cs ce cmid lo hi E R FULL model HC Hr) as [HCl HCr].
    destruct (kn_contra (kn (set_kn cs (KRange ce lo cmid :: kn cs)))) eqn:Hk1.
    { destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
      - exfalso. exact (kn_contra_sound E _ _ (co_know _ _ _ _ _ (HCl Hle)) Hk1).
      - exact (SAME ck2 _ s Hc (HCr ltac:(lia)) HP). }
    destruct (kn_contra (kn (set_kn cs (KRange ce (cmid + 1) hi :: kn cs)))) eqn:Hk2.
    { destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
      - exact (SAME ck1 _ s Hc (HCl Hle) HP).
      - exfalso. exact (kn_contra_sound E _ _ (co_know _ _ _ _ _ (HCr ltac:(lia))) Hk2). }
    apply cmerge_ok in Hc as (s1 & s2 & H1 & H2 & Hc). cbn beta in H2.
    match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hse; [|discriminate] end. injection Hc as <-.   (* [comment removed for export] *)
    destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
    + exact (SAME ck1 _ s1 H1 (HCl Hle) HP).
    + rewrite <- (shape_ok2 s1 s2 Hse). exact (SAME ck2 _ s2 H2 (HCr ltac:(lia)) HP).
  - (* [comment removed for export] *)
    destruct (node_casedisj A cs db1 db2) as [[csa csb]|] eqn:Hn; [|discriminate].
    apply cmerge_ok in Hc as (s1 & s2 & H1 & H2 & Hc). cbn beta in H2.
    match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hse; [|discriminate] end. injection Hc as <-.   (* [comment removed for export] *)
    destruct (casedisj_sound cs db1 db2 csa csb E R FULL model HC Hn) as [[HC' Hpc]|[HC' Hpc]]; rewrite <- Hpc;
      destruct (node_casedisj_form cs db1 db2 csa csb Hn) as (K1 & K2 & Ea & Eb).
    + subst csa. exact (SAME dk1 _ s1 H1 HC' HP).
    + subst csb. rewrite <- (shape_ok2 s1 s2 Hse). exact (SAME dk2 _ s2 H2 HC' HP).
  - (* [comment removed for export] *)
    destruct (node_shdisj A cs sb1 sn1 sb2 sn2) as [cs1|] eqn:Hn; [|discriminate].
    destruct (shdisj_sound cs sb1 sn1 sb2 sn2 cs1 E R FULL model HC Hn) as [HC' Hpc]. rewrite <- Hpc.
    destruct (node_shdisj_form cs sb1 sn1 sb2 sn2 cs1 Hn) as [K1 ->]. exact (SAME k _ s Hc HC' HP).
  - (* [comment removed for export] *)
    destruct (kn_contra (kn cs)) eqn:Hk; [|discriminate]. exfalso.
    exact (kn_contra_sound E _ (kn cs) (co_know _ _ _ _ _ HC) Hk).
  - (* [comment removed for export] *)
    destruct (fact_ok (kn cs) K || AP.fact_okL (kn cs) K)%bool eqn:Hf; [|discriminate].
    exact (SAME k _ s Hc (fact_soundL E cs R FULL model K HC Hf) HP).
  - (* [comment removed for export] *)
    apply GW in Hc as [HN Hc].
    destruct (node_join SEGS cs jb joff jn) as [cs1|] eqn:Hn; [|discriminate].
    eapply (@node_join_sound fy jb joff jn cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |].
    exact (fun E' R' m' Hag HC' Hfs Hmv Hhid => CONTE k (AP.gkeepE (xp_gh xp) [] cs cs1) s Hc E' R' m' Hag (cs_ok_set_props _ _ _ _ _ _ HC')
             (props_ok_gkeepE E E' _ _ _ _ [] (nxt cs) (a_props cs) HP (proj2 Hag) (facts_of_ok SEGS E _ _ (co_know _ _ _ _ _ HC))
                (Mr_frameW _ E E' cs cs1 model m' FULL FULL Hhid (fun a _ => eq_refl))) Hfs Hmv).
  - (* [comment removed for export] *)
    exact (SAME k _ s Hc (forget_sound E cs R FULL model ixs HC) HP).
  - (* [comment removed for export] *)
    assert (Hpc : pc (node_droprange cs db dn) = pc cs) by (unfold node_droprange; destruct (split_lit db); reflexivity).
    rewrite <- Hpc.
    assert (HP' : props_ok E (Mr E (node_droprange cs db dn) model FULL) (a_props (node_droprange cs db dn))) by (unfold node_droprange; destruct (split_lit db); exact HP).
    exact (SAME k _ s Hc (droprange_sound E cs R FULL model db dn HC) HP').
  - (* [comment removed for export] *)
    rewrite <- (pc_set_kn cs (kn_keep (kn cs) gws)).
    exact (SAME k _ s Hc (cs_ok_set_kn E cs R FULL model _ HC (know_ok_filter E _ _ (kn cs) (co_know _ _ _ _ _ HC))) HP).
  - (* [comment removed for export] *)
    destruct (node_bump cs bm) as [cs1|] eqn:Hn; [|discriminate].
    destruct (bump_sound E cs R FULL model bm cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    pose proof (node_bump_form cs bm cs1 Hn) as Ecs1.
    assert (HP1 : props_ok E (Mr E cs1 model FULL) (a_props cs1)) by (rewrite Ecs1; exact HP).
    exact (SAME k _ s Hc HC1 HP1).
  - (* [comment removed for export] *)
    destruct (node_havoc nx0 cs hrs) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havoc_sound E cs R FULL model hrs cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    destruct (node_havoc_neutral _ _ _ Hn) as [Hf1 Hv1].
    exact (CONTE k (AP.gkeepE (xp_gh xp) [] cs cs1) s Hc E' R model Hag (cs_ok_set_props _ _ _ _ _ _ HC1)
             (props_ok_gkeepE E E' _ _ _ _ [] (nxt cs) (a_props cs) HP (proj2 Hag) (facts_of_ok SEGS E _ _ (co_know _ _ _ _ _ HC))
                (Mr_frameW _ E E' cs cs1 model model FULL FULL (hid_memneutral E E' cs cs1 model Hf1 Hv1 (proj2 Hag)) (fun a _ => eq_refl))) eq_refl (mvis_refl _)).
  - (* [comment removed for export] *)
    destruct (node_havocbig nx0 cs hbK) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havocbig_sound E cs R FULL model hbK cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    destruct (node_havocbig_neutral _ _ _ Hn) as [Hf1 Hv1].
    exact (CONTE k (AP.gkeepE (xp_gh xp) [] cs cs1) s Hc E' R model Hag (cs_ok_set_props _ _ _ _ _ _ HC1)
             (props_ok_gkeepE E E' _ _ _ _ [] (nxt cs) (a_props cs) HP (proj2 Hag) (facts_of_ok SEGS E _ _ (co_know _ _ _ _ _ HC))
                (Mr_frameW _ E E' cs cs1 model model FULL FULL (hid_memneutral E E' cs cs1 model Hf1 Hv1 (proj2 Hag)) (fun a _ => eq_refl))) eq_refl (mvis_refl _)).
  - (* [comment removed for export] *)
    apply GW in Hc as [HN Hc].
    destruct (node_fresh nx0 cs r logc fb) as [cs1|] eqn:Hn; [|discriminate].
    destruct (node_fresh_soundL r logc fb cs cs1 E R FULL model HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    destruct (node_fresh_neutral _ _ _ _ _ Hn) as [Hf1 Hv1].
    exact (CONTE k (AP.gkeepE (xp_gh xp) [] cs cs1) s Hc E' R model Hag (cs_ok_set_props _ _ _ _ _ _ HC1)
             (props_ok_gkeepE E E' _ _ _ _ [] (nxt cs) (a_props cs) HP (proj2 Hag) (facts_of_ok SEGS E _ _ (co_know _ _ _ _ _ HC))
                (Mr_frameW _ E E' cs cs1 model model FULL FULL (hid_memneutral E E' cs cs1 model Hf1 Hv1 (proj2 Hag)) (fun a _ => eq_refl))) eq_refl (mvis_refl _)).
  - (* [comment removed for export] *)
    unfold AP.sys_okW in Hc. apply GWS in Hc as [HNW Hc].
    apply GWa in Hc.   (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_sys A nx0 y cs) as [cs1|] eqn:Hn; [|discriminate].
    destruct (xp_sysws xp y cs) as [ws|] eqn:Hws.
    + eapply (@node_sysW_sound fy y cs ws Hws cs1 E R FULL model); [exact HC | exact Hec | exact Hn |].
      exact (fun E' R' F' m' Hag HC' Hfs Hfr Hmv Hhid => CONTS _ ws HNW eq_refl k (AP.gkeepE (xp_gh xp) ws cs cs1) s Hc E' R' F' m' Hag (cs_ok_set_props _ _ _ _ _ _ HC')
               (props_ok_gkeepE E E' _ _ _ _ ws (nxt cs) (a_props cs) HP (proj2 Hag) (facts_of_ok SEGS E _ _ (co_know _ _ _ _ _ HC)) (Mr_frameW _ E E' cs cs1 model m' FULL F' Hhid Hfr)) Hfs Hfr Hmv).
    + destruct HNW as [HN|[ws' [E1 _]]]; [|discriminate E1].
      destruct (AP.sys_frame A y cs) as [Wf|] eqn:Hsf.
      * (* [comment removed for export] *)
        eapply (@node_sys_sound fy y cs cs1 E R FULL model); [exact HC | exact Hec | exact Hn |].
        exact (fun E' R' F' m' Hag HC' Hfs Hmr => CONTF HN k (AP.gkeepE (xp_gh xp) Wf cs cs1) s Hc E' R' F' m' Hag (cs_ok_set_props _ _ _ _ _ _ HC')
                 (props_ok_gkeepE E E' _ _ _ _ Wf (nxt cs) (a_props cs) HP (proj2 Hag) (facts_of_ok SEGS E _ _ (co_know _ _ _ _ _ HC)) (fun a Ha => Hmr Wf a Hsf Ha)) Hfs).
      * eapply (@node_sys_sound fy y cs cs1 E R FULL model); [exact HC | exact Hec | exact Hn |]. exact (fun E' R' F' m' Hag HC' Hfs _ => CONTF HN k (gpures (xp_gh xp) cs cs1) s Hc E' R' F' m' Hag (cs_ok_set_props _ _ _ _ _ _ HC') (props_ok_gpures _ _ _ _ cs cs1 HP (proj2 Hag)) Hfs).
  - (* [comment removed for export] *)
    apply GW in Hc as [HN Hc].
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mmap A nx0 LIMIT cs) as [cs1|] eqn:Hn; [|discriminate].
    eapply (@node_mmap_sound fy cs cs1 E R FULL model); [exact HC | exact Hec | exact Hn |].
    destruct (AP.mmap_win A cs1) as [W|] eqn:HWm.
    + exact (fun E' R' F' m' Hag HC' Hfs Hfr Hhid => CONTF HN ma (AP.gkeepP (xp_gh xp) W cs cs1) s Hc E' R' F' m' Hag (cs_ok_set_props _ _ _ _ _ _ HC')
             (props_ok_gkeepP E E' _ _ _ _ W (nxt cs) (a_props cs) HP (proj2 Hag) (facts_of_ok SEGS E' _ _ (co_know _ _ _ _ _ HC'))
                (Mr_frameWP _ E E' cs cs1 model m' FULL F' (fun a Ha => Hhid W a eq_refl Ha) (fun a Ha => Hfr W a eq_refl Ha))) Hfs).
    + exact (fun E' R' F' m' Hag HC' Hfs _ _ => CONTF HN ma (gpures (xp_gh xp) cs cs1) s Hc E' R' F' m' Hag (cs_ok_set_props _ _ _ _ _ _ HC') (props_ok_gpures _ _ _ _ cs cs1 HP (proj2 Hag)) Hfs).
  - (* [comment removed for export] *)
    apply GW in Hc as [HN Hc].
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mmapin A LIMIT cs) as [cs1|] eqn:Hn; [|discriminate].
    eapply (@node_mmapin_sound fy cs cs1 E R FULL model); [exact HC | exact Hec | exact Hn |]. exact (fun E' R' F' m' Hag HC' Hfs => CONTF HN ib (gpures (xp_gh xp) cs cs1) s Hc E' R' F' m' Hag (cs_ok_set_props _ _ _ _ _ _ HC') (props_ok_gpures _ _ _ _ cs cs1 HP (proj2 Hag)) Hfs).
  - (* [comment removed for export] *)
    apply GW in Hc as [HN Hc].
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mprotect A LIMIT cs) as [cs1|] eqn:Hn; [|discriminate].
    eapply (@node_mprotect_sound fy cs cs1 E R FULL model); [exact HC | exact Hec | exact Hn |]. exact (fun E' R' F' m' Hag HC' Hfs => CONTF HN qb (gpures (xp_gh xp) cs cs1) s Hc E' R' F' m' Hag (cs_ok_set_props _ _ _ _ _ _ HC') (props_ok_gpures _ _ _ _ cs cs1 HP (proj2 Hag)) Hfs).
  - (* [comment removed for export] *)
    apply GW in Hc as [HN Hc]. discriminate Hc.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    unfold AP.x_okW in Hc. apply GWS in Hc as [HNW Hc].
    destruct (node_x SEGS A nx0 x args cs) as [cs1|] eqn:Hn; [|discriminate].
    destruct (xp_xws xp x args cs) as [ws|] eqn:Hws; cbn [AP.gsuccW] in Hc; rewrite ?AP.gkeepEM_eq in Hc.
    + eapply (@node_xW_sound fy x args cs ws Hws cs1 E R FULL model); [exact HC | reflexivity | exact Hn |].
      exact (fun E' R' F' m' Hag HC' Hfs Hfr Hmv Hhid => CONTS _ ws HNW eq_refl k (AP.gkeepE (xp_gh xp) ws cs cs1) s Hc E' R' F' m' Hag (cs_ok_set_props _ _ _ _ _ _ HC')
               (props_ok_gkeepE E E' _ _ _ _ ws (nxt cs) (a_props cs) HP (proj2 Hag) (facts_of_ok SEGS E _ _ (co_know _ _ _ _ _ HC)) (Mr_frameW _ E E' cs cs1 model m' FULL F' Hhid Hfr)) Hfs Hfr Hmv).
    + destruct HNW as [HN|[ws' [E1 _]]]; [|discriminate E1].
      eapply (@node_x_sound fy x args cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |]. exact (fun E' R' F' m' Hag HC' Hfs => CONTF HN k (gpures (xp_gh xp) cs cs1) s Hc E' R' F' m' Hag (cs_ok_set_props _ _ _ _ _ _ HC') (props_ok_gpures _ _ _ _ cs cs1 HP (proj2 Hag)) Hfs).
  - (* [comment removed for export] *)
    unfold AP.ext_okW in Hc.
    destruct (xp_extG xp xid) eqn:HxG.
    { (* [comment removed for export] *)
      match type of Hc with (if negb ?b then _ else _) = _ => destruct b; [|discriminate] end. cbn [negb] in Hc.
      apply GW in Hc as [HN Hc].
      destruct (XN xid xargs cs) as [cs1|] eqn:Hn; [|discriminate].
      eapply (@node_extG_sound fy xid HxG xargs cs cs1 E R FULL model); [exact HC | exact HP | exact Hn |].
      intros E' R' F' m' Hag HC' HPn Hfs.
      exact (CONTF HN k cs1 s Hc E' R' F' m' Hag HC' HPn Hfs). }
    destruct (xp_extF xp xid) eqn:HxF.
    + cbn [orb negb] in Hc. destruct (XN xid xargs cs) as [cs1|] eqn:Hn; [|discriminate].
      eapply (@node_extF_sound fy xid HxF xargs cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |].
      exact (fun E' R' m' Hag HC' Hfs Hmv Hhid => CONTE k (AP.gkeepE (xp_gh xp) [] cs cs1) s Hc E' R' m' Hag (cs_ok_set_props _ _ _ _ _ _ HC')
               (props_ok_gkeepE E E' _ _ _ _ [] (nxt cs) (a_props cs) HP (proj2 Hag) (facts_of_ok SEGS E _ _ (co_know _ _ _ _ _ HC))
                  (Mr_frameW _ E E' cs cs1 model m' FULL FULL Hhid (fun a _ => eq_refl))) Hfs Hmv).
    + cbn [orb] in Hc. apply GWS in Hc as [HNW Hc].
      destruct (XN xid xargs cs) as [cs1|] eqn:Hn; [|discriminate].
      destruct (xp_xnws xp xid xargs cs) as [ws|] eqn:Hws; cbn [AP.gsuccW] in Hc; rewrite ?AP.gkeepEM_eq in Hc.
      * eapply (@node_extW_sound fy xid xargs cs ws Hws cs1 E R FULL model); [exact HC | reflexivity | exact Hn |].
        exact (fun E' R' F' m' Hag HC' Hfs Hfr Hmv Hhid => CONTS _ ws HNW eq_refl k (AP.gkeepE (xp_gh xp) ws cs cs1) s Hc E' R' F' m' Hag (cs_ok_set_props _ _ _ _ _ _ HC')
               (props_ok_gkeepE E E' _ _ _ _ ws (nxt cs) (a_props cs) HP (proj2 Hag) (facts_of_ok SEGS E _ _ (co_know _ _ _ _ _ HC)) (Mr_frameW _ E E' cs cs1 model m' FULL F' Hhid Hfr)) Hfs Hfr Hmv).
      * destruct HNW as [HN|[ws' [E1 _]]]; [|discriminate E1].
        eapply (@node_ext_sound fy xid HxG xargs cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |]. exact (fun E' R' F' m' Hag HC' Hfs => CONTF HN k (gpures (xp_gh xp) cs cs1) s Hc E' R' F' m' Hag (cs_ok_set_props _ _ _ _ _ _ HC') (props_ok_gpures _ _ _ _ cs cs1 HP (proj2 Hag)) Hfs).
  - (* [comment removed for export] *)
    unfold AP.emit_okW in Hc. apply GWS in Hc as [HNW Hc].
    destruct (XE eid eargs cs) as [[[fd ps] cs1]|] eqn:Hn; [|discriminate].
    destruct (xp_xews xp eid eargs cs) as [ws|] eqn:Hws; cbn [AP.gsuccW] in Hc; rewrite ?AP.gkeepEM_eq in Hc.
    + destruct (CHECK bfuel fuel lc (AP.gkeepE (xp_gh xp) ws cs cs1) k) as [s1| |] eqn:H1; [|discriminate|discriminate]. injection Hc as <-. cbn [sd].
      eapply (@node_emitW_sound fy eid eargs cs ws Hws fd ps cs1 E R FULL model); [exact HC | exact Hn | apply sd_has_nil; exact HD |].
      exact (fun E' R' F' m' Hag HC' Hfs Hfr Hmv Hhid => CONTS _ ws HNW eq_refl k (AP.gkeepE (xp_gh xp) ws cs cs1) s1 H1 E' R' F' m' Hag (cs_ok_set_props _ _ _ _ _ _ HC')
               (props_ok_gkeepE E E' _ _ _ _ ws (nxt cs) (a_props cs) HP (proj2 Hag) (facts_of_ok SEGS E _ _ (co_know _ _ _ _ _ HC)) (Mr_frameW _ E E' cs cs1 model m' FULL F' Hhid Hfr)) Hfs Hfr Hmv).
    + destruct (CHECK bfuel fuel lc (gpures (xp_gh xp) cs cs1) k) as [s1| |] eqn:H1; [|discriminate|discriminate]. injection Hc as <-. cbn [sd].
      destruct HNW as [HN|[ws' [E1 _]]]; [|discriminate E1].
      eapply (@node_emit_sound fy eid eargs cs fd ps cs1 E R FULL model); [exact HC | exact Hn | apply sd_has_nil; exact HD |]. exact (fun E' R' F' m' Hag HC' Hfs => CONTF HN k (gpures (xp_gh xp) cs cs1) s1 H1 E' R' F' m' Hag (cs_ok_set_props _ _ _ _ _ _ HC') (props_ok_gpures _ _ _ _ cs cs1 HP (proj2 Hag)) Hfs).
  - (* [comment removed for export] *)
    apply GW in Hc as [HN Hc].
    destruct (XB bid bargs cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    apply cmerge_ok in Hc as (sa & sb & H1 & H2 & Hc). cbn beta in H2.
    injection Hc as <-. cbn [sd].
    eapply (@node_ext2_sound fy bid bargs cs csa csb E R FULL model); [exact HC | exact Hn | exact (fun E' R' F' m' Hag HC' Hfs => CONTF HN kb1 (gpures (xp_gh xp) cs csa) sa H1 E' R' F' m' Hag (cs_ok_set_props _ _ _ _ _ _ HC') (props_ok_gpures _ _ _ _ cs csa HP (proj2 Hag)) Hfs) | exact (fun E' R' F' m' Hag HC' Hfs => CONTF HN kb2 (gpures (xp_gh xp) cs csb) sb H2 E' R' F' m' Hag (cs_ok_set_props _ _ _ _ _ _ HC') (props_ok_gpures _ _ _ _ cs csb HP (proj2 Hag)) Hfs)].
  - (* [comment removed for export] *)
    apply GW in Hc as [HN Hc].
    destruct (a_props linv) eqn:Hpl; [|discriminate]. cbn [negb] in Hc.
    destruct (loop_ok nx0 cs lJ lN linv) as [nhi|] eqn:Hlo; [|discriminate].
    destruct (Z.eqb (pc linv) (pc cs) && entails_h A (Datatypes.S lJ) (nxt linv) cs (inst linv lJ (ELit 0)))%bool eqn:Ht; [|discriminate].
    apply andb_prop in Ht as [Hpc Hent]. apply Z.eqb_eq in Hpc.
    destruct (CHECK bfuel fuel (Some (LC (pc cs) (inst linv lJ (eaddz (EVar lJ) 1)) (Datatypes.S lJ) (nxt linv))) (loop_body_state lJ lN nhi linv) lbody) as [sb| |] eqn:Hbody; [|discriminate|discriminate].
    destruct sb; try discriminate. rename Hc into Hk.
    destruct (loop_ok_facts cs lJ lN linv nhi Hlo) as (Ffr & FJ & FJh & Flog & Flen & FvN & FxN & Fnhi).
    destruct (fresh_ok_parts cs Ffr) as (_ & _ & _ & _ & _ & _ & Fle).
    pose proof (xhi_sound SEGS E _ (kn cs) lN nhi (co_know _ _ _ _ _ HC) FxN) as HNv.
    set (Nv := bv_unsigned (edenot E lN)) in *. pose proof (u64_range (edenot E lN)) as RN. fold Nv in RN.
    set (D0 := sd D E (m_fs model) s).
    assert (HD0 : D0 []) by (apply sd_has_nil; exact HD).
    set (h := pc cs) in *.
    (* [comment removed for export] *)
    assert (Q : forall m j (fy2 : FPState) E' R' F' m', frm_zero (@fp_csr fy2) -> j = Nv - Z.of_nat m -> 0 <= j -> env_agree (nxt cs) E E' ->
               cs_ok E' (inst linv lJ (ELit j)) R' F' m' -> m_fs m' = m_fs model ->
               srealizes SEGS (cfgF fy2 R' h F' m') D0).
    { induction m as [|m IHm]; intros j fy2 E' R' F' m' Hz2 Hj Hj0 Hag HCj Hfs.
      - (* [comment removed for export] *)
        assert (HNe : edenot E' lN = edenot E' (ELit j)).
        { cbn [edenot]. rewrite <- (edenot_agree' (nxt cs) E E' lN Hag FvN). apply bv_eq. rewrite u_small by lia. cbn in Hj. lia. }
        assert (HCN : cs_ok E' (inst linv lJ lN) R' F' m').
        { apply (proj2 (cs_ok_inst E' lJ lN linv R' F' m' ltac:(lia) Flog)). rewrite HNe.
          apply (proj1 (cs_ok_inst E' lJ (ELit j) linv R' F' m' ltac:(lia) Flog)). exact HCj. }
        unfold D0. rewrite (sd_agree D E E' (m_fs model) s ltac:(eapply env_agree_le; [exact Hag | exact Fle]) (check_vars _ _ _ _ _ _ Hk)).
        rewrite <- Hfs. replace h with (pc (inst linv lJ lN)) by (unfold h; rewrite pc_inst; exact Hpc).
        apply (IH bfuel lc lk _ s Hk fy2 E' R' F' m' D E0 M0 m0 Hz2 HCN ltac:(rewrite a_props_inst; apply props_ok_nil) (WI_none _ _ _ _ _ _ HN)); [|exact HD].
        rewrite Hfs. eapply LCOK_agree; [exact HL | exact Hg | exact Hag].
      - (* [comment removed for export] *)
        set (E'' := upd E' lJ (Z_to_bv 64 j)).
        assert (Hjlt : j < Nv) by lia.
        assert (HCinv : cs_ok E'' linv R' F' m').
        { unfold E''. replace (Z_to_bv 64 j) with (edenot E' (ELit j)) by reflexivity.
          apply (proj1 (cs_ok_inst E' lJ (ELit j) linv R' F' m' ltac:(lia) Flog)). exact HCj. }
        assert (Hag'' : env_agree (nxt cs) E E'').
        { eapply env_agree_trans; [exact Hag|]. eapply env_agree_le; [apply upd_agree | exact FJ]. }
        assert (HNE'' : edenot E'' lN = edenot E lN) by (symmetry; eapply (edenot_agree' (nxt cs)); [exact Hag'' | exact FvN]).
        assert (HJ'' : ev E'' lJ = Z_to_bv 64 j) by (unfold E''; apply upd_at).
        assert (HCb : cs_ok E'' (loop_body_state lJ lN nhi linv) R' F' m').
        { unfold loop_body_state, add_kn. apply cs_ok_set_kn; [exact HCinv|]. apply Forall_app. split; [|exact (co_know _ _ _ _ _ HCinv)].
          constructor; [|constructor; [|constructor]]; cbn [kentry_ok edenot].
          - rewrite HJ'', u_small by lia. lia.
          - unfold esub. rewrite mkAlu_denot, u_sub64. cbn [edenot]. rewrite HNE'', HJ''. fold Nv. rewrite u_small by lia.
            rewrite Z.mod_small by lia. lia. }
        replace h with (pc (loop_body_state lJ lN nhi linv)) by exact Hpc.
        refine (IH bfuel _ lbody _ SNext Hbody fy2 E'' R' F' m' D0 E0 M0 m0 Hz2 HCb ltac:(rewrite a_props_loop_body_state, Hpl; apply props_ok_nil) (WI_none _ _ _ _ _ _ HN) _ HD0).
        (* [comment removed for export] *)
        split; [unfold WBOK; rewrite HN; exact I|]. cbn [LCOK]. split.
        { split; [lia|]. split; [lia|]. unfold inst. cbn [a_ss s_regs mk_ss]. rewrite length_map. exact Flen. }
        intros fy3 E3 R3 F3 m3 Hz3 Hag3 HC3 _ Hfs3.
        assert (HJ3 : ev E3 lJ = Z_to_bv 64 j) by (rewrite <- HJ''; symmetry; apply (proj1 Hag3); lia).
        assert (Hnext : edenot E3 (eaddz (EVar lJ) 1) = Z_to_bv 64 (j + 1)).
        { unfold eaddz. rewrite mkAlu_denot. cbn [edenot]. rewrite HJ3. apply bv_eq. rewrite u_add64, !u_small by lia. rewrite Z.mod_small by lia. reflexivity. }
        set (E4 := upd E3 lJ (Z_to_bv 64 (j + 1))).
        apply (IHm (j + 1) fy3 E4 R3 F3 m3); [exact Hz3 | lia | lia | | | rewrite Hfs3; exact Hfs].
        + eapply env_agree_trans; [exact Hag''|]. eapply env_agree_trans; [eapply env_agree_le; [exact Hag3 | lia]|].
          eapply env_agree_le; [apply upd_agree | exact FJ].
        + apply (proj2 (cs_ok_inst E4 lJ (ELit (j + 1)) linv R3 F3 m3 ltac:(lia) Flog)).
          unfold E4. cbn [edenot]. rewrite upd_upd. rewrite <- Hnext.
          apply (proj1 (cs_ok_inst E3 lJ (eaddz (EVar lJ) 1) linv R3 F3 m3 ltac:(lia) Flog)). exact HC3. }
    (* [comment removed for export] *)
    destruct (entails_h_sound (Datatypes.S lJ) (nxt linv) E cs (inst linv lJ (ELit 0)) R FULL model HC Hent ltac:(lia)
                ltac:(unfold inst; cbn [a_ss s_regs mk_ss]; rewrite length_map; exact Flen)) as (E1 & Hag1 & _ & HC1 & _).
    unfold D0 in Q. apply (Q (Z.to_nat Nv) 0 fy E1 R FULL model); [exact Hz | lia | lia | eapply env_agree_le; [exact Hag1 | lia] | exact HC1 | reflexivity].
  - (* [comment removed for export] *)
    destruct lc as [[h nx lo hi|j' js' sk' b' lo'|whs wcur lo hi wV wxs wxts|so shi]|]; [|discriminate| |discriminate|discriminate].
    { destruct (Z.eqb (pc cs) h && entails_h A lo hi cs nx)%bool eqn:Ht; [|discriminate]. injection Hc as <-. cbn [sd].
      apply andb_prop in Ht as [Hpc Hent]. apply Z.eqb_eq in Hpc.
      pose proof HL as HL0. destruct HL as [HB0 HL]. cbn [LCOK] in HL. destruct HL as [(Hn0 & Hlh & Hlen) HL]. cbn [lc_guard lc_bnd] in Hg. apply Nat.leb_le in Hg.
      destruct (entails_h_sound lo hi E cs nx R FULL model HC Hent Hn0 Hlen) as (E' & Hag & _ & HC' & Hpc').
      rewrite Hpc. exact (HL fy E' R FULL model Hz Hag HC' (WI_agree_lo _ _ _ _ _ _ _ _ HW HB0 Hag) eq_refl). }
    (* [comment removed for export] *)
    destruct whs as [|wT whs']; [discriminate|].
    destruct (Z.eqb (pc cs) (pc wT)) eqn:Hpc; [|discriminate].
    destruct (entails_s A lo (nxt wT) [] cs wT) as [sg|] eqn:Hent; [|discriminate].
    destruct (variant_ok (kn cs) sg wV wcur 0 && shape_vars_lt nx0 wxs)%bool eqn:Hv; [|discriminate].
    apply with_props_ok in Hc as [Hnp Hc]. injection Hc as <-.
    apply andb_prop in Hv as [Hdec Hsv]. apply Z.eqb_eq in Hpc.
    destruct HL as [HB0 HL]. cbn [LCOK] in HL. destruct HL as ((Hn0 & Hlh & HV) & HL2 & _).
    destruct (HL2 0%nat wT eq_refl) as (Hlog & Hlo & HL2').
    destruct (entails_s_sound lo (nxt wT) [] E cs wT sg R FULL model HC Hent Hn0 Hlog) as (Hag & HC' & Hpc' & _ & HH).
    rewrite (sd_agree D E (updl E sg) (m_fs model) wxs (env_agree_le _ _ _ _ Hag Hn0) Hsv). rewrite Hpc.
    apply (HL2' fy (updl E sg) R FULL model Hz Hag HC' (WI_agree_lo _ _ _ _ _ _ _ _ HW HB0 Hag) eq_refl (template_props_ok cs wT sg E R FULL model HC HP Hnp HH)).
    unfold variant_ok in Hdec. unfold uE. rewrite <- esubsts_denot.
    destruct (variant_dec (kn cs) sg wV) eqn:Hd1.
    + left. unfold variant_dec in Hd1. pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ (co_know _ _ _ _ _ HC) Hd1) as G.
      cbn [xt_den fst snd] in G. lia.
    + right. apply andb_prop in Hdec as [Hlt Hle]. apply Nat.ltb_lt in Hlt. unfold variant_le in Hle.
      pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ (co_know _ _ _ _ _ HC) Hle) as G. cbn [xt_den fst snd] in G. split; [lia | exact Hlt].
  - (* [comment removed for export] *)
    apply GW in Hc as [HN Hc].
    destruct (HS h) as [ch|] eqn:Hh; [|destruct (Nat.leb 1000 h); discriminate].
    destruct (entails cs ch) eqn:He; [|discriminate]. apply with_props_ok in Hc as [Hnp Hc]. injection Hc as <-. cbn [sd].
    destruct (entails_sound E cs ch R FULL model HC He) as [HC' Hpc].
    rewrite <- Hpc. apply (HS_sound fy Hz h ch Hh E R FULL model HC').
    (* [comment removed for export] *)
    rewrite (Mr_entails E cs ch model FULL He).
    exact (needs_props_sound cs (a_props ch) E _ Hnp (co_know _ _ _ _ _ HC) HP).
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_exit cs) as [code|] eqn:Hn; [|discriminate]. injection Hc as <-. cbn [sd].
    eapply (node_exit_sound fy); eassumption.
  - (* [comment removed for export] *)
    destruct (node_spin SEGS cs) eqn:Hn; [|discriminate]. injection Hc as <-. cbn [sd].
    exact (node_spin_sound cs E R FULL model HC Hn).
  - (* [comment removed for export] *)
    apply GW in Hc as [_ Hc].   (* [comment removed for export] *)
    destruct (node_fog cs fi fsz) as [cs1|] eqn:Hn; [|discriminate].
    destruct (fog_sound E cs R FULL model fi fsz cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME fk _ s Hc (cs_ok_set_props _ _ _ _ _ _ HC1) (props_ok_gpures _ _ _ _ cs cs1 HP (env_agree_refl _ _))).
  - (* [comment removed for export] *)
    apply GW in Hc as [_ Hc].   (* [comment removed for export] *)
    destruct (node_fognew cs gi gsz) as [cs1|] eqn:Hn; [|discriminate].
    destruct (fognew_sound E cs R FULL model gi gsz cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME gk _ s Hc (cs_ok_set_props _ _ _ _ _ _ HC1) (props_ok_gpures _ _ _ _ cs cs1 HP (env_agree_refl _ _))).
  - (* [comment removed for export] *)
    apply GW in Hc as [HN Hc].
    destruct (node_ghost LIMIT cs gb gn) as [cs1|] eqn:Hn; [|discriminate].
    destruct (ghost_sound E cs R FULL model gb gn cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME gk2 _ s Hc (cs_ok_set_props _ _ _ _ _ _ HC1) (props_ok_gpures _ _ _ _ cs cs1 HP (env_agree_refl _ _))).
  - (* [comment removed for export] *)
    apply GW in Hc as [HN Hc].
    destruct (node_unvis A cs ub un) as [cs1|] eqn:Hn; [|discriminate].
    destruct (unvis_sound E cs R FULL model ub un cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME uk _ s Hc (cs_ok_set_props _ _ _ _ _ _ HC1) (props_ok_gpures _ _ _ _ cs cs1 HP (env_agree_refl _ _))).
  - (* [comment removed for export] *)
    destruct (node_havocbrk nx0 cs hlo hhi) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havocbrk_sound E cs R FULL model hlo hhi cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONTE hk (gpures (xp_gh xp) cs cs1) s Hc E' R model Hag (cs_ok_set_props _ _ _ _ _ _ HC1) (props_ok_gpures _ _ _ _ cs cs1 HP (proj2 Hag)) eq_refl (mvis_refl _)).
  - (* [comment removed for export] *)
    destruct (node_intro nx0 cs ilo ihi) as [cs1|] eqn:Hn; [|discriminate].
    destruct (intro_sound E cs R FULL model ilo ihi cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    destruct (node_intro_neutral _ _ _ _ Hn) as [Hf1 Hv1].
    exact (CONTE ik (AP.gkeepE (xp_gh xp) [] cs cs1) s Hc E' R model Hag (cs_ok_set_props _ _ _ _ _ _ HC1)
             (props_ok_gkeepE E E' _ _ _ _ [] (nxt cs) (a_props cs) HP (proj2 Hag) (facts_of_ok SEGS E _ _ (co_know _ _ _ _ _ HC))
                (Mr_frameW _ E E' cs cs1 model model FULL FULL (hid_memneutral E E' cs cs1 model Hf1 Hv1 (proj2 Hag)) (fun a _ => eq_refl))) eq_refl (mvis_refl _)).
  - (* [comment removed for export] *)
    apply GW in Hc as [HN Hc].
    destruct (branch_probe IT cs) as [e|] eqn:Hbp; [|discriminate].
    destruct (erange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
    pose proof (LCOK_bnd E0 M0 m0 lc D E (m_fs model) HL) as Hgb.
    destruct (Z.ltb hi 1 || Z.ltb 0 lo)%bool eqn:Hdec.
    { (* [comment removed for export] *)
      destruct (run_block_gc_wb_ws SEGS IT _ (AP.WB xp) KC bfuel (djp :: STOPS A) cs) as [[cs1 W1]|] eqn:Hrb; [|discriminate].
      destruct (Z.eqb (pc cs1) djp); [|discriminate].
      eapply run_block_gc_wb_ws_sound; [exact Hz | exact Hgb | exact Hrb | exact HC | exact HW | exact (WB_run _ _ _ _ _ _ _ _ HL Hg) |].
      intros fy' E' R' FULL' model' Hz' Hag HC1 HW1 Hfs HW8 Hmr.
      exact (CONTW dk (gkeep (xp_gh xp) W1 cs cs1) s Hc fy' E' R' FULL' model' Hz' Hag (cs_ok_set_props _ _ _ _ _ _ HC1)
               (props_ok_gkeep _ _ _ _ _ cs cs1 W1 HP (proj2 Hag) (co_know _ _ _ _ _ HC1) HW8 Hmr) HW1 Hfs). }
    cbv zeta in Hc.
    destruct (run_block_gc_wb_ws SEGS IT _ (AP.WB xp) KC bfuel (djp :: STOPS A) (set_kn cs (KRange e lo 0 :: kn cs))) as [[ca Wa]|] eqn:Hra; [|discriminate].
    destruct (run_block_gc_wb_ws SEGS IT _ (AP.WB xp) KC bfuel (djp :: STOPS A) (set_kn cs (KRange e 1 hi :: kn cs))) as [[cb Wb]|] eqn:Hrb; [|discriminate].
    destruct (node_diamond_join A nx0 (nxt cs) djp drs ca cb) as [csj|] eqn:Hj; [|discriminate].
    destruct (split_sound cs e 0 lo hi E R FULL model HC Hr) as [HCl HCr].
    destruct (diamond_join_sound2 (nxt cs) djp drs ca cb csj Hj) as (Ja & Jb & Jvis & Jgh & Jka & Jkb).
    destruct (run_block_gc_wb_ws_vis _ _ _ _ _ _ _ Hra) as (Va & Ga & Fa).
    destruct (run_block_gc_wb_ws_vis _ _ _ _ _ _ _ Hrb) as (Vb & Gb & Fb).
    destruct (fresh_ok_parts _ (fresh_ok_mono _ _ Hgb Fa)) as (_ & _ & _ & Fallow & _ & _ & Fle).
    change (pairs_vars_lt (nxt cs) (a_vis cs ++ a_ghost cs) = true) in Fallow. change (nx0 <= nxt cs)%nat in Fle.
    change (a_vis ca = a_vis cs) in Va. change (a_ghost ca = a_ghost cs) in Ga.
    change (a_vis cb = a_vis cs) in Vb. change (a_ghost cb = a_ghost cs) in Gb.
    (* [comment removed for export] *)
    assert (KEEP : forall (ca0 : acs) (Wa0 : list (saddr * nat)) E' E'' R' FULL' model',
              incl Wa0 (Wa ++ Wb) -> incl (kn csj) (kn ca0) ->
              a_vis ca0 = a_vis cs -> a_ghost ca0 = a_ghost cs -> a_vis csj = a_vis ca0 ->
              env_agree (nxt cs) E E' -> env_agree (nxt cs) E' E'' -> cs_ok E' ca0 R' FULL' model' ->
              Forall (fun w => (snd w <= 8)%nat) Wa0 ->
              (forall a, wout E' Wa0 a -> Mr E' ca0 model' FULL' a = Mr E cs model FULL a) ->
              props_ok E'' (Mr E'' csj model' FULL') (a_props (gkeep (xp_gh xp) (Wa ++ Wb) cs csj))).
    { intros ca0 Wa0 E' E'' R' FULL' model' Hincl Hkn Hva Hga Hvj Hag1 Hag2 HCa HW8 Hmr.
      unfold gkeep, set_props. cbn [a_props].
      assert (Hhid : hid E'' csj model' = hid E' ca0 model').
      { eapply (hid_extF (nxt cs)); [exact Hvj | exact Hag2 | exact Fle | rewrite Hva, Hga; exact Fallow | apply mvis_refl]. }
      assert (HMr : Mr E'' csj model' FULL' = Mr E' ca0 model' FULL') by (unfold Mr; rewrite Hhid; reflexivity).
      rewrite HMr. apply (props_ok_gkeep1_agree E' E''); [exact Hag2|].
      eapply (props_ok_gkeep_sub E E' _ _ (Mr E' ca0 model' FULL') (kn csj) (Wa ++ Wb) Wa0 (s_next (a_ss cs)) (a_props cs) HP Hag1);
        [ eapply incl_Forall; [exact Hkn | exact (co_know _ _ _ _ _ HCa)] | exact Hincl | exact HW8 | exact Hmr]. }
    assert (MRK : forall K E' ca0 model' FULL' (P : word -> Prop),
              (forall a, P a -> Mr E' ca0 model' FULL' a = Mr E (set_kn cs K) model FULL a) ->
              forall a, P a -> Mr E' ca0 model' FULL' a = Mr E cs model FULL a).
    { intros K E' ca0 model' FULL' P H a Ha. rewrite (H a Ha). unfold Mr. rewrite (hid_ext E cs (set_kn cs K) model eq_refl). reflexivity. }
    destruct (Z.leb_spec (bv_unsigned (edenot E e)) 0) as [Hle|Hgt].
    + rewrite <- (pc_set_kn cs (KRange e lo 0 :: kn cs)).
      eapply run_block_gc_wb_ws_sound; [exact Hz | exact Hgb | exact Hra | exact (HCl Hle) | exact HW | exact (WB_run _ _ _ _ _ _ _ _ HL Hg) |].
      intros fy' E' R' FULL' model' Hz' [Hag0 Hag1] HC1 HW1 Hfs HW8 Hmr.
      destruct (Ja E' R' FULL' model' HC1) as (E'' & (Hag2a & Hag2b & Hag2c) & HC2 & Hpc2). rewrite <- Hpc2.
      change (env_agree (nxt cs) E E') in Hag1.
      exact (CONT HN dk (gkeep (xp_gh xp) (Wa ++ Wb) cs csj) s Hc fy' E'' R' FULL' model' Hz'
               (conj (env_agree_trans _ _ _ _ Hag0 Hag2a) (env_agree_trans _ _ _ _ Hag1 Hag2b)) (cs_ok_set_props _ _ _ _ _ _ HC2)
               (KEEP ca Wa E' E'' R' FULL' model' (incl_appl Wb (incl_refl Wa)) Jka Va Ga Jvis Hag1 Hag2b HC1 HW8 (MRK _ _ _ _ _ _ Hmr)) Hfs).
    + rewrite <- (pc_set_kn cs (KRange e 1 hi :: kn cs)).
      eapply run_block_gc_wb_ws_sound; [exact Hz | exact Hgb | exact Hrb | exact (HCr ltac:(lia)) | exact HW | exact (WB_run _ _ _ _ _ _ _ _ HL Hg) |].
      intros fy' E' R' FULL' model' Hz' [Hag0 Hag1] HC1 HW1 Hfs HW8 Hmr.
      destruct (Jb E' R' FULL' model' HC1) as (E'' & (Hag2a & Hag2b & Hag2c) & HC2 & Hpc2). rewrite <- Hpc2.
      change (env_agree (nxt cs) E E') in Hag1.
      exact (CONT HN dk (gkeep (xp_gh xp) (Wa ++ Wb) cs csj) s Hc fy' E'' R' FULL' model' Hz'
               (conj (env_agree_trans _ _ _ _ Hag0 Hag2a) (env_agree_trans _ _ _ _ Hag1 Hag2b)) (cs_ok_set_props _ _ _ _ _ _ HC2)
               (KEEP cb Wb E' E'' R' FULL' model' (incl_appr Wa (incl_refl Wb)) Jkb Vb Gb (eq_trans Jvis (eq_trans Va (eq_sym Vb))) Hag1 Hag2b HC1 HW8 (MRK _ _ _ _ _ _ Hmr)) Hfs).

  - (* [comment removed for export] *)
    apply GW in Hc as [_ Hc].   (* [comment removed for export] *)
    destruct (node_rename _ cs rnm) as [cs1|] eqn:Hn; [|discriminate].
    pose proof (LCOK_bnd E0 M0 m0 lc D E (m_fs model) HL) as Hgb.
    destruct (rename_sound _ E cs R FULL model rnm cs1 Hgb HC Hn) as (E' & Hag & HC1 & Hpc & HPr). rewrite <- Hpc.
    rewrite (sd_agree D E E' (m_fs model) s (env_agree_le _ _ _ _ Hag Hgb) (check_vars _ _ _ _ _ _ Hc)).
    eapply IH; [exact Hc | exact Hz | exact HC1 | exact (HPr HP) | exact (WI_agree_gb _ _ _ _ _ _ _ _ _ _ _ HW HL Hag) | eapply LCOK_agree_gb; [exact HL | exact Hag] | exact HD].
  - (* [comment removed for export] *)
    apply GW in Hc as [_ Hc].   (* [comment removed for export] *)
    destruct (node_compact _ cs) as [cs1|] eqn:Hn; [|discriminate].
    pose proof (LCOK_bnd E0 M0 m0 lc D E (m_fs model) HL) as Hgb.
    destruct (compact_sound _ E cs R FULL model cs1 Hgb HC Hn) as (E' & Hag & HC1 & Hpc & HPr). rewrite <- Hpc.
    rewrite (sd_agree D E E' (m_fs model) s (env_agree_le _ _ _ _ Hag Hgb) (check_vars _ _ _ _ _ _ Hc)).
    eapply IH; [exact Hc | exact Hz | exact HC1 | exact (HPr HP) | exact (WI_agree_gb _ _ _ _ _ _ _ _ _ _ _ HW HL Hag) | eapply LCOK_agree_gb; [exact HL | exact Hag] | exact HD].
  - (* [comment removed for export] *)
    apply GW in Hc as [HN Hc].
    destruct (via_ok nx0 cs vjs vlo && forallb (gvars_lt (nxt cs)) (a_props vjs))%bool eqn:Hv; [|discriminate].
    apply andb_prop in Hv as [Hv Hgv].
    destruct (CHECK bfuel fuel lc vjs vk) as [sk| |] eqn:Hk; [|discriminate|discriminate].
    unfold via_ok in Hv. repeat match type of Hv with (_ && _)%bool = true => apply andb_prop in Hv as [Hv ?X] end.
    match goal with Hl : match s_log (a_ss vjs) with _ => _ end = true |- _ => clear Hl end.
    match goal with Hl : Nat.eqb (length _) 32 = true |- _ => apply Nat.eqb_eq in Hl; rename Hl into Hlen end.
    repeat match goal with Hl : Nat.leb _ _ = true |- _ => apply Nat.leb_le in Hl end.
    pose proof (LCOK_bnd E0 M0 m0 lc D E (m_fs model) HL) as Hgb.
    assert (Hgb' : (match lc with Some c => lc_bnd c | None => nx0 end <= nxt cs)%nat).
    { destruct lc as [c|]; [apply Nat.leb_le; exact Hg | lia]. }
    apply (IH bfuel (Some (JC vj vjs sk (nxt cs) vlo)) vka cs s Hc fy E R FULL model D E0 M0 m0 Hz HC HP (WI_none _ _ _ _ _ _ HN)); [|exact HD].
    split; [unfold WBOK; rewrite HN; exact I|]. cbn [LCOK]. split; [split; [lia | split; [lia | split; [exact Hlen | exact Hgv]]]|].
    intros fy2 E' R' F' m' Hz2 Hag HC' _ Hfs HPj. rewrite <- Hfs.
    apply (IH bfuel lc vk vjs sk Hk fy2 E' R' F' m' D E0 M0 m0 Hz2 HC' HPj (WI_none _ _ _ _ _ _ HN)); [|exact HD].
    rewrite Hfs. eapply LCOK_agree_gb; [exact HL|]. eapply env_agree_le; [exact Hag | exact Hgb'].
  - (* [comment removed for export] *)
    destruct lc as [[h nx lo hi|j' js' sk' b' lo'|whs' wcur' wlo' whi' wV' wxs' wxts'|so shi]|]; [discriminate| |discriminate|discriminate|discriminate].
    destruct HL as [HB0 HL]. cbn [LCOK] in HL. destruct HL as [(Hn0 & Hbl & Hlen & Hgv) HJ].
    destruct (Nat.eqb mj j' && Z.eqb (pc cs) (pc js') && shape_vars_lt nx0 sk' && entails_h A lo' (nxt js') cs js')%bool eqn:Ht.
    2:{ (* [comment removed for export] *)
      destruct (Nat.eqb mj j' && Z.eqb (pc cs) (pc js') && shape_vars_lt nx0 sk' && match s_log (a_ss js') with [] => true | _ => false end)%bool eqn:Ht2; [|discriminate].
      destruct (entails_s A lo' (nxt js') [] cs js') as [sg|] eqn:Hent; [|discriminate].
      apply with_props_ok in Hc as [Hnp Hc]. injection Hc as <-.
      apply andb_prop in Ht2 as [Ht2 Hlog]. apply andb_prop in Ht2 as [Ht2 Hsv]. apply andb_prop in Ht2 as [_ Hpc]. apply Z.eqb_eq in Hpc.
      assert (Hlog' : s_log (a_ss js') = []) by (destruct (s_log (a_ss js')); [reflexivity | discriminate Hlog]).
      assert (Hn0l : (nx0 <= lo')%nat) by (clear -Hn0 Hbl; lia).
      destruct (entails_s_sound lo' (nxt js') [] E cs js' sg R FULL model HC Hent Hn0l Hlog') as (Hag & HC' & Hpc' & _ & HH).
      rewrite (sd_agree D E (updl E sg) (m_fs model) sk' (env_agree_le nx0 lo' E (updl E sg) Hag Hn0l) Hsv). rewrite Hpc.
      exact (HJ fy (updl E sg) R FULL model Hz (env_agree_le _ _ _ _ Hag Hbl) HC' (WI_agree_lo _ _ _ _ _ _ _ _ HW HB0 (env_agree_le _ _ _ _ Hag Hbl)) eq_refl
                (template_props_ok cs js' sg E R FULL model HC HP Hnp HH)). }
    apply with_props_ok in Hc as [Hnp Hc]. injection Hc as <-.
    apply andb_prop in Ht as [Ht Hent]. apply andb_prop in Ht as [Ht Hsv]. apply andb_prop in Ht as [_ Hpc]. apply Z.eqb_eq in Hpc.
    destruct (entails_h_sound lo' (nxt js') E cs js' R FULL model HC Hent ltac:(clear -Hn0 Hbl; lia) Hlen) as (E' & Hag & _ & HC' & Hpc').
    assert (Hn0l : (nx0 <= lo')%nat) by lia.
    rewrite (sd_agree D E E' (m_fs model) sk' (env_agree_le nx0 lo' E E' Hag Hn0l) Hsv). rewrite Hpc.
    (* [comment removed for export] *)
    assert (HPj : props_ok E' (Mr E' js' model FULL) (a_props js')).
    { rewrite (Mr_entails_h lo' (nxt js') E E' cs js' model FULL Hent Hn0l Hag).
      apply (props_ok_agree b' E E'); [| exact Hgv | exact (env_agree_le _ _ _ _ Hag Hbl)].
      exact (needs_props_sound cs (a_props js') E _ Hnp (co_know _ _ _ _ _ HC) HP). }
    exact (HJ fy E' R FULL model Hz (env_agree_le _ _ _ _ Hag Hbl) HC' (WI_agree_lo _ _ _ _ _ _ _ _ HW HB0 (env_agree_le _ _ _ _ Hag Hbl)) eq_refl HPj).
  - (* [comment removed for export] *)
    destruct (node_abstractcell A cs ab an) as [cs1|] eqn:Hn; [|discriminate].
    destruct (abstractcell_sound E cs R FULL model ab an cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME ak _ s Hc (cs_ok_set_props _ _ _ _ _ _ HC1) (props_ok_gpures _ _ _ _ cs cs1 HP (env_agree_refl _ _))).
  - (* [comment removed for export] *)
    destruct (node_havocwords nx0 cs hws) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havocwords_sound E cs R FULL model hws cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONTE hwk (gpures (xp_gh xp) cs cs1) s Hc E' R model Hag (cs_ok_set_props _ _ _ _ _ _ HC1) (props_ok_gpures _ _ _ _ cs cs1 HP (proj2 Hag)) eq_refl (mvis_refl _)).
  - (* [comment removed for export] *)
    destruct (node_respell cs rsr rse) as [cs1|] eqn:Hn; [|discriminate].
    destruct (respell_sound E cs R FULL model rsr rse cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    assert (Hv1 : a_vis cs1 = a_vis cs) by (unfold node_respell in Hn; destruct (_ && _ && _ && _)%bool; [injection Hn as <-; reflexivity | discriminate Hn]).
    exact (SAME rsk _ s Hc (cs_ok_set_props _ _ _ _ _ _ HC1)
             (props_ok_gkeepE E E _ _ _ _ [] (nxt cs) (a_props cs) HP (env_agree_refl _ _) (facts_of_ok SEGS E _ _ (co_know _ _ _ _ _ HC))
                (Mr_frameW _ E E cs cs1 model model FULL FULL (hid_ext E cs cs1 model Hv1) (fun a _ => eq_refl)))).
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    revert Hc. generalize (AP.normT xp cs wexits) as wexits'. generalize (AP.normT xp cs wheads) as wheads'.
    intros wheads' wexits' Hc. rename wheads into wheads00. rename wexits into wexits00. rename wheads' into wheads. rename wexits' into wexits.
    destruct wheads as [|[T0 b0] hrest]; [discriminate|].
    destruct (while_okN nx0 cs wlo (map fst ((T0, b0) :: hrest)) wV wxs && Z.eqb (pc cs) (pc T0))%bool eqn:Hw; [|discriminate].
    apply andb_prop in Hw as [Hw Hpc0]. apply Z.eqb_eq in Hpc0.
    destruct (entails_s A wlo (nxt T0) [] cs T0) as [sg0|] eqn:Hent; [|discriminate].
    destruct (needs_props xp cs (map (ginst sg0) (a_props T0))) eqn:Hnp0; [|discriminate].
    destruct (chk_exits nx0 (CHECK bfuel fuel lc) wlo wxs wexits) as [xts|e] eqn:Hxts; [|exfalso; exact (chk_exits_err _ _ _ _ _ Hxts _ Hc)].
    set (heads := (T0, b0) :: hrest) in *. set (hs := map fst heads) in *.
    destruct (chk_heads (CHECK bfuel fuel) hs 0 wlo wV wxs xts heads) as [s'| |] eqn:Hh; [|discriminate|discriminate].
    injection Hc as <-. destruct (chk_heads_ok _ _ _ _ _ _ _ _ _ Hh) as [-> Hbodies].
    destruct (while_okN_facts cs wlo hs wV wxs Hw) as (Wn0 & Wnxt & Wheads & Wxs & Wsv).
    pose proof (LCOK_bnd E0 M0 m0 lc D E (m_fs model) HL) as Hgb.
    assert (Hgb' : (match lc with Some c => lc_bnd c | None => nx0 end <= wlo)%nat).
    { destruct lc as [c|]; [apply Nat.leb_le in Hg; lia | exact Wn0]. }
    set (K := length heads).
    assert (HSd : forall h T, nth_error hs h = Some T -> exists b, nth_error heads h = Some (T, b) /\ head_ok nx0 wlo wV T = true /\ (h < K)%nat).
    { intros h T HT. unfold hs in HT. rewrite nth_error_map in HT.
      destruct (nth_error heads h) as [[T' b]|] eqn:Hn; [|discriminate]. cbn [option_map fst] in HT. injection HT as ->.
      exists b. split; [reflexivity|]. split.
      - apply Wheads. unfold hs. apply in_map_iff. exists (T, b). split; [reflexivity | eapply nth_error_In; exact Hn].
      - unfold K. apply (proj1 (nth_error_Some heads h)). rewrite Hn. discriminate. }
    assert (HT0 : nth_error hs 0 = Some T0) by reflexivity.
    destruct (HSd 0%nat T0 HT0) as (bb0 & _ & Hok0 & HK0). destruct (head_ok_facts wlo wV T0 Hok0) as (_ & Wlog0 & _ & _ & _).
    destruct (entails_s_sound wlo (nxt T0) [] E cs T0 sg0 R FULL model HC Hent Wn0 Wlog0) as (Hag0 & HC0 & Hpc & _ & HH0).
    assert (Q : forall n h T (fy1 : FPState) E1 R1 F1 m1, frm_zero (@fp_csr fy1) -> nth_error hs h = Some T -> cs_ok E1 T R1 F1 m1 -> env_agree wlo E E1 ->
                 WI E0 M0 m0 E1 F1 m1 ->
                 m_fs m1 = m_fs model -> props_ok E1 (Mr E1 T m1 F1) (a_props T) -> (Z.to_nat (uE E1 wV) * K + (K - 1 - h) <= n)%nat ->
                 srealizes SEGS (cfgF fy1 R1 (pc T) F1 m1) (sd D E (m_fs model) wxs)).
    { induction n as [|n IHn]; intros h T fy1 E1 R1 F1 m1 Hz1 HT HC1 Hag1 HW1 Hfs1 HP1 Hn.
      all: destruct (HSd h T HT) as (b & Hinb & Hok & HhK); destruct (head_ok_facts wlo wV T Hok) as (Tfr & Tlog & Tlen & Tlo & TV).
      all: pose proof (Hbodies h T b Hinb) as Hbody; cbn [Nat.add] in Hbody.
      all: assert (AG0 : env_agree nx0 E E1) by (eapply env_agree_le; [exact Hag1 | exact Wn0]).
      all: rewrite <- (sd_loop_shape D E E1 (m_fs model) wxs Wxs Wsv AG0), <- Hfs1.
      all: apply (IH bfuel (Some (WC hs h wlo (nxt T) wV wxs xts)) b T wxs Hbody fy1 E1 R1 F1 m1 _ E0 M0 m0 Hz1 HC1 HP1 HW1);
        [| rewrite Hfs1; apply sd_has_nil; exact HD].
      all: split; [eapply WBOK_nest; [exact HL | cbn [lc_lo]; exact Hgb']|].
      all: cbn [LCOK]; split; [split; [exact Wn0 | split; [exact Tlo | exact TV]]|].
      all: split.
      (* [comment removed for export] *)
      1: { intros h' T' HT'. destruct (HSd h' T' HT') as (b' & _ & Hok' & HhK'). destruct (head_ok_facts wlo wV T' Hok') as (_ & Tlog' & _ & Tlo' & _).
           split; [exact Tlog'|]. split; [exact Tlo'|].
           intros fy2 E2 R2 F2 m2 Hz2 Hag2 HC2 HW2 Hfs2 HP2 HV2. exfalso. unfold uE in *. pose proof (u64_range (edenot E2 wV)). nia. }
      2: { intros h' T' HT'. destruct (HSd h' T' HT') as (b' & _ & Hok' & HhK'). destruct (head_ok_facts wlo wV T' Hok') as (_ & Tlog' & _ & Tlo' & _).
           split; [exact Tlog'|]. split; [exact Tlo'|].
           intros fy2 E2 R2 F2 m2 Hz2 Hag2 HC2 HW2 Hfs2 HP2 HV2.
           assert (AG2 : env_agree nx0 E E2) by (eapply env_agree_le; [eapply env_agree_trans; [exact Hag1 | exact Hag2] | exact Wn0]).
           rewrite Hfs1, (sd_loop_shape D E E2 (m_fs model) wxs Wxs Wsv AG2).
           apply (IHn h' T' fy2 E2 R2 F2 m2 Hz2 HT' HC2 (env_agree_trans _ _ _ _ Hag1 Hag2) HW2); [rewrite Hfs2, Hfs1; reflexivity | exact HP2 |].
           unfold uE in *. pose proof (u64_range (edenot E2 wV)). pose proof (u64_range (edenot E1 wV)).
           destruct HV2 as [HV2|[HV2 Hhh]].
           - assert (X : (Z.to_nat (bv_unsigned (edenot E2 wV)) + 1 <= Z.to_nat (bv_unsigned (edenot E1 wV)))%nat) by lia. nia.
           - assert (X : (Z.to_nat (bv_unsigned (edenot E2 wV)) <= Z.to_nat (bv_unsigned (edenot E1 wV)))%nat) by lia. nia. }
      (* [comment removed for export] *)
      all: intros i x sx Hi; destruct (chk_exits_ok (CHECK bfuel fuel lc) wlo wxs wexits xts Hxts i x sx Hi) as (kx & Htx & Hkx & Hnn);
           destruct (template_ok_facts wlo x Htx) as (Xfr & Xlog & Xlen & Xlo);
           split; [exact Xlo|]; split; [exact Xlog|];
           intros fy2 E2 R2 F2 m2 Hz2 Hag2 HC2 HW2 Hfs2 HP2;
           assert (AGl : env_agree wlo E E2) by (eapply env_agree_trans; [exact Hag1 | exact Hag2]);
           assert (HL2 : LCOK E0 M0 m0 lc D E2 (m_fs m2))
             by (rewrite Hfs2, Hfs1; eapply LCOK_agree_gb; [exact HL | eapply env_agree_le; [exact AGl | lia]]);
           pose proof (IH bfuel lc kx x sx Hkx fy2 E2 R2 F2 m2 D E0 M0 m0 Hz2 HC2 HP2 HW2 HL2 HD) as B; rewrite Hfs2 in B;
           (destruct Hnn as [Hnn|Hnn]; [rewrite (sd_nonext _ D E2 _ sx Hnn); exact B
                                      | apply is_snext_eq in Hnn; subst wxs; exact B]). }
    rewrite Hpc0.
    exact (Q _ 0%nat T0 fy (updl E sg0) R FULL model Hz HT0 HC0 Hag0
             (WI_agree_gb _ _ _ _ _ _ _ _ _ _ _ HW HL (env_agree_le _ _ _ _ Hag0 Hgb')) eq_refl (template_props_ok cs T0 sg0 E R FULL model HC HP Hnp0 HH0) (le_n _)).
  - (* [comment removed for export] *)
    destruct lc as [[h nx lo hi|j' js' sk' b' lo'|whs wcur lo hi wV wxs wxts|so shi]|]; [discriminate|discriminate| |discriminate|discriminate].
    destruct (nth_error whs nh) as [wT|] eqn:HT; [|discriminate].
    destruct (Z.eqb (pc cs) (pc wT)) eqn:Hpc; [|discriminate].
    destruct (entails_s A lo (nxt wT) nwh cs wT) as [sg|] eqn:Hent; [|discriminate].
    destruct (variant_ok (kn cs) sg wV wcur nh && shape_vars_lt nx0 wxs)%bool eqn:Hv; [|discriminate].
    apply with_props_ok in Hc as [Hnp Hc]. injection Hc as <-.
    apply andb_prop in Hv as [Hdec Hsv]. apply Z.eqb_eq in Hpc.
    destruct HL as [HB0 HL]. cbn [LCOK] in HL. destruct HL as ((Hn0 & Hlh & HV) & HL2 & _).
    destruct (HL2 nh wT HT) as (Hlog & Hlo & HL2').
    destruct (entails_s_sound lo (nxt wT) nwh E cs wT sg R FULL model HC Hent Hn0 Hlog) as (Hag & HC' & Hpc' & _ & HH).
    rewrite (sd_agree D E (updl E sg) (m_fs model) wxs (env_agree_le _ _ _ _ Hag Hn0) Hsv). rewrite Hpc.
    apply (HL2' fy (updl E sg) R FULL model Hz Hag HC' (WI_agree_lo _ _ _ _ _ _ _ _ HW HB0 Hag) eq_refl (template_props_ok cs wT sg E R FULL model HC HP Hnp HH)).
    unfold variant_ok in Hdec. unfold uE. rewrite <- esubsts_denot.
    destruct (variant_dec (kn cs) sg wV) eqn:Hd1.
    + left. unfold variant_dec in Hd1. pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ (co_know _ _ _ _ _ HC) Hd1) as G.
      cbn [xt_den fst snd] in G. lia.
    + right. apply andb_prop in Hdec as [Hlt Hle]. apply Nat.ltb_lt in Hlt. unfold variant_le in Hle.
      pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ (co_know _ _ _ _ _ HC) Hle) as G. cbn [xt_den fst snd] in G. split; [lia | exact Hlt].
  - (* [comment removed for export] *)
    destruct lc as [[h nx lo hi|j' js' sk' b' lo'|whs wcur lo hi wV wxs wxts|so shi]|]; [discriminate|discriminate| | |discriminate].
    + destruct (nth_error wxts bi) as [[x sx]|] eqn:Hi; [|discriminate].
      destruct (entails_s A lo (nxt x) bh cs x) as [sg|] eqn:Hent; [|discriminate].
      destruct (shape_vars_lt nx0 sx) eqn:Hsv; [|discriminate]. apply with_props_ok in Hc as [Hnp Hc]. injection Hc as <-.
      destruct HL as [HB0 HL]. cbn [LCOK] in HL. destruct HL as ((Hn0 & Hlh & HV) & _ & HL3).
      destruct (HL3 bi x sx Hi) as (Hlox & Hlogx & HL3i).
      destruct (entails_s_sound lo (nxt x) bh E cs x sg R FULL model HC Hent Hn0 Hlogx) as (Hag & HC' & Hpc' & _ & HH).
      rewrite (sd_agree D E (updl E sg) (m_fs model) sx (env_agree_le _ _ _ _ Hag Hn0) Hsv). rewrite <- Hpc'.
      exact (HL3i fy (updl E sg) R FULL model Hz Hag HC' (WI_agree_lo _ _ _ _ _ _ _ _ HW HB0 Hag) eq_refl (template_props_ok cs x sg E R FULL model HC HP Hnp HH)).
    + (* [comment removed for export] *)
      destruct (nth_error so bi) as [x|] eqn:Hi; [|discriminate].
      destruct (entails_s A shi (nxt x) bh cs x) as [sg|] eqn:Hent; [|discriminate]. injection Hc as <-. cbn [sd].
      destruct HL as [HB0 HL]. cbn [LCOK] in HL. destruct HL as [Hn0 HL3].
      destruct (HL3 bi x Hi) as (Hlox & Hlogx & Hlenx & HL3i).
      destruct (entails_s_sound shi (nxt x) bh E cs x sg R FULL model HC Hent Hn0 Hlogx) as (Hag & HC' & Hpc' & _).
      rewrite (HOLES_agree 0%nat E (updl E sg) (m_fs model) (env_agree_le _ _ _ _ Hag Hn0)). rewrite <- Hpc'.
      exact (HL3i fy (updl E sg) R FULL model Hz Hag HC' (WI_agree_lo _ _ _ _ _ _ _ _ HW HB0 Hag) eq_refl).
  - (* [comment removed for export] *)
    destruct (xp_sg xp usid) as [SD0|] eqn:Hsd; [|discriminate].
    destruct (AP.segdef_wf nx0 SD0) eqn:Hwf0; [|discriminate]. cbn [negb] in Hc.
    (* [comment removed for export] *)
    destruct (AP.use_view cs SD0) as [[SD skh]|] eqn:Huv; [|discriminate].
    match type of Hc with (if ?b then _ else _) = _ => destruct b; [discriminate|] end.
    destruct (SEGS_sound usid SD0 cs SD skh Hsd Huv) as [SEM_SD Hwf_SD]. pose proof (Hwf_SD Hwf0) as Hwf. clear Hwf_SD.
    set (n := Nat.max (sg_lo SD) (nxt cs)) in Hc. set (d := (n - sg_lo SD)%nat) in Hc.
    revert Hc. generalize (map (fun ve => ((fst ve + d)%nat, snd ve)) skh ++ uhints) as uhints'.
    intros uhints' Hc. rename uhints into uhints00. rename uhints' into uhints.
    set (rho := AP.shiftb (sg_lo SD) (AP.sg_top SD) d) in Hc.
    destruct (entails_s A n (n + (sg_hi SD - sg_lo SD))%nat uhints cs (insts rho (sg_in SD))) as [sg|] eqn:Hent; [|discriminate].
    destruct (fresh_ok nx0 cs && forallb (fun b => AP.expr_vars_lt n (snd b)) sg)%bool eqn:Hchk; [|discriminate]. cbn [negb] in Hc.
    apply andb_prop in Hchk as [Hfresh Hsgv].
    set (Wc := map (AP.wnorm (facts_of (kn cs))) (AP.wsubsts sg (AP.wsubsts rho (sg_w SD)))) in Hc.
    destruct (AP.okW xp (Some Wc) cs) eqn:Hok; [|discriminate]. cbn [negb] in Hc.    (* [comment removed for export] *)
    rewrite AP.frameQ_eq in Hc.   (* [comment removed for export] *)
    set (FR := flat_map (fun K => if AP.kpure K then [K] else
                                 match AP.kfoot K with Some _ => AP.wcut (facts_of (kn cs)) Wc K | None => [] end) (kn cs)) in Hc.
    set (KP := List.filter (AP.gkeep1E (xp_gh xp) (facts_of (kn cs)) Wc (nxt cs)) (a_props cs)) in Hc.   (* [comment removed for export] *)
    destruct (AP.use_all (CHECK bfuel fuel lc) (AP.use_exit sg rho d FR KP) _ cs (sg_outs SD) uks) as [ss|r] eqn:Hua.
    2: { exfalso. exact (use_all_err _ _ _ _ _ _ _ _ Hua Hc). }
    destruct (forallb (shape_eqb (nth 0 ss SNil)) ss) eqn:Hsame; [|discriminate]. injection Hc as <-.
    assert (SS0 : forall i s0, nth_error ss i = Some s0 -> s0 = nth 0%nat ss SNil).
    { intros i s0 Hi. symmetry. apply shape_eqb_eq. exact (proj1 (forallb_forall _ _) Hsame s0 (nth_error_In _ _ Hi)). }
    clear CONTW CONT CONTF CONTE SAME GWS GW CONTS.
    destruct (segdef_wf_facts SD Hwf) as (Wlo & Wlohi & Wnxt & Wtin & Wouts & WWv & Wsh & Wnn & Wprops).
    destruct (template_ok_facts (sg_lo SD) (sg_in SD) Wtin) as (Ifr & Ilog & Ilen & Ilo).
    destruct (use_all_ok _ _ _ _ _ _ _ Hua) as [Hsslen Hall].
    pose proof (sg_top_ge SD) as [Tophi Topx].
    assert (Hnlo : (sg_lo SD <= n)%nat) by (unfold n; lia).
    assert (Hncs : (nxt cs <= n)%nat) by (unfold n; lia).
    assert (Hdn : (n = sg_lo SD + d)%nat) by (unfold d; lia).
    assert (Hrho : sg_dom_ge nx0 rho = true) by (unfold rho; apply shiftb_dom_ge; lia).
    assert (Ilog2 : s_log (a_ss (insts rho (sg_in SD))) = []) by reflexivity.
    destruct (entails_s_sound n _ uhints E cs (insts rho (sg_in SD)) sg R FULL model HC Hent ltac:(lia) Ilog2) as (HagS & HCS & HpcS & HlenS & HHS).
    set (Es := updl (updl E sg) rho).
    assert (HCin : cs_ok Es (sg_in SD) R FULL model) by (apply (proj1 (cs_ok_insts (updl E sg) rho (sg_in SD) R FULL model Hrho Ilog)); exact HCS).
    assert (AGs : env_agree nx0 E Es).
    { eapply env_agree_trans; [eapply env_agree_le; [exact HagS | lia] | apply updl_agree; exact Hrho]. }
    set (K := fun (i : nat) (E1 : env) (fs1 : Fs.Fs) => sd D E1 fs1 (nth i ss SNil)).
    assert (Kvars : forall i, shape_vars_lt nx0 (nth i ss SNil) = true).
    { intros i. destruct (nth_error ss i) as [s0|] eqn:Hn.
      - rewrite (nth_error_nth ss i SNil Hn). destruct (nth_error (sg_outs SD) i) as [x|] eqn:Hx.
        + destruct (Hall i x Hx) as (k & s1 & _ & Hs1 & Hck). rewrite Hn in Hs1. injection Hs1 as ->. exact (check_vars _ _ _ _ _ _ Hck).
        + exfalso. apply nth_error_None in Hx. assert (X : nth_error ss i <> None) by (rewrite Hn; discriminate). apply nth_error_Some in X. lia.
      - rewrite nth_overflow; [reflexivity|]. apply nth_error_None. exact Hn. }
    assert (Kag : forall i E1 E2 fs1, env_agree nx0 E1 E2 -> K i E1 fs1 = K i E2 fs1).
    { intros i E1 E2 fs1 Hag12. unfold K. apply sd_agree; [exact Hag12 | exact (Kvars i)]. }
    assert (Knil : forall i E1 fs1, K i E1 fs1 []) by (intros; unfold K; apply sd_has_nil; exact HD).
    pose proof (SEM_SD K Kag Knil fy Es R FULL model Hz HCin) as SEM.
    assert (SPL : forall sh, shape_vars_lt nx0 sh = true -> no_next sh = true -> sd D E (m_fs model) (AP.xsplice sh ss) = sdK K t_nil Es (m_fs model) sh).
    { induction sh; cbn [AP.xsplice sd sdK shape_vars_lt no_next is_snext]; intros Hv Hnn; try reflexivity; try discriminate Hnn.
      - rewrite (IHsh Hv Hnn). unfold Wp. replace (flat_map (piece_den Es) ps) with (flat_map (piece_den E) ps); [reflexivity|].
        apply flat_map_ext. intros [bs|kk]; cbn [piece_den]; [reflexivity|]. destruct AGs as [_ Heb]. rewrite Heb. reflexivity.
      - apply andb_prop in Hv as [Hv1 Hv2]. apply andb_prop in Hnn as [Hn1 Hn2]. rewrite (IHsh1 Hv1 Hn1), (IHsh2 Hv2 Hn2). reflexivity.
      - apply andb_prop in Hv as [Hv Hv3]. apply andb_prop in Hv as [Hv1 Hv2]. apply andb_prop in Hnn as [Hn1 Hn2].
        rewrite (IHsh1 Hv2 Hn1), (IHsh2 Hv3 Hn2). rewrite (edenot_agree' nx0 E Es e AGs Hv1). reflexivity.
      - unfold K. apply sd_agree; [exact AGs | exact (Kvars h)]. }
    rewrite (SPL (sg_shape SD) Wsh Wnn). rewrite <- HpcS. replace (pc (insts rho (sg_in SD))) with (pc (sg_in SD)) by reflexivity.
    apply SEM. clear SEM SPL.
    intros i x fy2 E2 R2 F2 m2 Hi Hz2 Hag2 HC2 Hfs2 Hfr2 Hmv2.
    destruct (Hall i x Hi) as (ki & si & Hki & Hsi & Hck).
    destruct (Wouts i x Hi) as [Wtx Wfx]. destruct (template_ok_facts (sg_hi SD) x Wtx) as (Xfr & Xlog & Xlen & Xlo).
    pose proof (Topx i x Hi) as Xtop.
    unfold K. rewrite <- (SS0 i si Hsi).
    assert (Hdomt : sg_dom_in n (n + (sg_hi SD - sg_lo SD))%nat sg = true /\ entails_t A cs (insts sg (insts rho (sg_in SD))) = true).
    { unfold entails_s in Hent. match type of Hent with (if ?c then _ else _) = _ => destruct c eqn:Hcnd; [|discriminate] end.
      injection Hent as Hsg. rewrite Hsg in Hcnd. apply andb_prop in Hcnd as [Hd1 Hd2]. split; assumption. }
    destruct Hdomt as [Hdom Hentt].
    pose proof (fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    set (Ec := Env (fun v => if (v <? sg_hi SD + d)%nat then ev E v else ev E2 (v - d)%nat) (eb E)).
    assert (AGc : env_agree (sg_hi SD + d)%nat E Ec).
    { split; [|reflexivity]. intros v Hv. unfold Ec. cbn [ev]. destruct (Nat.ltb_spec v (sg_hi SD + d)%nat); [reflexivity | lia]. }
    assert (AGc2 : env_agree nx0 Ec E2).
    { split.
      - intros v Hv. unfold Ec. cbn [ev]. destruct (Nat.ltb_spec v (sg_hi SD + d)%nat); [|lia].
        transitivity (ev Es v); [apply (proj1 AGs); exact Hv | apply (proj1 Hag2); lia].
      - unfold Ec. cbn [eb]. transitivity (eb Es); [exact (proj2 AGs) | exact (proj2 Hag2)]. }
    assert (SGV : forall w e, sg_get sg w = Some e -> (n <= w < n + (sg_hi SD - sg_lo SD))%nat /\ AP.expr_vars_lt n e = true).
    { intros w e Hw. pose proof (sg_get_in sg w e Hw) as Hin.
      pose proof (proj1 (forallb_forall _ _) Hdom (w, e) Hin) as D1. cbn [fst] in D1. apply andb_prop in D1 as [D1 D2]. apply Nat.leb_le in D1. apply Nat.ltb_lt in D2.
      pose proof (proj1 (forallb_forall _ _) Hsgv (w, e) Hin) as D3. cbn [snd] in D3. split; [lia | exact D3]. }
    assert (KEY : env_agree (nxt x) E2 (updl (updl Ec sg) rho)).
    { split.
      2: { cbn [updl eb]. unfold Ec. cbn [eb]. symmetry. transitivity (eb Es); [exact (proj2 AGs) | exact (proj2 Hag2)]. }
      intros v Hv. cbn [updl ev]. unfold rho. rewrite shiftb_get.
      destruct (Nat.leb_spec (sg_lo SD) v) as [Hlov|Hlov].
      - replace (v <? sg_top SD)%nat with true by (symmetry; apply Nat.ltb_lt; lia). cbn [andb edenot updl ev].
        destruct (sg_get sg (v + d)%nat) as [e|] eqn:Hge.
        + destruct (SGV _ _ Hge) as [Q1 Q2].
          transitivity (ev Es v); [symmetry; apply (proj1 Hag2); lia|].
          unfold Es. cbn [updl ev]. unfold rho. rewrite shiftb_get.
          replace ((sg_lo SD <=? v)%nat && (v <? sg_top SD)%nat)%bool with true by (symmetry; apply andb_true_intro; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
          cbn [edenot updl ev]. rewrite Hge. apply (edenot_agree' n); [|exact Q2]. eapply env_agree_le; [exact AGc | lia].
        + unfold Ec. cbn [ev]. destruct (Nat.ltb_spec (v + d)%nat (sg_hi SD + d)%nat) as [H1|H1].
          * transitivity (ev Es v); [symmetry; apply (proj1 Hag2); lia|].
            unfold Es. cbn [updl ev]. unfold rho. rewrite shiftb_get.
            replace ((sg_lo SD <=? v)%nat && (v <? sg_top SD)%nat)%bool with true by (symmetry; apply andb_true_intro; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
            cbn [edenot updl ev]. rewrite Hge. reflexivity.
          * f_equal. lia.
      - replace ((sg_lo SD <=? v)%nat && (v <? sg_top SD)%nat)%bool with false by (symmetry; apply andb_false_iff; left; apply Nat.leb_gt; lia).
        cbn [updl ev]. destruct (sg_get sg v) as [e|] eqn:Hge; [destruct (SGV _ _ Hge) as [Q1 _]; exfalso; lia|].
        unfold Ec. cbn [ev]. replace (v <? sg_hi SD + d)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
        transitivity (ev Es v); [symmetry; apply (proj1 Hag2); lia|].
        unfold Es. cbn [updl ev]. unfold rho. rewrite shiftb_get.
        replace ((sg_lo SD <=? v)%nat && (v <? sg_top SD)%nat)%bool with false by (symmetry; apply andb_false_iff; left; apply Nat.leb_gt; lia).
        cbn [updl ev]. rewrite Hge. reflexivity. }
    pose proof (cs_ok_agree E2 (updl (updl Ec sg) rho) x R2 F2 m2 KEY Xfr HC2) as HCx1.
    apply (proj2 (cs_ok_insts (updl Ec sg) rho x R2 F2 m2 Hrho Xlog)) in HCx1.
    assert (Hsgge : sg_dom_ge nx0 sg = true).
    { unfold sg_dom_ge. apply forallb_forall. intros p Hp. pose proof (proj1 (forallb_forall _ _) (sg_dom_in_ge _ _ _ Hdom) p Hp) as Q. apply Nat.leb_le in Q. apply Nat.leb_le. lia. }
    assert (Xlog2 : s_log (a_ss (insts rho x)) = []) by reflexivity.
    apply (proj2 (cs_ok_insts Ec sg (insts rho x) R2 F2 m2 Hsgge Xlog2)) in HCx1.
    set (xr := insts sg (insts rho x)) in HCx1.
    assert (LED : a_vis (insts sg (insts rho (sg_in SD))) = a_vis cs /\ a_ghost (insts sg (insts rho (sg_in SD))) = a_ghost cs).
    { unfold entails_t in Hentt. repeat match type of Hentt with (_ && _)%bool = true => apply andb_prop in Hentt as [Hentt ?X] end.
      match goal with Ha : list_eqb pair_eqb (a_vis cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ha; rename Ha into Qv end.
      match goal with Hg2 : list_eqb pair_eqb (a_ghost cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hg2; rename Hg2 into Qg end.
      split; [symmetry; exact Qv | symmetry; exact Qg]. }
    destruct LED as [LEDv LEDg].
    assert (FRX : a_vis x = a_vis (sg_in SD) /\ a_ghost x = a_ghost (sg_in SD)).
    { unfold AP.acs_frame_eqb in Wfx. repeat match type of Wfx with (_ && _)%bool = true => apply andb_prop in Wfx as [Wfx ?X] end.
      match goal with Ha : list_eqb pair_eqb (a_vis (sg_in SD)) (a_vis x) = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ha; rename Ha into Pv end.
      match goal with Hb : list_eqb pair_eqb (a_ghost (sg_in SD)) (a_ghost x) = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hb; rename Hb into Pg end.
      split; [symmetry; exact Pv | symmetry; exact Pg]. }
    destruct FRX as [FRXv FRXg].
    assert (XRv : a_vis xr = a_vis cs).
    { unfold xr. rewrite <- LEDv. cbn [insts a_vis]. rewrite FRXv. reflexivity. }
    assert (HIDx : hid Ec xr m2 = hid E cs model).
    { rewrite (hid_ext Ec cs xr m2 XRv). rewrite (hid_mvis Ec cs model m2 Hmv2).
      assert (AGcn0 : env_agree (nxt cs) E Ec) by (eapply env_agree_le; [exact AGc | lia]).
      exact (hid_agree (nxt cs) E Ec cs model AGcn0 Fle Fallow). }
    assert (AGcn : env_agree (nxt cs) E Ec) by (eapply env_agree_le; [exact AGc | lia]).
    assert (KVL : forall b k K, AP.kn_vars_lt b k = true -> In K k -> AP.kn_vars_lt b [K] = true).
    { intros b k K0 Hk Hin. induction k as [|K1 k IHk]; [destruct Hin|]. cbn [AP.kn_vars_lt] in Hk. apply andb_prop in Hk as [Hk1 Hk2].
      destruct Hin as [<-|Hin]; [cbn [AP.kn_vars_lt]; rewrite Hk1; reflexivity | exact (IHk Hk2 Hin)]. }
    assert (WIN : forall a : word, in_windows Es (sg_w SD) a = true ->
              exists wb wk wl, In (SA wb wk, wl) Wc /\ (estart E (SA wb wk) <= bv_unsigned a < estart E (SA wb wk) + elenZ E wl)%Z).
    { intros a Ha. unfold in_windows in Ha. apply existsb_exists in Ha as ([[wb wk] wl] & Hin & Hr).
      apply andb_prop in Hr as [Hr1 Hr2]. apply Z.leb_le in Hr1. apply Z.ltb_lt in Hr2. cbn [fst snd] in Hr1, Hr2.
      destruct (AP.anorm (facts_of (kn cs)) (SA (esubsts sg (esubsts rho wb)) wk)) as [wb2 wk2] eqn:Hn2.
      pose proof (proj1 (anorm_sem (facts_of (kn cs)) E _ (SA (esubsts sg (esubsts rho wb)) wk) (facts_of_ok SEGS E _ _ (co_know _ _ _ _ _ HC)))) as EQ2.
      rewrite Hn2 in EQ2.
      exists wb2, wk2, (esubsts sg (esubsts rho wl)). split.
      - unfold Wc, AP.wsubsts. apply in_map_iff. exists (SA (esubsts sg (esubsts rho wb)) wk, esubsts sg (esubsts rho wl)).
        split; [unfold AP.wnorm; cbn [fst snd]; rewrite Hn2; reflexivity|].
        apply in_map_iff. exists (asubsts rho (SA wb wk), esubsts rho wl). split; [reflexivity|].
        apply in_map_iff. exists (SA wb wk, wl). split; [reflexivity | exact Hin].
      - rewrite EQ2. unfold Es in Hr1, Hr2. unfold estart, elenZ in *. cbn [a_base a_off] in *. rewrite !esubsts_denot. lia. }
    assert (FROK : know_ok SEGS Ec (Mr Ec xr m2 F2) FR).
    { apply Forall_forall. intros Ke HK. unfold FR in HK. apply in_flat_map in HK as (K0 & HKin0 & HKe).
      pose proof (proj1 (Forall_forall _ _) (co_know _ _ _ _ _ HC) K0 HKin0) as HK0E.
      assert (KV0 : AP.kentry_vars_lt (nxt cs) K0 = true).
      { pose proof (KVL _ _ _ Fkn HKin0) as KV1. cbn [AP.kn_vars_lt] in KV1. apply andb_prop in KV1 as [KV1 _]. exact KV1. }
      (* [comment removed for export] *)
      assert (PIECES : (AP.kpure K0 = true /\ Ke = K0)
                       \/ (kentry_ok SEGS E (Mr E cs model FULL) Ke /\ AP.kentry_vars_lt (nxt cs) Ke = true
                           /\ exists ka kl, AP.kfoot Ke = Some (ka, kl) /\ forall w, In w Wc -> apartw E w ka kl)).
      { destruct (AP.kpure K0) eqn:Hpure; [left; destruct HKe as [<-|[]]; split; reflexivity | right].
        destruct (AP.kfoot K0) as [[ka0 kl0]|] eqn:Hkf0; [|destruct HKe]. unfold AP.wcut in HKe.
        pose proof (wcut_ok (facts_of (kn cs)) E (Mr E cs model FULL) (Mr E cs model FULL) (nxt cs) Wc [] [K0]
                      (facts_of_ok SEGS E _ _ (co_know _ _ _ _ _ HC))) as WO.
        destruct (WO ltac:(intros P [<-|[]]; split; [exact HK0E|]; split; [exact KV0|]; exists ka0, kl0; split; [exact Hkf0 | intros w []]) Ke HKe)
          as (O1 & O2 & ka & kl & O3 & O4).
        split; [exact O1|]. split; [exact O2|]. exists ka, kl. split; [exact O3|]. intros w Hw. apply O4. exact Hw. }
      assert (HKEE : kentry_ok SEGS E (Mr E cs model FULL) Ke) by (destruct PIECES as [[_ ->]|[X _]]; [exact HK0E | exact X]).
      assert (KV : AP.kentry_vars_lt (nxt cs) Ke = true) by (destruct PIECES as [[_ ->]|(_ & X & _)]; [exact KV0 | exact X]).
      assert (HK1 : kentry_ok SEGS Ec (Mr E cs model FULL) Ke).
      { apply (proj1 (Forall_forall _ _) (know_ok_agree' (nxt cs) E Ec _ [Ke] AGcn ltac:(cbn [AP.kn_vars_lt]; rewrite KV; reflexivity) ltac:(constructor; [exact HKEE | constructor]))). left. reflexivity. }
      unfold Mr. rewrite HIDx. unfold Mr in HK1.
      destruct PIECES as [[Hpure ->] | (_ & _ & ka & kl & Hkf & APT)].
      - destruct K0; try discriminate Hpure; exact HK1.
      - assert (MEQ : forall a : word, (estart Ec ka <= bv_unsigned a < estart Ec ka + elenZ Ec kl)%Z ->
                  mrestrict (hid E cs model) F2 a = mrestrict (hid E cs model) FULL a).
        { intros a Ha. unfold mrestrict. destruct (hid E cs model a); [reflexivity|]. apply Hfr2.
          destruct (in_windows Es (sg_w SD) a) eqn:Hw; [|reflexivity]. exfalso.
          destruct (WIN a Hw) as (wb & wk & wl & HinW & Hra).
          destruct ka as [kb kk].
          pose proof (APT (SA wb wk, wl) HinW) as DIS. unfold apartw in DIS. cbn [fst snd] in DIS.
          assert (EK1 : estart Ec (SA kb kk) = estart E (SA kb kk) /\ elenZ Ec kl = elenZ E kl).
          { destruct Ke; cbn [AP.kfoot] in Hkf; try discriminate Hkf;
              try match type of Hkf with (if ?c then _ else _) = _ => destruct c; [|discriminate Hkf] end;
              injection Hkf as Q1 Q2; subst;
              cbn [AP.kentry_vars_lt] in KV; unfold AP.saddr_vars_lt in KV; cbn [a_base] in KV;
              repeat match type of KV with (_ && _)%bool = true => apply andb_prop in KV as [KV ?Y] end;
              unfold estart, elenZ; cbn [a_base a_off edenot];
              repeat match goal with Hq : AP.expr_vars_lt (nxt cs) ?e = true |- _ => rewrite <- (edenot_agree' (nxt cs) E Ec _ AGcn Hq); clear Hq end;
              split; reflexivity. }
          destruct EK1 as [EK1 EK2]. rewrite EK1, EK2 in Ha. lia. }
        destruct Ke as [[kb kk] w v|[kb kk] kn0|[kb kk] kn0 bk|lo hi|ae am|re rlo rhi|[kb kk] kn0|da1 dn1 da2 dn2|[kb kk] kn0 fc|[kb kk] kn0];
          cbn [AP.kfoot] in Hkf; try discriminate Hkf;
          lazymatch type of Hkf with (if _ then _ else _) = _ => idtac | _ => injection Hkf as <- <-; cbn [kentry_ok] in HK1 |- * end.
        + (* [comment removed for export] *) destruct HK1 as (W1 & W2 & W3). split; [exact W1|]. split; [exact W2|]. rewrite <- W3. symmetry. apply rdn_ext.
          * pose proof (flat_u Ec _ _ W2) as U. destruct W2 as (F1 & F2' & F3 & F4). rewrite U. lia.
          * intros a Ha. symmetry. apply MEQ. pose proof (flat_u Ec _ _ W2) as U. rewrite U in Ha. unfold elenZ. cbn [edenot]. rewrite u64_lit by lia. lia.
        + (* [comment removed for export] *) destruct HK1 as [W1 W2]. split; [exact W1|]. intros i0 Hi0. rewrite <- (W2 i0 Hi0). apply MEQ.
          destruct W1 as (F1 & F2' & F3 & F4). rewrite u64_lit by lia. lia.
        + (* [comment removed for export] *) destruct HK1 as (W1 & W2 & W3). split; [exact W1|]. split; [exact W2|]. intros i0 Hi0. rewrite <- (W3 i0 Hi0). apply MEQ.
          destruct W1 as (F1 & F2' & F3 & F4). rewrite u64_lit by lia. lia.
        + (* [comment removed for export] *) destruct (Z.ltb_spec (hi - lo) two64) as [Hhl|Hhl]; [|discriminate Hkf]. injection Hkf as <- <-. cbn [kentry_ok] in HK1 |- *.
          unfold two64 in Hhl. destruct HK1 as (W1 & W2 & W3). split; [exact W1|]. split; [exact W2|]. intros i0 Hi0. rewrite <- (W3 i0 Hi0). apply MEQ.
          unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite !u64_lit by lia. lia.
        + (* [comment removed for export] *) destruct HK1 as [W1 W2]. split; [exact W1|]. intros d0 m1 Hd0 Hm1.
          destruct m1 as [|m1']; [reflexivity|].
          destruct W1 as (F1 & F2' & F3 & F4).
          rewrite (store_ok_memeq (Datatypes.S m1') (mrestrict (hid E cs model) F2) (mrestrict (hid E cs model) FULL)); [exact (W2 d0 (Datatypes.S m1') Hd0 Hm1) | rewrite u64_lit by lia; lia |].
          intros a Ha. rewrite u64_lit in Ha by lia. apply MEQ. lia.
        + (* [comment removed for export] *) destruct HK1 as [W1 W2]. split; [exact W1|]. intros i0 Hi0. rewrite <- (W2 i0 Hi0). apply MEQ.
          destruct W1 as (F1 & F2' & F3 & F4). rewrite u64_lit by lia. lia.
        + (* [comment removed for export] *) destruct HK1 as [W1 W2]. split; [exact W1|]. intros i0 Hi0. rewrite MEQ; [exact (W2 i0 Hi0)|].
          destruct W1 as (F1 & F2' & F3 & F4). rewrite u64_lit by lia. lia. }
    
    assert (KALL : know_ok SEGS Ec (Mr Ec xr m2 F2) (kn xr ++ FR)) by (apply Forall_app; split; [exact (co_know _ _ _ _ _ HCx1) | exact FROK]).
    assert (HCe : cs_ok Ec (AP.use_exit sg rho d FR KP x) R2 F2 m2).
    { unfold AP.use_exit. fold xr.
      destruct HCx1; constructor; cbn [set_props with_ss a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_props kn mk_ss s_regs s_log s_know]; try assumption; try reflexivity.
      apply Forall_app. split.
      - (* [comment removed for export] *)
        eapply incl_Forall; [apply incl_filter|].
        apply (proj2 (Forall_map _ _ _)). apply Forall_forall. intros Ke HKe. apply (knorm_ok _ Ke Ec _ KALL).
        exact (proj1 (Forall_forall _ _) KALL Ke (in_or_app _ _ _ (or_introl HKe))).
      - apply incl_Forall with (l1 := FR); [apply incl_filter | exact FROK]. }
    (* [comment removed for export] *)
    assert (FRW : forall a, ws_out E Wc a -> F2 a = FULL a).
    { intros a Ha. apply Hfr2. destruct (in_windows Es (sg_w SD) a) eqn:Hw; [|reflexivity]. exfalso.
      destruct (WIN a Hw) as (wb & wk & wl & HinW & Hra). destruct (Ha (SA wb wk, wl) HinW) as [Q|Q]; cbn [fst snd] in Q; lia. }
    (* [comment removed for export] *)
    assert (HPe : props_ok Ec (Mr Ec (AP.use_exit sg rho d FR KP x) m2 F2) (a_props (AP.use_exit sg rho d FR KP x))).
    { replace (a_props (AP.use_exit sg rho d FR KP x)) with KP by reflexivity.
      assert (XRv' : a_vis (AP.use_exit sg rho d FR KP x) = a_vis cs) by (rewrite <- XRv; reflexivity).
      unfold Mr. rewrite (hid_ext Ec cs (AP.use_exit sg rho d FR KP x) m2 XRv'). rewrite (hid_mvis Ec cs model m2 Hmv2).
      rewrite (hid_agree (nxt cs) E Ec cs model AGcn Fle Fallow).
      unfold KP. apply (props_ok_gkeepE E Ec (Mr E cs model FULL) _ (Mr E cs model FULL) (facts_of (kn cs)) Wc (nxt cs) (a_props cs) HP AGcn (facts_of_ok SEGS E _ _ (co_know _ _ _ _ _ HC))).
      intros a Ha. unfold Mr, mrestrict. destruct (hid E cs model a); [reflexivity|]. exact (FRW a Ha). }
    assert (HL2 : LCOK E0 M0 m0 lc D Ec (m_fs m2)).
    { rewrite Hfs2. eapply LCOK_agree; [exact HL | exact Hg | exact AGcn]. }
    (* [comment removed for export] *)
    assert (HW2 : WI E0 M0 m0 Ec F2 m2).
    { exact (WI_ws _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Some Wc) Wc _ HW HL Hg AGcn Hok eq_refl (facts_of_ok SEGS E _ _ (co_know _ _ _ _ _ HC)) FRW Hmv2). }
    pose proof (IH bfuel lc ki (AP.use_exit sg rho d FR KP x) si Hck fy2 Ec R2 F2 m2 D E0 M0 m0 Hz2 HCe HPe HW2 HL2 HD) as RZ.
    replace (pc (AP.use_exit sg rho d FR KP x)) with (pc x) in RZ by reflexivity.
    rewrite Hfs2 in RZ. rewrite (sd_agree D Ec E2 (m_fs model) si AGc2) in RZ; [exact RZ|].
    rewrite <- (nth_error_nth ss i SNil Hsi). exact (Kvars i).
  - (* [comment removed for export] *)
    destruct (gvars_lt (nxt cs) gg) eqn:Hgv; [|discriminate].
    destruct (need1 xp cs (VCAtom gg)) eqn:Hn1; [|match type of Hc with (match ?r with _ => _ end = _) => destruct r; discriminate end].
    apply (SAME gk _ s Hc (cs_ok_set_props _ _ _ _ _ _ HC)).
    unfold set_props. cbn [a_props]. constructor; [|exact HP].
    exact (need1_sound cs (VCAtom gg) E _ Hn1 (co_know _ _ _ _ _ HC) HP).
  - (* [comment removed for export] *)
    apply (SAME gdk _ s Hc (cs_ok_set_props _ _ _ _ _ _ HC)).
    unfold set_props. cbn [a_props]. unfold props_ok in *. apply Forall_forall. intros g Hin.
    apply (proj1 (Forall_forall _ _) HP g). revert Hin. generalize (a_props cs) gi. clear.
    induction l as [|x l IHl]; intros [|i] H; cbn [remove_nth] in H; [destruct H | destruct H | right; exact H |].
    destruct H as [<-|H]; [left; reflexivity | right; exact (IHl i H)].
  - (* [comment removed for export] *)
    destruct (kentry_vars_lt (nxt cs) gK) eqn:Hkv; [|discriminate].
    destruct (need1 xp cs (VCFact gK)) eqn:Hn1; [|match type of Hc with (match ?r with _ => _ end = _) => destruct r; discriminate end].
    apply (SAME gfk _ s Hc); [|exact HP].
    unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact (co_know _ _ _ _ _ HC)].
    exact (need1_sound cs (VCFact gK) E _ Hn1 (co_know _ _ _ _ _ HC) HP).
  - (* [comment removed for export] *)
    destruct (tfact_inst lc cs gtx gti gtK) as [gK|]; [|discriminate].
    destruct (kentry_vars_lt (nxt cs) gK) eqn:Hkv; [|discriminate].
    destruct (need1 xp cs (VCFact gK)) eqn:Hn1; [|match type of Hc with (match ?r with _ => _ end = _) => destruct r; discriminate end].
    apply (SAME gtfk _ s Hc); [|exact HP].
    unfold add_kn_end. apply cs_ok_set_kn; [exact HC|]. apply Forall_app. split; [exact (co_know _ _ _ _ _ HC)|].
    constructor; [|constructor]. exact (need1_sound cs (VCFact gK) E _ Hn1 (co_know _ _ _ _ _ HC) HP).
  - (* [comment removed for export] *)
    apply GW in Hc as [HN Hc].
    destruct (HS sh) as [ch|] eqn:Hh; [|discriminate].
    destruct (Nat.leb nx0 slo && match s_log (a_ss ch) with [] => true | _ => false end)%bool eqn:Ht; [|discriminate].
    destruct (entails_s A slo (nxt ch) shints cs ch) as [sg|] eqn:Hent; [|discriminate].
    apply with_props_ok in Hc as [Hnp Hc]. injection Hc as <-. cbn [sd].
    apply andb_prop in Ht as [Hlo Hlog]. apply Nat.leb_le in Hlo.
    assert (Hlog' : s_log (a_ss ch) = []) by (destruct (s_log (a_ss ch)); [reflexivity | discriminate Hlog]).
    destruct (entails_s_sound slo (nxt ch) shints E cs ch sg R FULL model HC Hent Hlo Hlog') as (Hag & HC' & Hpc' & _ & HH).
    rewrite (HOLES_agree sh E (updl E sg) (m_fs model) (env_agree_le _ _ _ _ Hag Hlo)). rewrite <- Hpc'.
    apply (HS_sound fy Hz sh ch Hh (updl E sg) R FULL model HC').
    exact (template_props_ok cs ch sg E R FULL model HC HP Hnp HH).
  - (* [comment removed for export] *)
    apply GW in Hc as [HN Hc].
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_brk2 A LIMIT cs) as [[csg csf]|] eqn:Hn; [|discriminate].
    apply cmerge_ok in Hc as (s1 & s2 & H1 & H2 & Hc). cbn beta in H2.
    match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hse; [|discriminate] end. injection Hc as <-.
    eapply (@node_brk2_sound fy cs csg csf E R FULL model); [exact HC | exact Hec | exact Hn | |].
    + exact (fun E' R' F' m' Hag HC' Hfs => CONTF HN kga (gpures (xp_gh xp) cs csg) s1 H1 E' R' F' m' Hag (cs_ok_set_props _ _ _ _ _ _ HC') (props_ok_gpures _ _ _ _ cs csg HP (proj2 Hag)) Hfs).
    + rewrite <- (shape_ok2 s1 s2 Hse).
      exact (fun E' R' F' m' Hag HC' Hfs => CONTF HN kgf (gpures (xp_gh xp) cs csf) s2 H2 E' R' F' m' Hag (cs_ok_set_props _ _ _ _ _ _ HC') (props_ok_gpures _ _ _ _ cs csf HP (proj2 Hag)) Hfs).
  - (* [comment removed for export] *)
    apply GW in Hc as [HN Hc].
    destruct (node_casedisjJ A cs jjb1 jjb2) as [[csl ocb]|] eqn:Hn; [|discriminate].
    pose proof (LCOK_bnd E0 M0 m0 lc D E (m_fs model) HL) as Hgb.
    pose proof (node_casedisjJ_sound cs jjb1 jjb2 csl ocb E R FULL model HC Hn) as CJ.
    assert (MRK : forall K E' ca0 model' FULL' (P : word -> Prop),
              (forall a, P a -> Mr E' ca0 model' FULL' a = Mr E (set_kn cs K) model FULL a) ->
              forall a, P a -> Mr E' ca0 model' FULL' a = Mr E cs model FULL a).
    { intros K E' ca0 model' FULL' P H a Ha. rewrite (H a Ha). unfold Mr. rewrite (hid_ext E cs (set_kn cs K) model eq_refl). reflexivity. }
    destruct ocb as [csb|].
    2:{ (* [comment removed for export] *)
      destruct CJ as [HCl [Kl EKl]]. subst csl.
      destruct (run_block_gc_wb_ws SEGS IT _ (AP.WB xp) KC bfuel (jjp :: STOPS A) (set_kn cs (Kl :: kn cs))) as [[cs1 W1]|] eqn:Hrb; [|discriminate].
      destruct (Z.eqb (pc cs1) jjp); [|discriminate].
      rewrite <- (pc_set_kn cs (Kl :: kn cs)).
      eapply run_block_gc_wb_ws_sound; [exact Hz | exact Hgb | exact Hrb | exact HCl | exact HW | exact (WB_run _ _ _ _ _ _ _ _ HL Hg) |].
      intros fy' E' R' FULL' model' Hz' Hag HC1 HW1 Hfs HW8 Hmr.
      exact (CONTW jk (gkeep (xp_gh xp) W1 cs cs1) s Hc fy' E' R' FULL' model' Hz' Hag (cs_ok_set_props _ _ _ _ _ _ HC1)
               (props_ok_gkeep _ _ _ _ _ cs cs1 W1 HP (proj2 Hag) (co_know _ _ _ _ _ HC1) HW8 (MRK _ _ _ _ _ _ Hmr)) HW1 Hfs). }
    destruct CJ as (CJ & [K1 EK1] & [K2 EK2]). subst csl csb.
    destruct (run_block_gc_wb_ws SEGS IT _ (AP.WB xp) KC bfuel (jjp :: STOPS A) (set_kn cs (K1 :: kn cs))) as [[ca Wa]|] eqn:Hra; [|discriminate].
    destruct (run_block_gc_wb_ws SEGS IT _ (AP.WB xp) KC bfuel (jjp :: STOPS A) (set_kn cs (K2 :: kn cs))) as [[cb Wb]|] eqn:Hrb; [|discriminate].
    destruct (node_diamond_join A nx0 (nxt cs) jjp jrs ca cb) as [csj|] eqn:Hj; [|discriminate].
    destruct (diamond_join_sound2 (nxt cs) jjp jrs ca cb csj Hj) as (Ja & Jb & Jvis & Jgh & Jka & Jkb).
    destruct (run_block_gc_wb_ws_vis _ _ _ _ _ _ _ Hra) as (Va & Ga & Fa).
    destruct (run_block_gc_wb_ws_vis _ _ _ _ _ _ _ Hrb) as (Vb & Gb & Fb).
    destruct (fresh_ok_parts _ (fresh_ok_mono _ _ Hgb Fa)) as (_ & _ & _ & Fallow & _ & _ & Fle).
    change (pairs_vars_lt (nxt cs) (a_vis cs ++ a_ghost cs) = true) in Fallow. change (nx0 <= nxt cs)%nat in Fle.
    change (a_vis ca = a_vis cs) in Va. change (a_ghost ca = a_ghost cs) in Ga.
    change (a_vis cb = a_vis cs) in Vb. change (a_ghost cb = a_ghost cs) in Gb.
    assert (KEEP : forall (ca0 : acs) (Wa0 : list (saddr * nat)) E' E'' R' FULL' model',
              incl Wa0 (Wa ++ Wb) -> incl (kn csj) (kn ca0) ->
              a_vis ca0 = a_vis cs -> a_ghost ca0 = a_ghost cs -> a_vis csj = a_vis ca0 ->
              env_agree (nxt cs) E E' -> env_agree (nxt cs) E' E'' -> cs_ok E' ca0 R' FULL' model' ->
              Forall (fun w => (snd w <= 8)%nat) Wa0 ->
              (forall a, wout E' Wa0 a -> Mr E' ca0 model' FULL' a = Mr E cs model FULL a) ->
              props_ok E'' (Mr E'' csj model' FULL') (a_props (gkeep (xp_gh xp) (Wa ++ Wb) cs csj))).
    { intros ca0 Wa0 E' E'' R' FULL' model' Hincl Hkn Hva Hga Hvj Hag1 Hag2 HCa HW8 Hmr.
      unfold gkeep, set_props. cbn [a_props].
      assert (Hhid : hid E'' csj model' = hid E' ca0 model').
      { eapply (hid_extF (nxt cs)); [exact Hvj | exact Hag2 | exact Fle | rewrite Hva, Hga; exact Fallow | apply mvis_refl]. }
      assert (HMr : Mr E'' csj model' FULL' = Mr E' ca0 model' FULL') by (unfold Mr; rewrite Hhid; reflexivity).
      rewrite HMr. apply (props_ok_gkeep1_agree E' E''); [exact Hag2|].
      eapply (props_ok_gkeep_sub E E' _ _ (Mr E' ca0 model' FULL') (kn csj) (Wa ++ Wb) Wa0 (s_next (a_ss cs)) (a_props cs) HP Hag1);
        [ eapply incl_Forall; [exact Hkn | exact (co_know _ _ _ _ _ HCa)] | exact Hincl | exact HW8 | exact Hmr]. }
    destruct CJ as [HCa0|HCb0].
    + rewrite <- (pc_set_kn cs (K1 :: kn cs)).
      eapply run_block_gc_wb_ws_sound; [exact Hz | exact Hgb | exact Hra | exact HCa0 | exact HW | exact (WB_run _ _ _ _ _ _ _ _ HL Hg) |].
      intros fy' E' R' FULL' model' Hz' [Hag0 Hag1] HC1 HW1 Hfs HW8 Hmr.
      destruct (Ja E' R' FULL' model' HC1) as (E'' & (Hag2a & Hag2b & Hag2c) & HC2 & Hpc2). rewrite <- Hpc2.
      change (env_agree (nxt cs) E E') in Hag1.
      exact (CONT HN jk (gkeep (xp_gh xp) (Wa ++ Wb) cs csj) s Hc fy' E'' R' FULL' model' Hz'
               (conj (env_agree_trans _ _ _ _ Hag0 Hag2a) (env_agree_trans _ _ _ _ Hag1 Hag2b)) (cs_ok_set_props _ _ _ _ _ _ HC2)
               (KEEP ca Wa E' E'' R' FULL' model' (incl_appl Wb (incl_refl Wa)) Jka Va Ga Jvis Hag1 Hag2b HC1 HW8 (MRK _ _ _ _ _ _ Hmr)) Hfs).
    + rewrite <- (pc_set_kn cs (K2 :: kn cs)).
      eapply run_block_gc_wb_ws_sound; [exact Hz | exact Hgb | exact Hrb | exact HCb0 | exact HW | exact (WB_run _ _ _ _ _ _ _ _ HL Hg) |].
      intros fy' E' R' FULL' model' Hz' [Hag0 Hag1] HC1 HW1 Hfs HW8 Hmr.
      destruct (Jb E' R' FULL' model' HC1) as (E'' & (Hag2a & Hag2b & Hag2c) & HC2 & Hpc2). rewrite <- Hpc2.
      change (env_agree (nxt cs) E E') in Hag1.
      exact (CONT HN jk (gkeep (xp_gh xp) (Wa ++ Wb) cs csj) s Hc fy' E'' R' FULL' model' Hz'
               (conj (env_agree_trans _ _ _ _ Hag0 Hag2a) (env_agree_trans _ _ _ _ Hag1 Hag2b)) (cs_ok_set_props _ _ _ _ _ _ HC2)
               (KEEP cb Wb E' E'' R' FULL' model' (incl_appr Wa (incl_refl Wb)) Jkb Vb Gb (eq_trans Jvis (eq_trans Va (eq_sym Vb))) Hag1 Hag2b HC1 HW8 (MRK _ _ _ _ _ _ Hmr)) Hfs).
Qed.

(* [comment removed for export] *)
Corollary check_sound_top : xp_wb xp = None -> forall fuel bfuel p cs s,
  CHECK bfuel fuel None cs p = COk s ->
  forall (fy : FPState) E R FULL model D, frm_zero (@fp_csr fy) ->
  cs_ok E cs R FULL model -> props_ok E (Mr E cs model FULL) (a_props cs) -> D [] ->
  srealizes SEGS (cfgF fy R (pc cs) FULL model) (sd D E (m_fs model) s).
Proof.
  intros HN fuel bfuel p cs s Hc fy E R FULL model D Hz HC HP HD.
  apply (check_sound fuel bfuel None p cs s Hc fy E R FULL model D E FULL model Hz HC HP (WI_none _ _ _ _ _ _ HN)); [|exact HD].
  split; [unfold WBOK; rewrite HN; exact I | exact I].
Qed.

End Sound.

(* [comment removed for export] *)
Definition GP0 : nat -> list Z -> (word -> option byte) -> Prop := fun _ _ _ => True.
Lemma GP0_frame : forall (G : gparams) id args E M M',
  (forall a, in_fp E (g_fp G id args) a = true -> M' a = M a) -> GP0 id (map (uE E) args) M -> GP0 id (map (uE E) args) M'.
Proof. intros; exact I. Qed.
Lemma G0_ok : forall SEGS (GP : nat -> list Z -> (word -> option byte) -> Prop) v, g_vcok G0 v = true -> vc_holds SEGS GP v.
Proof. intros SEGS GP v H. discriminate H. Qed.
(* [comment removed for export] *)
Lemma vc_list_ok : forall SEGS (GP : nat -> list Z -> (word -> option byte) -> Prop) L,
  Forall (vc_holds SEGS GP) L -> forall v, AP.vc_list L v = true -> vc_holds SEGS GP v.
Proof.
  intros SEGS GP L HL v Hr. unfold AP.vc_list in Hr. apply existsb_exists in Hr as [w [Hin Heq]]. unfold AP.vc_implied in Heq.
  destruct (vconcl_eqb (vc_concl v) (vc_concl w)) eqn:Hc; [|discriminate].
  destruct (forallb (fun K => existsb (kentry_eqb K) (vc_kn v)) (vc_kn w)) eqn:Hk; [|discriminate]. rename Heq into Hh.
  apply vconcl_eqb_eq in Hc.
  pose proof (proj1 (Forall_forall _ _) HL w Hin) as Hw. unfold vc_holds in Hw |- *. intros E M HK HP. rewrite Hc. apply (Hw E M).
  - unfold know_ok. apply Forall_forall. intros K HK1. pose proof (proj1 (forallb_forall _ _) Hk K HK1) as X.
    apply existsb_exists in X as [K' [HK2 HK3]]. apply kentry_eqb_eq in HK3. subst K'. exact (proj1 (Forall_forall _ _) HK K HK2).
  - apply Forall_forall. intros g Hg1. pose proof (proj1 (forallb_forall _ _) Hh g Hg1) as X.
    apply existsb_exists in X as [g' [Hg2 Hg3]]. apply gatom_eqb_eq in Hg3. subst g'. exact (proj1 (Forall_forall _ _) HP g Hg2).
Qed.
(* [comment removed for export] *)
Lemma props_ok_GP0 : forall E M l, props_ok GP0 E M l.
Proof. intros E M l. unfold props_ok. apply Forall_forall. intros g _. exact I. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SegSound.
Variable SEGS : list Segment.
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable A : atable.
Variable nx0 : nat.
Hypothesis NX0_min : nx0_min_ok nx0.   (* [comment removed for export] *)
Variable LIMIT : Z.
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis SHADOW_ok : shadow_ok A.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable FS0 : Fs.Fs.
Variable KC : nat.
Variable xp0 : xparams.   (* [comment removed for export] *)
Hypothesis node_sys_sound : forall (fy : FPState) y, sys_stmt SEGS A nx0 LIMIT SINV argH FS0 (fx:=fy) y.
Hypothesis node_brk2_sound : forall (fy : FPState), brk2d_stmt SEGS A nx0 LIMIT SINV argH FS0 (fx:=fy) (node_brk2 A LIMIT).   (* [comment removed for export] *)
Hypothesis node_mmap_sound : forall (fy : FPState), mmap_stmtW SEGS A nx0 LIMIT SINV argH FS0 (fx:=fy).   (* [comment removed for export] *)
Hypothesis node_mmapin_sound : forall (fy : FPState), node1_stmt SEGS A nx0 LIMIT SINV argH FS0 (fx:=fy) (is_ecall_at SEGS) (node_mmapin A LIMIT).
Hypothesis node_mprotect_sound : forall (fy : FPState), node1_stmt SEGS A nx0 LIMIT SINV argH FS0 (fx:=fy) (is_ecall_at SEGS) (node_mprotect A LIMIT).
Hypothesis node_exit_sound : forall (fy : FPState), exit_stmt SEGS A LIMIT SINV argH FS0 (fx:=fy).
Hypothesis node_x_sound : forall (fy : FPState) x, x_stmt SEGS A nx0 LIMIT SINV argH FS0 (fx:=fy) x.
Hypothesis node_join_sound : forall (fy : FPState), join_stmt SEGS A nx0 LIMIT SINV argH FS0 (fx:=fy).
Hypothesis node_ext_sound : forall (fy : FPState), ext_stmt SEGS A nx0 LIMIT XN SINV argH FS0 (fx:=fy).
Hypothesis node_emit_sound : forall (fy : FPState), emit_stmt SEGS A nx0 LIMIT XE SINV argH FS0 (fx:=fy).
Hypothesis node_ext2_sound : forall (fy : FPState), ext2_stmt SEGS A nx0 LIMIT XB SINV argH FS0 (fx:=fy).
Hypothesis node_extF_sound : forall (fy : FPState) id, xp_extF xp0 id = true -> ext_stmtF SEGS A nx0 LIMIT XN SINV argH FS0 (fx:=fy) id.
Hypothesis node_sysW_sound : forall (fy : FPState) y cs ws, xp_sysws xp0 y cs = Some ws ->
  node1_stmtW_at SEGS A nx0 LIMIT SINV argH FS0 (fx:=fy) (is_ecall_at SEGS) (node_sys A nx0 y) cs ws.
Hypothesis node_extW_sound : forall (fy : FPState) id args cs ws, xp_xnws xp0 id args cs = Some ws ->
  node1_stmtW_at SEGS A nx0 LIMIT SINV argH FS0 (fx:=fy) always (XN id args) cs ws.
Hypothesis node_emitW_sound : forall (fy : FPState) id args cs ws, xp_xews xp0 id args cs = Some ws ->
  emit_stmtW_at SEGS A nx0 LIMIT XE SINV argH FS0 (fx:=fy) id args cs ws.
Hypothesis node_xW_sound : forall (fy : FPState) x args cs ws, xp_xws xp0 x args cs = Some ws ->
  node1_stmtW_at SEGS A nx0 LIMIT SINV argH FS0 (fx:=fy) always (node_x SEGS A nx0 x args) cs ws.
(* [comment removed for export] *)
Variable GPs : nat -> list Z -> (word -> option byte) -> Prop.
Hypothesis GPs_frame : forall id args E M M',
  (forall a, in_fp E (g_fp (xp_gh xp0) id args) a = true -> M' a = M a) ->
  GPs id (map (uE E) args) M -> GPs id (map (uE E) args) M'.
Hypothesis Gs_ok : forall v, g_vcok (xp_gh xp0) v = true -> vc_holds SEGS GPs v.

(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis sysws_reL : forall y cs L, xp_sysws xp0 y (with_ledger L cs) = xp_sysws xp0 y cs.
Hypothesis xnws_reL : forall id args cs L, xp_xnws xp0 id args (with_ledger L cs) = xp_xnws xp0 id args cs.
Hypothesis xews_reL : forall id args cs L, xp_xews xp0 id args (with_ledger L cs) = xp_xews xp0 id args cs.
Hypothesis xws_reL : forall x args cs L, xp_xws xp0 x args (with_ledger L cs) = xp_xws xp0 x args cs.
Hypothesis XN_reL : forall id args cs cs' L, (xp_extF xp0 id = true \/ xp_xnws xp0 id args cs <> None) ->
  ledger_vars_lt (nxt cs) L = true -> XN id args cs = Some cs' -> XN id args (with_ledger L cs) = Some (with_ledger L cs').
Hypothesis XE_reL : forall id args cs fd ps cs' L, xp_xews xp0 id args cs <> None ->
  ledger_vars_lt (nxt cs) L = true -> XE id args cs = Some (fd, ps, cs') -> XE id args (with_ledger L cs) = Some (fd, ps, with_ledger L cs').
#[local] Notation SEGSEM SD := (seg_sem SEGS A nx0 LIMIT SINV argH FS0 SD) (only parsing).

(* [comment removed for export] *)
Lemma check_reledger_seg : forall sid SD L s,
  AP.segdef_wf nx0 SD = true -> ledger_vars_lt (sg_hi SD) L = true -> APL.ledger_evars L = true ->
  lens_le L (ledger_of (sg_in SD)) ->
  AP.check SEGS IT A nx0 LIMIT XN XE XB (fun _ => None) KC (xp_seg xp0 (sg_w SD) (sg_hi SD) sid) (sg_bfuel SD) (sg_fuel SD)
           (Some (SC (sg_outs SD) (sg_hi SD))) (sg_in SD) (sg_body SD) = COk s ->
  AP.check SEGS IT A nx0 LIMIT XN XE XB (fun _ => None) KC (xp_seg xp0 (sg_w SD) (sg_hi SD) sid) (sg_bfuel SD) (sg_fuel SD)
           (Some (SC (map (with_ledger L) (sg_outs SD)) (sg_hi SD))) (with_ledger L (sg_in SD)) (sg_body SD) = COk s.
Proof.
  intros sid SD L s Hwf HL He Hlen Hc.
  pose proof (segdef_wf_facts nx0 SD Hwf) as (_ & _ & W3 & W4 & _).
  assert (HC : ledger_vars_lt (sg_hi SD) (ledger_of (sg_in SD)) = true).
  { unfold template_ok in W4. repeat match type of W4 with (_ && _)%bool = true => apply andb_prop in W4 as [W4 ?X] end.
    pose proof (fresh_ok_parts nx0 _ W4) as (_ & _ & F3 & F4 & _). rewrite W3 in F3, F4.
    unfold ledger_vars_lt. cbn [ledger_of lg_maps lg_vis lg_ghost]. unfold pairs_vars_lt in *. rewrite forallb_app in F4.
    apply andb_prop in F4 as [F4 F5]. rewrite F3, F4, F5. reflexivity. }
  set (xp := xp_seg xp0 (sg_w SD) (sg_hi SD) sid) in *.
  assert (HXN : forall id args cs cs' L0, AP.ext_okW xp id args cs = true -> ledger_vars_lt (nxt cs) L0 = true ->
            XN id args cs = Some cs' -> XN id args (with_ledger L0 cs) = Some (with_ledger L0 cs')).
  { intros id args cs cs' L0 Hok HL0 HX. apply (XN_reL id args cs cs' L0); [|exact HL0|exact HX].
    unfold AP.ext_okW, AP.okW in Hok. cbn [xp xp_extF xp_xnws xp_wb xp_seg] in Hok.
    destruct (xp_extF xp0 id); [left; reflexivity | right]. cbn [orb] in Hok.
    destruct (xp_xnws xp0 id args cs); [discriminate | discriminate Hok]. }
  assert (HXE : forall id args cs fd ps cs' L0, AP.emit_okW xp id args cs = true -> ledger_vars_lt (nxt cs) L0 = true ->
            XE id args cs = Some (fd, ps, cs') -> XE id args (with_ledger L0 cs) = Some (fd, ps, with_ledger L0 cs')).
  { intros id args cs fd ps cs' L0 Hok HL0 HX. apply (XE_reL id args cs fd ps cs' L0); [|exact HL0|exact HX].
    unfold AP.emit_okW, AP.okW in Hok. cbn [xp xp_xews xp_wb xp_seg] in Hok.
    destruct (xp_xews xp0 id args cs); [discriminate | discriminate Hok]. }
  change (Some (SC (map (with_ledger L) (sg_outs SD)) (sg_hi SD))) with (reledger_lc L (Some (SC (sg_outs SD) (sg_hi SD)))).
  apply (check_reledger SEGS IT A nx0 LIMIT (fun _ => None) XN XE XB KC xp sysws_reL xnws_reL xews_reL xws_reL HXN HXE
           (sg_bfuel SD) (sg_fuel SD) (Some (SC (sg_outs SD) (sg_hi SD))) (sg_body SD) (sg_in SD) s L (sg_hi SD));
    [reflexivity | exact He | exact HL | exact HC | exact Hlen | cbn; lia | exact Hc].
Qed.
Lemma list_eqb_refl' : forall {T} (eqb : T -> T -> bool) l, (forall x, eqb x x = true) -> list_eqb eqb l l = true.
Proof. intros T eqb l H. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite H, IH. reflexivity. Qed.
Lemma pair_eqb_refl' : forall p, pair_eqb p p = true.
Proof. intros [a b]. unfold pair_eqb. cbn. rewrite !expr_eqb_refl'. reflexivity. Qed.
Lemma maps_vars_lt_mono : forall b b' ms, maps_vars_lt b ms = true -> (b <= b')%nat -> maps_vars_lt b' ms = true.
Proof.
  intros b b' ms H Hle. unfold maps_vars_lt in *. apply forallb_forall. intros m Hm.
  pose proof (proj1 (forallb_forall _ _) H m Hm) as Q. apply andb_prop in Q as [Q1 Q2].
  rewrite (expr_vars_lt_mono _ _ _ Q1 Hle), (expr_vars_lt_mono _ _ _ Q2 Hle). reflexivity.
Qed.
Lemma pairs_vars_lt_mono : forall b b' ps, pairs_vars_lt b ps = true -> (b <= b')%nat -> pairs_vars_lt b' ps = true.
Proof.
  intros b b' ps H Hle. unfold pairs_vars_lt in *. apply forallb_forall. intros q Hq.
  pose proof (proj1 (forallb_forall _ _) H q Hq) as Q. apply andb_prop in Q as [Q1 Q2].
  rewrite (expr_vars_lt_mono _ _ _ Q1 Hle), (expr_vars_lt_mono _ _ _ Q2 Hle). reflexivity.
Qed.
Lemma ledger_vars_lt_mono : forall b b' L, ledger_vars_lt b L = true -> (b <= b')%nat -> ledger_vars_lt b' L = true.
Proof.
  intros b b' L H Hle. unfold ledger_vars_lt in *. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  rewrite (maps_vars_lt_mono _ _ _ H1 Hle), (pairs_vars_lt_mono _ _ _ H2 Hle), (pairs_vars_lt_mono _ _ _ H3 Hle). reflexivity.
Qed.
Lemma fresh_ok_with_ledger : forall x L, fresh_ok nx0 x = true -> ledger_vars_lt (nxt x) L = true -> fresh_ok nx0 (with_ledger L x) = true.
Proof.
  intros x L H HL. pose proof (fresh_ok_parts nx0 x H) as (F1 & F2 & _ & _ & F5 & F6 & F7).
  unfold ledger_vars_lt in HL. apply andb_prop in HL as [HL HL3]. apply andb_prop in HL as [HL1 HL2].
  unfold fresh_ok. cbn [a_ss a_maps a_vis a_ghost a_brk a_fd with_ledger].
  change (nxt (with_ledger L x)) with (nxt x). change (kn (with_ledger L x)) with (kn x).
  rewrite F1, F2, HL1, HL2, HL3, F5, F6. cbn [andb]. apply Nat.leb_le. exact F7.
Qed.
Lemma template_ok_with_ledger : forall lo x L, template_ok nx0 lo x = true -> ledger_vars_lt (nxt x) L = true ->
  template_ok nx0 lo (with_ledger L x) = true.
Proof.
  intros lo x L H HL. unfold template_ok in *. repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  change (a_ss (with_ledger L x)) with (a_ss x). change (nxt (with_ledger L x)) with (nxt x).
  rewrite (fresh_ok_with_ledger x L H HL), X1, X0, X. destruct (s_log (a_ss x)); [|discriminate X2]. reflexivity.
Qed.
Lemma acs_frame_eqb_with_ledger : forall x y L, AP.acs_frame_eqb x y = true -> AP.acs_frame_eqb (with_ledger L x) (with_ledger L y) = true.
Proof.
  intros x y L H. unfold AP.acs_frame_eqb in *. repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  cbn [a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset with_ledger].
  rewrite (list_eqb_refl' amap_eqb _ amap_eqb_refl'), !(list_eqb_refl' pair_eqb _ pair_eqb_refl'), !Z.eqb_refl, X1, X0, X. reflexivity.
Qed.
Lemma segdef_wf_reledger : forall SD L, AP.segdef_wf nx0 SD = true -> ledger_vars_lt (sg_hi SD) L = true ->
  AP.segdef_wf nx0 (AP.reledger_sd L SD) = true.
Proof.
  intros SD L H HL. pose proof (segdef_wf_facts nx0 SD H) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9).
  unfold AP.segdef_wf. cbn [AP.reledger_sd sg_lo sg_hi sg_in sg_outs sg_w sg_shape].
  change (nxt (with_ledger L (sg_in SD))) with (nxt (sg_in SD)). change (a_props (with_ledger L (sg_in SD))) with (a_props (sg_in SD)).
  rewrite W3, Nat.eqb_refl, W6, W7, W8, W9. rewrite (proj2 (Nat.leb_le _ _) W1), (proj2 (Nat.leb_le _ _) W2).
  rewrite (template_ok_with_ledger _ _ _ W4 ltac:(rewrite W3; exact HL)). cbn [andb].
  rewrite !Bool.andb_true_r. apply forallb_forall. intros x' Hx'. apply in_map_iff in Hx' as (x & <- & Hx).
  apply In_nth_error in Hx as [i Hi]. destruct (W5 i x Hi) as [T1 T2].
  rewrite (template_ok_with_ledger _ _ _ T1), (acs_frame_eqb_with_ledger _ _ _ T2); [reflexivity|].
  unfold template_ok in T1. repeat match type of T1 with (_ && _)%bool = true => apply andb_prop in T1 as [T1 ?Y] end.
  apply Nat.leb_le in Y. exact (ledger_vars_lt_mono _ _ _ HL Y).
Qed.

(* [comment removed for export] *)
Lemma seg_sem_of_check : forall sid SD,
  (forall sid' SD0 cs SD' skh, (sid' < sid)%nat -> xp_sg xp0 sid' = Some SD0 -> AP.use_view cs SD0 = Some (SD', skh) ->
      SEGSEM SD' /\ (AP.segdef_wf nx0 SD0 = true -> AP.segdef_wf nx0 SD' = true)) ->   (* [comment removed for export] *)
  AP.segdef_wf nx0 SD = true ->
  AP.check SEGS IT A nx0 LIMIT XN XE XB (fun _ => None) KC (xp_seg xp0 (sg_w SD) (sg_hi SD) sid) (sg_bfuel SD) (sg_fuel SD)
           (Some (SC (sg_outs SD) (sg_hi SD))) (sg_in SD) (sg_body SD) = COk (sg_shape SD) ->
  SEGSEM SD.
Proof.
  intros sid SD Hbelow Hwf Hc K K_agree K_nil fy E R FULL model Hz HC Hexits.
  set (xp := xp_seg xp0 (sg_w SD) (sg_hi SD) sid) in Hc.
  unfold AP.segdef_wf in Hwf.
  repeat match type of Hwf with (_ && _)%bool = true => apply andb_prop in Hwf as [Hwf ?X] end.
  apply Nat.leb_le in Hwf.
  match goal with Hl : Nat.leb (sg_lo SD) (sg_hi SD) = true |- _ => apply Nat.leb_le in Hl; rename Hl into Hlohi end.
  match goal with Hl : AP.wvars_lt (sg_hi SD) (sg_w SD) = true |- _ => rename Hl into HWv end.
  match goal with Hl : forallb _ (sg_outs SD) = true |- _ => rename Hl into Houts end.
  match goal with Hl : match a_props (sg_in SD) with _ => _ end = true |- _ => rename Hl into Hprops end.
  assert (HP0 : forall E0 M0, props_ok GPs E0 M0 (a_props (sg_in SD)))
    by (intros E0 M0; unfold props_ok; destruct (a_props (sg_in SD)); [constructor | discriminate Hprops]).
  assert (HSS : forall sid' SD0 cs SD' skh, xp_sg xp sid' = Some SD0 -> AP.use_view cs SD0 = Some (SD', skh) ->
            SEGSEM SD' /\ (AP.segdef_wf nx0 SD0 = true -> AP.segdef_wf nx0 SD' = true)).
  { intros sid' SD0 cs0 SD' skh Hn Huv. cbn [xp xp_seg xp_sg] in Hn. destruct (Nat.ltb_spec sid' sid); [exact (Hbelow sid' SD0 cs0 SD' skh ltac:(lia) Hn Huv) | discriminate Hn]. }
  assert (HSnone : forall (fy0 : FPState), frm_zero (@fp_csr fy0) -> holes_stmt SEGS A LIMIT (fun _ => None) SINV argH K FS0 GPs (fx:=fy0))
    by (intros fy0 _ h ch Hh; discriminate Hh).
  assert (HextF : forall (fy0 : FPState) id, xp_extF xp id = true -> ext_stmtF SEGS A nx0 LIMIT XN SINV argH FS0 (fx:=fy0) id)
    by (intros fy0 id Hid; apply node_extF_sound; exact Hid).
  pose proof (check_sound SEGS IT IT_ok A nx0 NX0_min LIMIT (fun _ => None) XN XE XB SEGS_wx SEGS_in_hull HULL_ok SHADOW_ok
                SINV argH argH_high argH_agree SINV_frame SINV_agree K K_agree K_nil FS0 KC xp GPs
                (fun Hhq : xp_hq xp = true => ltac:(discriminate Hhq))
                node_sys_sound node_brk2_sound node_mmap_sound node_mmapin_sound node_mprotect_sound node_exit_sound
                node_x_sound node_join_sound (fun fy id _ => node_ext_sound fy id) node_emit_sound node_ext2_sound HSnone HextF
                node_sysW_sound node_extW_sound node_emitW_sound node_xW_sound
                GPs_frame Gs_ok (fun fy0 id (Hid : xp_extG xp id = true) => ltac:(discriminate Hid)) HSS
                (sg_fuel SD) (sg_bfuel SD) (Some (SC (sg_outs SD) (sg_hi SD))) (sg_body SD) (sg_in SD) (sg_shape SD) Hc
                fy E R FULL model t_nil E FULL model Hz HC (HP0 _ _)) as CS.
  rewrite (sd_sdK K) in CS. apply CS; [| |reflexivity].
  - (* [comment removed for export] *) unfold WI. cbn [xp_wb xp]. split; [apply env_agree_refl|]. split; [intros; reflexivity | apply mvis_refl].
  - (* [comment removed for export] *)
    split.
    + unfold WBOK. cbn [xp_wb xp lc_lo]. split; [exact HWv | lia].
    + cbn [LCOK]. split; [lia|]. intros i x Hi.
      pose proof (proj1 (forallb_forall _ _) Houts x (nth_error_In _ _ Hi)) as Hx. apply andb_prop in Hx as [Htx _].
      destruct (template_ok_facts nx0 (sg_hi SD) x Htx) as (Xfr & Xlog & Xlen & Xlo).
      split; [exact Xlo|]. split; [exact Xlog|]. split; [exact Xlen|].
      intros fy' E' R' F' m' Hz' Hag HC' HW' Hfs. unfold WI in HW'. cbn [xp_wb xp] in HW'. destruct HW' as (_ & HM & Hmv).
      apply (Hexits i x fy' E' R' F' m' Hi Hz' Hag HC'); [exact Hfs | exact HM | exact Hmv].
Qed.

(* [comment removed for export] *)
Theorem seg_ok_sound : forall sid SD,
  (forall sid' SD0 cs SD' skh, (sid' < sid)%nat -> xp_sg xp0 sid' = Some SD0 -> AP.use_view cs SD0 = Some (SD', skh) ->
      SEGSEM SD' /\ (AP.segdef_wf nx0 SD0 = true -> AP.segdef_wf nx0 SD' = true)) ->
  AP.seg_ok SEGS IT A nx0 LIMIT XN XE XB KC xp0 sid SD = true ->
  forall cs SD' skh, AP.use_view cs SD = Some (SD', skh) ->
    SEGSEM SD' /\ (AP.segdef_wf nx0 SD = true -> AP.segdef_wf nx0 SD' = true).
Proof.
  intros sid SD Hbelow Hok cs SD' skh Huv.
  unfold AP.seg_ok in Hok. apply andb_prop in Hok as [Hwf Hchk].
  destruct (AP.check SEGS IT A nx0 LIMIT XN XE XB (fun _ => None) KC (xp_seg xp0 (sg_w SD) (sg_hi SD) sid) (sg_bfuel SD) (sg_fuel SD)
              (Some (SC (sg_outs SD) (sg_hi SD))) (sg_in SD) (sg_body SD)) as [s| |] eqn:Hc; [|discriminate|discriminate].
  apply shape_eqb_eq in Hchk. subst s.
  unfold AP.use_view in Huv. destruct (AP.skel_free SD) eqn:Hsf.
  - destruct (AP.reskel (sg_lo SD) (sg_hi SD) (ledger_of (sg_in SD)) (ledger_of cs)) as [[L sk]|] eqn:Hrs; [|discriminate Huv].
    injection Huv as <- <-.
    destruct (APL.reskel_shape _ _ _ _ _ _ Hrs) as (HLe & HLv & N1 & N2 & N3 & M1 & M2 & M3).
    assert (HLl : lens_le L (ledger_of (sg_in SD))) by (unfold lens_le; rewrite N1, N2, N3; repeat split; assumption).
    pose proof (segdef_wf_reledger SD L Hwf HLv) as Hwf'.
    split; [|intros _; exact Hwf'].
    apply (seg_sem_of_check sid (AP.reledger_sd L SD) Hbelow Hwf').
    cbn [AP.reledger_sd sg_w sg_hi sg_bfuel sg_fuel sg_outs sg_in sg_body sg_shape].
    exact (check_reledger_seg sid SD L (sg_shape SD) Hwf HLv HLe HLl Hc).
  - injection Huv as <- <-. split; [exact (seg_sem_of_check sid SD Hbelow Hwf Hc) | intros _; exact Hwf].
Qed.

(* [comment removed for export] *)
Theorem segs_ok_sound :
  (forall sid SD, xp_sg xp0 sid = Some SD -> AP.seg_ok SEGS IT A nx0 LIMIT XN XE XB KC xp0 sid SD = true) ->
  forall sid SD0 cs SD skh, xp_sg xp0 sid = Some SD0 -> AP.use_view cs SD0 = Some (SD, skh) ->
    SEGSEM SD /\ (AP.segdef_wf nx0 SD0 = true -> AP.segdef_wf nx0 SD = true).
Proof.
  intros Hall sid. induction sid as [sid IH] using (well_founded_induction Wf_nat.lt_wf).
  intros SD0 cs SD skh Hsd Huv. apply (seg_ok_sound sid SD0) with (cs := cs) (skh := skh); [| exact (Hall sid SD0 Hsd) | exact Huv].
  intros sid' SD1 cs' SD1' skh' Hlt Hsd' Huv'. exact (IH sid' Hlt SD1 cs' SD1' skh' Hsd' Huv').
Qed.

(* [comment removed for export] *)
Lemma extF_none_sound : forall (fy : FPState) id, xp_extF XP0 id = true -> ext_stmtF SEGS A nx0 LIMIT XN SINV argH FS0 (fx:=fy) id.
Proof. intros fy id H. discriminate H. Qed.
Lemma segs_none_sound : forall sid SD0 cs SD skh, xp_sg XP0 sid = Some SD0 -> AP.use_view cs SD0 = Some (SD, skh) ->
  SEGSEM SD /\ (AP.segdef_wf nx0 SD0 = true -> AP.segdef_wf nx0 SD = true).
Proof. intros sid SD0 cs SD skh H. discriminate H. Qed.
Lemma sysW_none_sound : forall (fy : FPState) y cs ws, xp_sysws XP0 y cs = Some ws ->
  node1_stmtW_at SEGS A nx0 LIMIT SINV argH FS0 (fx:=fy) (is_ecall_at SEGS) (node_sys A nx0 y) cs ws.
Proof. intros fy y cs ws H. discriminate H. Qed.
Lemma extW_none_sound : forall (fy : FPState) id args cs ws, xp_xnws XP0 id args cs = Some ws ->
  node1_stmtW_at SEGS A nx0 LIMIT SINV argH FS0 (fx:=fy) always (XN id args) cs ws.
Proof. intros fy id args cs ws H. discriminate H. Qed.
Lemma emitW_none_sound : forall (fy : FPState) id args cs ws, xp_xews XP0 id args cs = Some ws ->
  emit_stmtW_at SEGS A nx0 LIMIT XE SINV argH FS0 (fx:=fy) id args cs ws.
Proof. intros fy id args cs ws H. discriminate H. Qed.
Lemma xW_none_sound : forall (fy : FPState) x args cs ws, xp_xws XP0 x args cs = Some ws ->
  node1_stmtW_at SEGS A nx0 LIMIT SINV argH FS0 (fx:=fy) always (node_x SEGS A nx0 x args) cs ws.
Proof. intros fy x args cs ws H. discriminate H. Qed.
(* [comment removed for export] *)
Lemma extF_none_sound' : forall (fy : FPState) (id : nat), false = true -> ext_stmtF SEGS A nx0 LIMIT XN SINV argH FS0 (fx:=fy) id.
Proof. intros fy id H. discriminate H. Qed.
Lemma segs_none_sound' : forall (sid : nat) SD0 (cs : acs) SD (skh : sbind), (None : option segdef) = Some SD0 -> AP.use_view cs SD0 = Some (SD, skh) ->
  SEGSEM SD /\ (AP.segdef_wf nx0 SD0 = true -> AP.segdef_wf nx0 SD = true).
Proof. intros sid SD0 cs SD skh H. discriminate H. Qed.
Lemma sysW_none_sound' : forall (fy : FPState) (y : snode) (cs : acs) ws, (None : option (list (saddr * expr))) = Some ws ->
  node1_stmtW_at SEGS A nx0 LIMIT SINV argH FS0 (fx:=fy) (is_ecall_at SEGS) (node_sys A nx0 y) cs ws.
Proof. intros fy y cs ws H. discriminate H. Qed.
Lemma extW_none_sound' : forall (fy : FPState) (id : nat) (args : list expr) (cs : acs) ws, (None : option (list (saddr * expr))) = Some ws ->
  node1_stmtW_at SEGS A nx0 LIMIT SINV argH FS0 (fx:=fy) always (XN id args) cs ws.
Proof. intros fy id args cs ws H. discriminate H. Qed.
Lemma emitW_none_sound' : forall (fy : FPState) (id : nat) (args : list expr) (cs : acs) ws, (None : option (list (saddr * expr))) = Some ws ->
  emit_stmtW_at SEGS A nx0 LIMIT XE SINV argH FS0 (fx:=fy) id args cs ws.
Proof. intros fy id args cs ws H. discriminate H. Qed.
Lemma xW_none_sound' : forall (fy : FPState) (x : xnode) (args : list expr) (cs : acs) ws, (None : option (list (saddr * expr))) = Some ws ->
  node1_stmtW_at SEGS A nx0 LIMIT SINV argH FS0 (fx:=fy) always (node_x SEGS A nx0 x args) cs ws.
Proof. intros fy x args cs ws H. discriminate H. Qed.
(* [comment removed for export] *)
Lemma extG_none_sound : forall (GP : nat -> list Z -> (word -> option byte) -> Prop) (fy : FPState) id,
  xp_extG XP0 id = true -> ext_stmtG SEGS A nx0 LIMIT XN SINV argH FS0 GP (fy:=fy) id.
Proof. intros GP fy id H. discriminate H. Qed.
Lemma extG_noneG_sound : forall G (GP : nat -> list Z -> (word -> option byte) -> Prop) (fy : FPState) id,
  xp_extG (XPG G) id = true -> ext_stmtG SEGS A nx0 LIMIT XN SINV argH FS0 GP (fy:=fy) id.
Proof. intros G GP fy id H. discriminate H. Qed.
End SegSound.
End APS.
