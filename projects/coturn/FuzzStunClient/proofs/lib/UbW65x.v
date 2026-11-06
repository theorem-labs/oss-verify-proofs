(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Amb.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg Nodes MmapSim AllocSim FileSim AgentLib SymExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Spec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LibWritev RefNodes.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbExitBase UbExit.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib RefLayout.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbStartup UbMainEntry.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import MallocDefs.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbEnframeBase UbEnframe UbReadBase UbWorld UbTargetPre.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbPilotOOM_defs UbPilotOOM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymXfer SymAbove UbW65_defs UbW65 UbW65m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.peel ::= peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_nobignat.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition off_image (x : Z) : Prop := (x + 1 <= 0x10000 \/ 0x58000 <= x)%Z.

Lemma find_segment_skip : forall seg rest a n,
  (0 < n)%Z ->
  (a < Z.of_N (seg_base seg) \/ Z.of_N (seg_base seg) + Z.of_N (seg_size seg) < a + n)%Z ->
  find_segment (seg :: rest) a n = find_segment rest a n.
Proof.
  intros seg rest a n Hn H. cbn [find_segment].
  destruct (Z.leb_spec (Z.of_N (seg_base seg)) a); destruct (Z.leb_spec (a + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)));
    cbn [andb]; try reflexivity. lia.
Qed.

Lemma find_segment_off : forall a n, (0 < n)%Z -> (a + n <= 0x10000 \/ 0x58000 <= a)%Z ->
  find_segment RSEGS a n = None.
Proof.
  intros a n Hn H. unfold Ubsan.M.loaded_segments, Ubsan_loaded_segments.
  rewrite 4 find_segment_skip; [reflexivity | exact Hn | | exact Hn | | exact Hn | | exact Hn |];
    cbn [seg_base seg_size Ubsan_segment_000 Ubsan_segment_001 Ubsan_segment_002 Ubsan_segment_003]; lia.
Qed.

Lemma seg_rom_off : forall x : word, off_image (bv_unsigned x) -> seg_rom RSEGS x = None.
Proof.
  intros x Hx. unfold seg_rom, memory_read. rewrite find_segment_off; [reflexivity | cbn; lia | unfold off_image in Hx; cbn; lia].
Qed.

Lemma wview_off : forall M (x : word), off_image (bv_unsigned x) -> wview RSEGS M x = M x.
Proof.
  intros M x Hx. unfold wview. destruct (M x); [reflexivity|].
  rewrite find_segment_off; [reflexivity | lia | unfold off_image in Hx; lia].
Qed.

Lemma rdn1_off : forall M (x : word) b, off_image (bv_unsigned x) ->
  rdn RSEGS M x 1 = Some [b] -> M x = Some b.
Proof.
  intros M x b Hx H. cbn [rdn] in H. rewrite (seg_rom_off x Hx) in H.
  destruct (M x) as [b0|]; [|discriminate]. injection H as ->. reflexivity.
Qed.

Lemma store_ok1_off : forall M (x : word), off_image (bv_unsigned x) ->
  store_ok RSEGS M x 1 = true -> M x <> None.
Proof.
  intros M x Hx H. cbn [store_ok] in H. rewrite (wview_off M x Hx) in H.
  destruct (M x); [discriminate | discriminate].
Qed.

Lemma u64_lit' : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

Lemma u0 : bv_unsigned (Z_to_bv 64 0) = 0%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cell_intro : forall M (x : word) n (v : word) (a z : Z),
  rdn RSEGS M x n = Some (word_to_le_bytes n v) ->
  x = Z_to_bv 64 a -> v = Z_to_bv 64 z -> cell M a n z.
Proof. intros M x n v a z H -> ->. exact H. Qed.

Lemma zero_bytes_intro : forall E M b k n a,
  kentry_ok RSEGS E M (KZero (SA b k) (ELit n)) -> (0 <= n < 2 ^ 64)%Z ->
  (bv_unsigned (edenot E b) + k)%Z = a -> zero_bytes M a n.
Proof.
  intros E M b k n a [Hf Hz] Hn Ha i Hi. unfold estart, elenZ in Hz. cbn [a_base a_off edenot] in Hz.
  rewrite u64_lit' in Hz by lia. rewrite <- Ha. apply Hz. lia.
Qed.

Lemma def_intro : forall E M b kk len a n,
  kentry_ok RSEGS E M (KWr (SA b kk) len) ->
  (bv_unsigned (edenot E b) + kk <= a)%Z -> (a + n <= bv_unsigned (edenot E b) + kk + len)%Z ->
  (a + n <= 0x10000 \/ 0x58000 <= a)%Z -> (0 <= a)%Z -> (a + n <= 2 ^ 64)%Z ->
  forall i, (0 <= i < n)%Z -> M (Z_to_bv 64 (a + i)) <> None.
Proof.
  intros E M b kk len a n [Hf Hst] H1 H2 Hoff H0 H64 i Hi.
  unfold estart in Hst. cbn [a_base a_off] in Hst.
  specialize (Hst (a + i - (bv_unsigned (edenot E b) + kk))%Z 1%nat ltac:(lia) ltac:(cbn; lia)).
  replace (bv_unsigned (edenot E b) + kk + (a + i - (bv_unsigned (edenot E b) + kk)))%Z with (a + i)%Z in Hst by lia.
  refine (store_ok1_off M _ _ Hst). unfold off_image; rewrite u64_lit' by lia; lia.
Qed.

Lemma byte_intro : forall M a v,
  cell M a 1 v -> word_to_le_bytes 1 (Z_to_bv 64 v) = [Z_to_bv 8 v] ->
  (0 <= a)%Z -> (a + 1 <= 2 ^ 64)%Z -> (a + 1 <= 0x10000 \/ 0x58000 <= a)%Z ->
  M (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Proof.
  intros M a v Hc Hw H0 H64 Hoff. unfold cell in Hc. rewrite Hw in Hc.
  apply rdn1_off; [unfold off_image; rewrite u64_lit' by lia; lia | exact Hc].
Qed.

Lemma img_clear_of_know : forall E M ivs,
  know_ok RSEGS E M (map (fun iv => KImg (fst iv) (snd iv)) ivs) ->
  Forall (fun iv => img_clear M (fst iv) (snd iv)) ivs.
Proof.
  intros E M ivs HK. unfold know_ok in HK. rewrite Forall_map in HK.
  eapply Forall_impl; [|exact HK]. intros [lo hi] (A & B & C). exact C.
Qed.

(* [comment removed for export] *)
Lemma errno_some : forall M, exists bs,
  rdn RSEGS M (Z_to_bv 64 0x36bbc) 4 = Some bs /\ length bs = 4%nat.
Proof.
  intros M. cbn [rdn].
  repeat match goal with
  | |- context [match M ?x with _ => _ end] =>
      destruct (M x); [| let r := eval vm_compute in (seg_rom RSEGS x) in change (seg_rom RSEGS x) with r]
  end; eexists; split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac addr_split a :=
  lazymatch a with
  | bv_unsigned ?x =>
      lazymatch x with
      | vals_ev _ ?i => constr:((EVar i, 0%Z))
      | _ => lazymatch goal with P : vals_ev _ ?i = x |- _ => constr:((EVar i, 0%Z)) end
      end
  | (?y + ?c)%Z =>
      lazymatch y with
      | context [bv_unsigned _] =>
          lazymatch addr_split y with (?b, ?k) => let k' := eval vm_compute in (k + c)%Z in constr:((b, k')) end
      | _ => let a' := eval vm_compute in a in constr:((ELit 0, a'))
      end
  | (?y - ?c)%Z =>
      lazymatch y with
      | context [bv_unsigned _] =>
          lazymatch addr_split y with (?b, ?k) => let k' := eval vm_compute in (k - c)%Z in constr:((b, k')) end
      | _ => let a' := eval vm_compute in a in constr:((ELit 0, a'))
      end
  | _ => let a' := eval vm_compute in a in constr:((ELit 0, a'))
  end.

(* [comment removed for export] *)
Ltac kside :=
  rewrite ?edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV ENVr gx bx ax]; rewrite ?u0; pins;
  rewrite ?ext_val_zx_id by (cbn; lia);
  first [ reflexivity
        | symmetry; apply Z_to_bv_bv_unsigned
        | rewrite Z_to_bv_bv_unsigned; (reflexivity || assumption || (symmetry; assumption))
        | f_equal; lia
        | lia ].

(* [comment removed for export] *)
Ltac kcell HK :=
  lazymatch goal with |- cell ?M ?a ?n ?z =>
  lazymatch type of HK with know_ok ?segs ?E M ?kn =>
  lazymatch addr_split a with (?b, ?k) =>
    let r := eval vm_compute in (kread segs kn b k n) in
    lazymatch r with
    | Some ?v =>
        apply (cell_intro M (adenot E (SA b k)) n (edenot E v) a z);
        [ apply (kread_rdn segs E M kn b k n v HK); [vm_compute; reflexivity | cbn; lia | cbn; lia
          | apply flat_intro; cbn [edenot ev ENV ENVr gx bx ax]; rewrite ?u0; pins; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ]
        | kside
        | kside ]
    | None => fail "kcell: knowledge does not determine" b k n
    end end end end.

(* [comment removed for export] *)
Ltac krdn HK :=
  lazymatch goal with |- rdn _ ?M (Z_to_bv 64 ?a) ?n = Some (word_to_le_bytes _ (Z_to_bv 64 ?z)) =>
    change (cell M a n z); kcell HK end.

(* [comment removed for export] *)
Ltac kzero HK :=
  lazymatch goal with |- zero_bytes ?M ?a ?n =>
  lazymatch type of HK with know_ok ?segs ?E M ?kn =>
  lazymatch addr_split a with (?b, ?k) =>
    let n' := eval vm_compute in n in
    apply (zero_bytes_intro E M b k n' a);
    [ apply (kderive_sound segs E M kn (KZero (SA b k) (ELit n')) HK); vm_compute; reflexivity
    | lia
    | cbn [edenot ev ENV ENVr gx bx ax]; rewrite ?u0; pins; lia ]
  end end end.

(* [comment removed for export] *)
Ltac kbyte HK :=
  lazymatch goal with |- ?M (Z_to_bv 64 ?a) = Some (Z_to_bv 8 ?v) =>
    apply (byte_intro M a v); [kcell HK | reflexivity | pins; lia | pins; lia | pins; lia] end.

(* [comment removed for export] *)
Ltac kdef HK b kk len :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
    apply (def_intro E M b kk len);
    [ apply (kderive_sound segs E M kn (KWr (SA b kk) len) HK); vm_compute; reflexivity
    | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia
    | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia
    | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia
    | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia
    | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia ]
  end.

(* [comment removed for export] *)
Lemma cell_join : forall M a n1 n2 v1 v2 v,
  cell M a n1 v1 -> cell M (a + Z.of_nat n1) n2 v2 ->
  word_to_le_bytes n1 (Z_to_bv 64 v1) ++ word_to_le_bytes n2 (Z_to_bv 64 v2) = word_to_le_bytes (n1 + n2) (Z_to_bv 64 v) ->
  (0 <= a)%Z -> (a + Z.of_nat n1 < 2 ^ 64)%Z -> cell M a (n1 + n2) v.
Proof.
  unfold cell. intros M a n1 n2 v1 v2 v H1 H2 Hw Ha Hn. rewrite <- Hw.
  apply rdn_app; [exact H1|]. rewrite w_add_nat, u_small by lia. exact H2.
Qed.

(* [comment removed for export] *)
Lemma kwr_window : forall E M kn b kk len base,
  know_ok RSEGS E M kn -> kderive RSEGS kn (KWr (SA b kk) len) = true ->
  (bv_unsigned (edenot E b) + kk)%Z = base ->
  forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= len)%Z -> store_ok RSEGS M (Z_to_bv 64 (base + d)) m = true.
Proof.
  intros E M kn b kk len base HK Hd Hb d m H0 Hm.
  destruct (kderive_sound RSEGS E M kn _ HK Hd) as [Hf Hst]. unfold estart in Hst. cbn [a_base a_off] in Hst.
  rewrite Hb in Hst. apply Hst; assumption.
Qed.

(* [comment removed for export] *)
Definition fG (i : nat) : nat := if Nat.eqb i 2 then 70%nat else if Nat.eqb i 3 then 72%nat else i.
Definition fT {AMB : Amb} (i : nat) : nat := if Nat.eqb i 2 then 71%nat else if Nat.eqb i 3 then 72%nat else i.

(* [comment removed for export] *)
Ltac kreg HR :=
  lazymatch goal with |- getr ?R ?r = _ =>
  lazymatch type of HR with regs_ok ?E ?sr R =>
    let e := eval vm_compute in (sr_get sr r) in
    rewrite (reg_val E sr R r HR); change (sr_get sr r) with e; kside
  end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section World.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable fdata : list byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv rdraw tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpnd : path <> dot_path.
  Hypothesis Hplen : (length path <= 4095)%nat.
  Variable fd3 : FdEntry.      (* [comment removed for export] *)
  Variable SI : (word -> option byte) -> Prop.   (* [comment removed for export] *)
  Hypothesis SI_step : forall M M' : word -> option byte,
    (forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M' a = M a) -> SI M -> SI M'.

  #[local] Notation ENVv := (ENV a0s path).
  #[local] Notation modelV := (modelV tid fs0 stdin0 fd3).

  (* [comment removed for export] *)
  Definition vm_small (VM : VmMaps) (gm : word) : Prop :=
    vm_reserved VM = segments_reserved RSEGS /\ vm_limit VM = LIM
    /\ (length (vm_maps VM) <= 4)%nat
    /\ In (gm, Z_to_bv 64 69632) (vm_maps VM)
    /\ Forall (fun p => (0 < bv_unsigned (snd p) <= 69632)%Z /\ (bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64)%Z) (vm_maps VM)
    /\ seps (vm_maps VM).

  (* [comment removed for export] *)
  Definition after_malloc (K : TSet) : Prop :=
    forall (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (mb gm sec cn : word) (area brkv mas : Z),
      area = (bv_unsigned mb + 4096)%Z ->
      read_pre sp0 (p1 sp0 a0s path envv) mb gm sec cn R M ->
      world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) M ->
      main_frame (bv_unsigned sp0) M ->
      vm_pre VM sp0 mb gm -> vm_small VM gm ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13b14) M (seg_rom RSEGS))
                              (model_pre path VM stdin0 fs0 tid)) K.

  (* [comment removed for export] *)
  Definition after_malloc_gen (K : TSet) : Prop :=
    forall (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (mb gm sec cn : word) (area brkv mas : Z),
      area = (bv_unsigned mb + 4096)%Z ->
      read_pre sp0 (p1 sp0 a0s path envv) mb gm sec cn R M ->
      world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) M ->
      main_frame (bv_unsigned sp0) M ->
      vm_pre VM sp0 mb gm -> vm_small VM gm -> SI M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13b14) M (seg_rom RSEGS))
                              (mkModelC (fdsV fd3) VM stdin0 fs0 None (Some tid) None)) K.

  Lemma modelV_eq : forall VM, modelV VM = mkModelC (fdsV fd3) VM stdin0 fs0 None (Some tid) None.
  Proof using Type. intros VM. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma p1_range : (0x7fff80000000 <= bv_unsigned (p1 sp0 a0s path envv) <= 0x800000400000)%Z.
  Proof using AMB rdraw Hva Hve Hvsp Hplen.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. unfold sp_window_lo, sp_window_hi in *.
    unfold p1. rewrite (u_cat_argv_ptr Ubsan.M.phdrs sp0 rdraw [a0s; path] envv a_uid a_hwcap Hva Hve) by (cbn; lia || (unfold sp_window_lo, sp_window_hi; cbn; lia)).
    pose proof (struct_av_bound Ubsan.M.phdrs sp0 rdraw [a0s; path] envv a_uid a_hwcap Hva Hve).
    pose proof (CatExec.total_arg_bytes_firstn_le 1 [a0s; path]). lia.
  Qed.

  Variable K : TSet.

  Lemma w65_exitG : after_malloc_gen K -> exitG_branch sp0 a0s path envv tid brk fs0 stdin0 fd3 SI K.
  Proof using rdraw Hva Hve Hvsp Htid Hbrk Hplen.
    intros AM vals R M VM HL P0 P2 P70 P5 HR HK HVM HVS HSI.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    pose proof (know_nth RSEGS _ _ knZ ltac:(let i := kidx knZ (is_krange gx) in exact i) _ HK eq_refl)
      as Kgm; cbn [kentry_ok edenot ev ENV ENVr gx bx ax] in Kgm.
    pose proof (know_nth RSEGS _ _ knZ ltac:(let i := kidx knZ (is_kalign gx) in exact i) _ HK eq_refl)
      as Kga; cbn [kentry_ok edenot ev ENV ENVr gx bx ax] in Kga.
    pose proof (know_nth RSEGS _ _ knZ ltac:(let i := kidx knZ (is_kdisj bx gx) in exact i) _ HK eq_refl)
      as Kgd; cbn [kentry_ok] in Kgd; unfold estart in Kgd; cbn [a_base a_off edenot ev ENV ENVr gx bx ax] in Kgd; rewrite P70 in Kgd.
    pose proof (know_nth RSEGS _ _ knZ ltac:(let i := kidx knZ (is_kdisj (EVar 0) gx) in exact i) _ HK eq_refl)
      as Kgw; cbn [kentry_ok] in Kgw; unfold estart in Kgw; cbn [a_base a_off edenot ev ENV ENVr gx bx ax] in Kgw; rewrite P0 in Kgw.
    pose proof p1_range as P1r.
    pose proof (u64_range brk) as Bu. pose proof (u64_range sp0) as Su.
    rewrite modelV_eq.
    apply (AM R M VM brk (vals_ev vals 72) (vals_ev vals 7) (vals_ev vals 4) (bv_unsigned brk + 4096)%Z (bv_unsigned brk + 8192)%Z 0%Z).
    - reflexivity.
    - (* [comment removed for export] *)
      constructor.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + lia.
      + exact P1r.
      + lia.
      + lia.
      + lia.
      + lia.
      + unfold stack_writable. apply (kwr_window (ENVv vals) M knZ (EVar 0) (-8388608) 8388608); [exact HK | vm_compute; reflexivity | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia].
      + unfold group_writable. apply (kwr_window (ENVv vals) M knZ gx 0 69632); [exact HK | vm_compute; reflexivity | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia].
      + unfold meta_writable. apply (kwr_window (ENVv vals) M knZ bx 4096 4096); [exact HK | vm_compute; reflexivity | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia].
      + destruct (errno_some M) as (bs & Hbs & Hlen). exists (Z_to_bv 64 (bytes_le_to_Z bs)).
        rewrite Hbs, word_to_le_bytes_of_lez by (assumption || lia). reflexivity.
      + intros x0 x1 x5 x6 extra ebs.
        apply (know_ok_ren RSEGS (ENVv vals) _ M fG [2;3;4;7]%nat kn_M1).
        * intros i Hi. destruct Hi as [<-|[<-|[<-|[<-|[]]]]]; cbn [ev ENV fG Nat.eqb vals_ev nth app]; pins; reflexivity.
        * vm_compute. reflexivity.
        * apply (kderive_all_sound RSEGS _ M knZ); [exact HK | vm_compute; reflexivity].
    - (* [comment removed for export] *)
      constructor.
      all: try kcell HK.
      all: try kzero HK.
      + exists (bv_unsigned (vals_ev vals 7)). split; [apply u64_range|]. split; kcell HK.
      + apply (cell_join M _ 4 4 101 0); [kcell HK | kcell HK | reflexivity | lia | lia].
      + apply (cell_join M _ 4 4 0 0); [kcell HK | kcell HK | reflexivity | lia | lia].
      + kdef HK bx 4096%Z 4096%Z.
      + (* [comment removed for export] *)
        constructor; cbn zeta.
        * kbyte HK.
        * kbyte HK.
        * krdn HK.
        * intros _. kbyte HK.
        * intros _. kbyte HK.
        * intros _. krdn HK.
        * intros _. kbyte HK.
        * intros _. krdn HK.
        * change (69616 * 0 / 16 + 1)%Z with 1%Z. lia.
      + kdef HK gx 0%Z 69632%Z.
      + replace (bv_unsigned brk + 4096)%Z with (bv_unsigned brk + 1 * 4096)%Z by lia. rewrite Z_mod_plus_full. exact Bal.
      + exact (proj2 Kga).
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + exact Htid.
      + destruct (errno_some M) as (bs & Hbs & Hlen). exists (bytes_le_to_Z bs).
        pose proof (SX2S.bytes_le_to_Z_bound bs) as Hb. rewrite Hlen in Hb.
        split; [cbn in Hb; lia|]. unfold cell. rewrite Hbs, word_to_le_bytes_of_lez by (assumption || lia). reflexivity.
      + exists (bv_unsigned (vals_ev vals 4)). kcell HK.
      + apply (img_clear_of_know (ENVv vals)). apply (kderive_all_sound RSEGS _ M knZ); [exact HK | vm_compute; reflexivity].
    - (* [comment removed for export] *)
      constructor. all: kcell HK.
    - exact HVM.
    - (* [comment removed for export] *)
      destruct HVS as (Hr & Hl & Hm). unfold vm_small. rewrite Hr, Hl.
      split; [reflexivity|]. split; [reflexivity|].
      assert (U1 : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by reflexivity.
      assert (U2 : bv_unsigned (Z_to_bv 64 8192) = 8192%Z) by reflexivity.
      assert (U3 : bv_unsigned (Z_to_bv 64 4096) = 4096%Z) by reflexivity.
      destruct Hm as [[-> Hdj] | [-> Hdj]]; cbn [length In fst snd];
        (split; [lia|]); (split; [left; reflexivity|]); split;
        [ repeat constructor; cbn [fst snd]; rewrite ?U1, ?U2, ?U3, ?u64_lit' by lia; lia
        | apply seps_cons; [constructor; [unfold iv_disjoint; cbn [fst snd]; rewrite ?U1, ?U2, ?U3, ?u64_lit' by lia; lia | constructor]
                          | apply seps_cons; [constructor | apply seps_nil]]
        | repeat constructor; cbn [fst snd]; rewrite ?U1, ?U2, ?U3, ?u64_lit' by lia; lia
        | apply seps_cons; [constructor; [unfold iv_disjoint; cbn [fst snd]; rewrite ?U1, ?U2, ?U3, ?u64_lit' by lia; lia | constructor]
                          | apply seps_cons; [constructor | apply seps_nil]] ].
    - exact HSI.
  Qed.

  Lemma w65_exitT : after_malloc_gen K -> exitT_branch sp0 a0s path envv tid brk fs0 stdin0 fd3 SI K.
  Proof using rdraw Hva Hve Hvsp Htid Hbrk Hplen.
    intros AM vals R M VM HL P0 P2 P70 P5 HR HK HVM HVS HSI.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_krange gx) in exact i) _ HK eq_refl)
      as Kgm; cbn [kentry_ok edenot ev ENV ENVr gx bx ax] in Kgm.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_kalign gx) in exact i) _ HK eq_refl)
      as Kga; cbn [kentry_ok edenot ev ENV ENVr gx bx ax] in Kga.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_kdisj ax gx) in exact i) _ HK eq_refl)
      as Kgd; cbn [kentry_ok] in Kgd; unfold estart in Kgd; cbn [a_base a_off edenot ev ENV ENVr gx bx ax] in Kgd.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_krange ax) in exact i) _ HK eq_refl)
      as Kam; cbn [kentry_ok edenot ev ENV ENVr gx bx ax] in Kam.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_kalign ax) in exact i) _ HK eq_refl)
      as Kaa; cbn [kentry_ok edenot ev ENV ENVr gx bx ax] in Kaa.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_kdisj (ELit 0) ax) in exact i) _ HK eq_refl)
      as Kai; cbn [kentry_ok] in Kai; unfold estart in Kai; cbn [a_base a_off edenot ev ENV ENVr gx bx ax] in Kai; rewrite u0 in Kai.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_kdisj (EVar 0) gx) in exact i) _ HK eq_refl)
      as Kgw; cbn [kentry_ok] in Kgw; unfold estart in Kgw; cbn [a_base a_off edenot ev ENV ENVr gx bx ax] in Kgw; rewrite P0 in Kgw.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_kdisj (EVar 0) ax) in exact i) _ HK eq_refl)
      as Kaw; cbn [kentry_ok] in Kaw; unfold estart in Kaw; cbn [a_base a_off edenot ev ENV ENVr gx bx ax] in Kaw; rewrite P0 in Kaw.
    pose proof (u64_range (vals_ev vals 71)) as Au.
    pose proof p1_range as P1r.
    pose proof (u64_range brk) as Bu. pose proof (u64_range sp0) as Su.
    rewrite modelV_eq.
    apply (AM R M VM (vals_ev vals 71) (vals_ev vals 72) (vals_ev vals 7) (vals_ev vals 4) (bv_unsigned (vals_ev vals 71) + 4096)%Z (2 ^ 64 - 1)%Z 1%Z).
    - reflexivity.
    - (* [comment removed for export] *)
      constructor.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + lia.
      + exact P1r.
      + lia.
      + lia.
      + lia.
      + lia.
      + unfold stack_writable. apply (kwr_window (ENVv vals) M knZm (EVar 0) (-8388608) 8388608); [exact HK | vm_compute; reflexivity | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia].
      + unfold group_writable. apply (kwr_window (ENVv vals) M knZm gx 0 69632); [exact HK | vm_compute; reflexivity | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia].
      + unfold meta_writable. apply (kwr_window (ENVv vals) M knZm ax 4096 4096); [exact HK | vm_compute; reflexivity | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia].
      + destruct (errno_some M) as (bs & Hbs & Hlen). exists (Z_to_bv 64 (bytes_le_to_Z bs)).
        rewrite Hbs, word_to_le_bytes_of_lez by (assumption || lia). reflexivity.
      + intros x0 x1 x5 x6 extra ebs.
        apply (know_ok_ren RSEGS (ENVv vals) _ M fT [2;3;4;7]%nat kn_M1).
        * intros i Hi. destruct Hi as [<-|[<-|[<-|[<-|[]]]]]; cbn [ev ENV fT Nat.eqb vals_ev nth app]; pins; reflexivity.
        * vm_compute. reflexivity.
        * apply (kderive_all_sound RSEGS _ M knZm); [exact HK | vm_compute; reflexivity].
    - (* [comment removed for export] *)
      constructor.
      all: try kcell HK.
      all: try kzero HK.
      + exists (bv_unsigned (vals_ev vals 7)). split; [apply u64_range|]. split; kcell HK.
      + apply (cell_join M _ 4 4 101 0); [kcell HK | kcell HK | reflexivity | pins; lia | pins; lia].
      + apply (cell_join M _ 4 4 0 0); [kcell HK | kcell HK | reflexivity | pins; lia | pins; lia].
      + kdef HK ax 4096%Z 4096%Z.
      + (* [comment removed for export] *)
        constructor; cbn zeta.
        * kbyte HK.
        * kbyte HK.
        * krdn HK.
        * intros _. kbyte HK.
        * intros _. kbyte HK.
        * intros _. krdn HK.
        * intros _. kbyte HK.
        * intros _. krdn HK.
        * change (69616 * 0 / 16 + 1)%Z with 1%Z. lia.
      + kdef HK gx 0%Z 69632%Z.
      + replace (bv_unsigned (vals_ev vals 71) + 4096)%Z with (bv_unsigned (vals_ev vals 71) + 1 * 4096)%Z by lia. rewrite Z_mod_plus_full. exact (proj2 Kaa).
      + exact (proj2 Kga).
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + exact Htid.
      + destruct (errno_some M) as (bs & Hbs & Hlen). exists (bytes_le_to_Z bs).
        pose proof (SX2S.bytes_le_to_Z_bound bs) as Hb. rewrite Hlen in Hb.
        split; [cbn in Hb; lia|]. unfold cell. rewrite Hbs, word_to_le_bytes_of_lez by (assumption || lia). reflexivity.
      + exists (bv_unsigned (vals_ev vals 4)). kcell HK.
      + apply (img_clear_of_know (ENVv vals)). apply (kderive_all_sound RSEGS _ M knZm); [exact HK | vm_compute; reflexivity].
    - (* [comment removed for export] *)
      constructor. all: kcell HK.
    - exact HVM.
    - (* [comment removed for export] *)
      destruct HVS as (Hr & Hl & Hm). unfold vm_small. rewrite Hr, Hl.
      split; [reflexivity|]. split; [reflexivity|].
      assert (U1 : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by reflexivity.
      assert (U2 : bv_unsigned (Z_to_bv 64 8192) = 8192%Z) by reflexivity.
      assert (U3 : bv_unsigned (Z_to_bv 64 4096) = 4096%Z) by reflexivity.
      destruct Hm as [[-> Hdj] | [-> Hdj]]; cbn [length In fst snd];
        (split; [lia|]); (split; [left; reflexivity|]); split;
        [ repeat constructor; cbn [fst snd]; rewrite ?U1, ?U2, ?U3, ?u64_lit' by lia; lia
        | apply seps_cons; [constructor; [unfold iv_disjoint; cbn [fst snd]; rewrite ?U1, ?U2, ?U3, ?u64_lit' by lia; lia | constructor]
                          | apply seps_cons; [constructor | apply seps_nil]]
        | repeat constructor; cbn [fst snd]; rewrite ?U1, ?U2, ?U3, ?u64_lit' by lia; lia
        | apply seps_cons; [constructor; [unfold iv_disjoint; cbn [fst snd]; rewrite ?U1, ?U2, ?U3, ?u64_lit' by lia; lia | constructor]
                          | apply seps_cons; [constructor | apply seps_nil]] ].
    - exact HSI.
  Qed.

  (* [comment removed for export] *)
  Theorem brk_ok_semV : after_malloc_gen K ->
    brk_ok_entry sp0 a0s path envv tid brk mbase fs0 stdin0 fd3 SI (t_alt2 (t_die msg_oom fs0) K).
  Proof using rdraw Hva Hve Hvsp Htid Hbrk Hplen SI_step. intros AM. apply brk_ok_worldV; try assumption. apply w65_exitG, AM. Qed.

  Theorem mmap_ok_semV : after_malloc_gen K ->
    mmap_ok_entry sp0 a0s path envv tid brk mbase fs0 stdin0 fd3 SI (t_alt2 (t_die msg_oom fs0) (t_alt2 (t_die msg_oom fs0) K)).
  Proof using rdraw Hva Hve Hvsp Htid Hbrk Hplen SI_step. intros AM. apply mmap_ok_worldV; try assumption. apply w65_exitT, AM. Qed.
End World.

(* [comment removed for export] *)
Theorem brk_ok_sem_g {AMB : Amb} sp0 a0s path envv (rdraw : EntryDraw) tid mem0 brk mbase fs0 stdin0
  (Hva : valid_argv [a0s; path]) (Hve : valid_envp envv)
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) fd3 K :
  after_malloc_gen sp0 a0s path envv tid fs0 stdin0 fd3 (above_eq sp0 mem0) K ->
  brk_ok_branch_g sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 fd3 (t_alt2 (t_die msg_oom fs0) K).
Proof.
  intros AM. exact (brk_ok_semV sp0 a0s path envv rdraw tid brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk Hplen fd3
                      (above_eq sp0 mem0) (above_eq_step sp0 mem0) K AM).
Qed.

Theorem mmap_ok_sem_g {AMB : Amb} sp0 a0s path envv (rdraw : EntryDraw) tid mem0 brk mbase fs0 stdin0
  (Hva : valid_argv [a0s; path]) (Hve : valid_envp envv)
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) fd3 K :
  after_malloc_gen sp0 a0s path envv tid fs0 stdin0 fd3 (above_eq sp0 mem0) K ->
  mmap_ok_branch_g sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 fd3 (t_alt2 (t_die msg_oom fs0) (t_alt2 (t_die msg_oom fs0) K)).
Proof.
  intros AM. exact (mmap_ok_semV sp0 a0s path envv rdraw tid brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk Hplen fd3
                      (above_eq sp0 mem0) (above_eq_step sp0 mem0) K AM).
Qed.

(* [comment removed for export] *)
Theorem brk_ok_sem {AMB : Amb} sp0 a0s path envv (rdraw : EntryDraw) tid mem0 brk mbase fs0 stdin0
  (Hva : valid_argv [a0s; path]) (Hve : valid_envp envv)
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) K :
  after_malloc sp0 a0s path envv tid fs0 stdin0 K ->
  brk_ok_branch sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 (t_alt2 (t_die msg_oom fs0) K).
Proof.
  intros AM. apply (brk_ok_sem_g sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk Hplen).
  intros R M VM mb gm sec cn area brkv mas EA RP W MF VP VS _. exact (AM R M VM mb gm sec cn area brkv mas EA RP W MF VP VS).
Qed.

Theorem mmap_ok_sem {AMB : Amb} sp0 a0s path envv (rdraw : EntryDraw) tid mem0 brk mbase fs0 stdin0
  (Hva : valid_argv [a0s; path]) (Hve : valid_envp envv)
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) K :
  after_malloc sp0 a0s path envv tid fs0 stdin0 K ->
  mmap_ok_branch sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 (t_alt2 (t_die msg_oom fs0) (t_alt2 (t_die msg_oom fs0) K)).
Proof.
  intros AM. apply (mmap_ok_sem_g sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk Hplen).
  intros R M VM mb gm sec cn area brkv mas EA RP W MF VP VS _. exact (AM R M VM mb gm sec cn area brkv mas EA RP W MF VP VS).
Qed.
