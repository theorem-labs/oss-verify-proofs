(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import RunEnv
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes
  MmapSim AllocSim FileSim AgentLib SpecConsts DivergeSim SpinAlg SpinAlgX
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame
  Spec LibWritev RefNodes RefMemcpyLib RefReadLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10Startup_u Pm10MainEntry_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Hoare MemSplit
  HeapIface DrvKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10Drv_defs_u Pm10DrvLib_u Pm10DrvA_u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.

Lemma vals_lo : forall (vals ext : list word) (n j : nat),
  (n <= length vals)%nat -> (j < n)%nat -> vals_ev (firstn n vals ++ ext) j = vals_ev vals j.
Proof.
  intros vals ext n j Hn Hj. unfold vals_ev. rewrite app_nth1 by (rewrite length_firstn; lia).
  rewrite nth_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj). reflexivity.
Qed.
Lemma vals_hi : forall (vals ext : list word) (n i : nat),
  (n <= length vals)%nat -> vals_ev (firstn n vals ++ ext) (n + i) = nth i ext (Z_to_bv 64 0).
Proof.
  intros vals ext n i Hn. unfold vals_ev. rewrite app_nth2 by (rewrite length_firstn; lia).
  rewrite length_firstn. replace (n + i - Nat.min n (length vals))%nat with i by lia. reflexivity.
Qed.
Lemma len_lay : forall (vals ext : list word) n, (n <= length vals)%nat -> length (firstn n vals ++ ext) = (n + length ext)%nat.
Proof. intros. rewrite length_app, length_firstn. lia. Qed.

Lemma regs_ok_by_nth : forall E sr R,
  (forall i, (0 < i < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat i)) = edenot E (nth i sr (ELit 0))) -> regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot]. reflexivity.
  - assert (Hnz : ridx r <> 0%nat).
    { intros Hc. assert (r = 0%bv) by (rewrite <- (ridx_roundtrip r), Hc; apply bv_eq; reflexivity). subst r.
      rewrite bv_eqb_refl in Hr0. discriminate. }
    pose proof (H (ridx r) ltac:(pose proof (ridx_range r); lia)) as Hx. rewrite ridx_roundtrip in Hx. exact Hx.
Qed.

Lemma store_ok_of_defined : forall M (a : Z) (m : nat),
  (0 <= a)%Z -> (a + Z.of_nat m <= 2 ^ 64)%Z -> (forall i, (0 <= i < Z.of_nat m)%Z -> M (Z_to_bv 64 (a + i)) <> None) ->
  store_ok RSEGS M (Z_to_bv 64 a) m = true.
Proof.
  intros M a m Ha Ham Hdef. destruct m as [|m']; [reflexivity|].
  apply store_ok_of_all; [rewrite u_small by lia; lia|].
  intros x Hx. rewrite u_small in Hx by lia. unfold wview.
  specialize (Hdef (bv_unsigned x - a)%Z ltac:(lia)). replace (a + (bv_unsigned x - a))%Z with (bv_unsigned x) in Hdef by lia.
  rewrite Z_to_bv_bv_unsigned in Hdef. destruct (M x); [discriminate | exfalso; apply Hdef; reflexivity].
Qed.

Lemma stage_store_ok : forall M (n : nat), (Z.of_nat n <= 65536)%Z -> store_ok RSEGS M (Z_to_bv 64 0xc4db9) n = true.
Proof.
  intros M n Hn. eapply (store_ok_window RSEGS M (Z_to_bv 64 0xc4000) _ 212992%nat n 0xc4000 0xf8000);
    [reflexivity | reflexivity | lia | exact wseg_c2000 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
Qed.

Section DrvB.
  Context {RE : RunEnv}.
  Variable L : heap_layout.
  Variable HI : heap_iface.
  Hypothesis HIok : heap_iface_ok L scfg HI.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable VM0 : VmMaps.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable fdata : list byte.
  Variable cr0 : credit.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hplen : (length path <= 4095)%nat.
  Hypothesis DL : drv_layout L sp0.

  Let Hsp : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z := conj (proj1 Hvsp) (proj1 (proj2 Hvsp)).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let LEN : Z := Z.of_nat (length fdata).

  Let ENVb (vals : list word) : env := ENV a0s path hw rdraw fdata vals.
  Let above (M : word -> option byte) : Prop := above_sp0 sp0 mem0 M.

  Definition model2 (VM : VmMaps) : Model := mkModelE fds0 VM stdin0 fs0 None (Some tid) None.

  Definition model1o (off : Z) (VM : VmMaps) : Model := mkModelE (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 off))) VM stdin0 fs0 None (Some tid) None.

  Lemma model1_o : forall VM, model1 path tid fs0 stdin0 VM = model1o 0 VM. Proof. reflexivity. Qed.
  Lemma m1o_fds : forall off VM, m_fds (model1o off VM) = fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 off)).
  Proof. reflexivity. Qed.
  Lemma m1o_fs : forall off VM, m_fs (model1o off VM) = fs0. Proof. reflexivity. Qed.
  Lemma fds_lookup3 : forall off, fd_lookup (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 off))) (Z_to_bv 64 3)
                                  = Some (FdFile path (Z_to_bv 64 off)).
  Proof. intros. reflexivity. Qed.
  Lemma fds_remove3 : forall off, fd_remove (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 off))) (Z_to_bv 64 3) = fds0.
  Proof. intros. reflexivity. Qed.
  Lemma with_fds_read : forall off off' VM,
    with_fds (fd_insert (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 off))) (Z_to_bv 64 3) (FdFile path off')) (model1o off VM)
    = mkModelE (fd_insert fds0 (Z_to_bv 64 3) (FdFile path off')) VM stdin0 fs0 None (Some tid) None.
  Proof. intros. reflexivity. Qed.
  Lemma with_fds_close : forall off VM, with_fds fds0 (model1o off VM) = model2 VM.
  Proof. intros. reflexivity. Qed.

  Lemma hiv_facts' : forall vals,
    vals_ev vals 3 = auxvp sp0 a0s path envv -> vals_ev vals 4 = rnd sp0 a0s path envv ->
    forall i, In i [3%nat; 4%nat] -> (bv_unsigned sp0 <= bv_unsigned (vals_ev vals i))%Z /\ (bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64)%Z.
  Proof. intros vals P3 P4 i Hi. exact (hiv_facts sp0 a0s path envv uid hw rdraw Hva Hve Hvsp Hplen vals P3 P4 i Hi). Qed.

  Lemma content_block' : forall vals M log (A : Z) (data : list byte),
    vals_ev vals 0 = sp0 -> log_in_b 0 (2 ^ 40) (2 ^ 40) [] [] IMG_W log = true ->
    hz sp0 A (Z.of_nat (length data)) ->
    rdn RSEGS M (Z_to_bv 64 A) (length data) = Some data ->
    rdn RSEGS (mem_denot (ENVb vals) M log) (Z_to_bv 64 A) (length data) = Some data.
  Proof.
    clear Htid Hplen Hal. intros vals M log A data P0 Hlog HZ Hc. unfold ENVb, ENV.
    rewrite (rdn_heap_frame sp0 Hsp vals _ M log A (length data) P0 Hlog HZ). exact Hc.
  Qed.

  Lemma above_wbytes : forall M (a : Z) bs,
    (0 <= a)%Z -> (a + Z.of_nat (length bs) <= bv_unsigned sp0)%Z -> above M -> above (wbytes M (Z_to_bv 64 a) bs).
  Proof.
    clear Htid Hplen Hal LEN. intros M a bs Ha Hab HA x Hx. pose proof Hsp as Hsp'. rewrite wbytes_out; [apply HA; exact Hx | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
  Qed.

  Lemma heap_stagewrite : forall LB cr M VM bs,
    (Z.of_nat (length bs) <= 65536)%Z -> hi_heap HI LB cr M VM -> hi_heap HI LB cr (wbytes M (Z_to_bv 64 0xc4db9) bs) VM.
  Proof.
    clear Htid Hplen Hal LEN ENVb. intros LB cr M VM bs Hn HH. pose proof Hsp as Hsp'.
    apply (hio_frame L scfg HI HIok LB cr M _ VM HH).
    - intros x Hx Hp. apply wbytes_out; rewrite ?u_small by lia; [lia|].
      destruct (Z.lt_ge_cases x 0xc4db9) as [Hlt|Hge]; [left; exact Hlt|]. right.
      destruct (Z.lt_ge_cases x (0xc4db9 + Z.of_nat (length bs))) as [Hlt2|Hge2]; [|exact Hge2].
      exfalso. destruct Hp as [(_ & _ & Hni)|Hro].
      + apply Hni. rewrite (dl_img_lo L sp0 DL), (dl_img_hi L sp0 DL). split; [lia|]. intros Hs. apply (dl_static L sp0 DL) in Hs. lia.
      + apply (dl_ro L sp0 DL) in Hro. lia.
    - intros x Hx. exact (wbytes_grows bs M (Z_to_bv 64 0xc4db9) x Hx).
  Qed.

  Definition IMG_NOSTAGE : list (Z * Z) := [(0x10000, 0xc4db9); (0xd4db9, 0xd675c); (0xd6760, 0xf6c08); (0xf6fb0, 0xf8000)]%Z.
  Definition CPout_stage (n : Z) (a : Z) : Prop := ~ (0xc4db9 <= a < 0xc4db9 + n)%Z.

  Lemma regions_stagewrite : forall vals (n : Z) bls LB,
    vals_ev vals 0 = sp0 -> (0 <= n <= 65536)%Z ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_block L LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall i, In i [3%nat; 4%nat] -> (bv_unsigned sp0 <= bv_unsigned (vals_ev vals i))%Z /\ (bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64)%Z) ->
    regions_ok RSEGS 0 0 0 bls [] [3%nat; 4%nat] IMG_NOSTAGE IMG_RW (ENVb vals) (CPout_stage n) (fun _ => False).
  Proof.
    clear Htid Hplen Hal. intros vals n bls LB P0 Hn Hbl Hhi. pose proof Hsp as Hsp'.
    constructor; cbn [ev ENVb ENV]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold CPout_stage. lia.
    - intros z Hz. exfalso. lia.
    - intros i nb Hf. destruct (Hbl i nb Hf) as (Hi & HSB). pose proof (sub_block_hz L sp0 DL _ _ _ HSB) as (Z1 & Z2 & Z3).
      destruct HSB as (cap & Hnb & Hin & HB). pose proof (hz_of_block_range L sp0 DL _ _ HB) as (Y1 & Y2 & Y3).
      split; [lia|]. intros z Hz. unfold CPout_stage. lia.
    - intros v b Hf. discriminate.
    - intros i Hi. destruct (Hhi i Hi) as [H1 H2]. split; [exact H1|]. split; [exact H2|]. intros z Hz. unfold CPout_stage. lia.
    - intros lo hi Hin. unfold IMG_NOSTAGE in Hin.
      destruct Hin as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros a Ha; unfold CPout_stage; lia.
    - intros lo hi Hin. unfold IMG_RW in Hin.
      destruct Hin as [E1|[E1|[]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros Mx d m Hd Hm.
      + eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xbd000) _ 28672%nat m 0xbd000 0xc4000);
          [reflexivity | reflexivity | lia | exact wseg_bb000 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
      + eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xc4000) _ 212992%nat m 0xc4000 0xf8000);
          [reflexivity | reflexivity | lia | exact wseg_c2000 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
  Qed.

  Definition keep_stage (bls : list (nat * Z)) (kn : list kentry) : list kentry :=
    kn_keep_g 0 0 0 bls [] [3%nat; 4%nat] IMG_NOSTAGE IMG_RW kn.

  Lemma know_stagewrite : forall vals M bs bls LB kn,
    vals_ev vals 0 = sp0 -> (Z.of_nat (length bs) <= 65536)%Z ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_block L LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall i, In i [3%nat; 4%nat] -> (bv_unsigned sp0 <= bv_unsigned (vals_ev vals i))%Z /\ (bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64)%Z) ->
    know_ok RSEGS (ENVb vals) M kn ->
    know_ok RSEGS (ENVb vals) (wbytes M (Z_to_bv 64 0xc4db9) bs) (keep_stage bls kn).
  Proof.
    clear Htid Hplen Hal. intros vals M bs bls LB kn P0 Hn Hbl Hhi HK.
    eapply (know_keep_g_sound RSEGS 0 0 0 bls [] [3%nat; 4%nat] IMG_NOSTAGE IMG_RW (ENVb vals) (CPout_stage (Z.of_nat (length bs))) (fun _ => False)
              (regions_stagewrite vals (Z.of_nat (length bs)) bls LB P0 ltac:(lia) Hbl Hhi) M).
    - intros x Hx Hout. unfold CPout_stage in Hout. apply wbytes_out; rewrite ?u_small by lia; [lia|lia].
    - intros x [].
    - apply wbytes_grows.
    - exact HK.
  Qed.

End DrvB.
End FPX_1.
