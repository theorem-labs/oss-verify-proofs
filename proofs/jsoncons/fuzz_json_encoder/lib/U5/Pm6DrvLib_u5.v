(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RunEnv
  PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg SpinAlg Hoare
  SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 RefMemcpyLib
  HeapIface DrvKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6MainEntry_u5 Pm6Drv_defs_u5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Record drv_layout (L : heap_layout) (sp0 : word) : Prop := DRV_LAYOUT {
  dl_segs : hl_segs L = RSEGS;
  dl_malloc : hl_malloc L = 0xaf8f8;
  dl_free : hl_free L = 0xaf7b8;
  dl_tp : hl_tp L = 0xdd010;
  dl_img_lo : hl_img_lo L = 0x10000;
  dl_img_hi : hl_img_hi L = 0xfe000;
  dl_static : forall a, hl_alloc_static L a -> 0xfd418 <= a < 0xfd7c0;
  dl_ro : forall a, hl_alloc_ro L a -> (0x10000 <= a < 0xcb000) \/ (0xfd280 <= a < 0xfd288) \/ (0xfd2a0 <= a < 0xfd418) \/ (0xfd7c0 <= a < 0xfd7c8) \/ (0xfdc04 <= a < 0xfdc08) \/ bv_unsigned sp0 <= a;
  dl_errno : hl_errno L = 0xdcf6c;
  dl_sptop : hl_sptop L = bv_unsigned sp0;
  dl_stack : 0 <= hl_stack L <= 16384;
  dl_k : 0 <= hl_k_per_malloc L;
  dl_b : 0 <= hl_b_overhead L
}.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvLayout.
  Variable L : heap_layout.
  Variable HI : heap_iface.
  Hypothesis HIok : heap_iface_ok L scfg HI.
  Variable sp0 : word.
  Hypothesis Hsp : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layout L sp0.

  (* [comment removed for export] *)
  Lemma wseg_c0000 : wseg_ok RSEGS (Z_to_bv 64 0xc4000) 28672 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma wseg_c7000 : wseg_ok RSEGS (Z_to_bv 64 0xcb000) 208896 = true.
  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition CPm (LB : list (Z * Z)) (sp : Z) (a : Z) : Prop := client_addr L LB sp (hl_stack L) a /\ ~ in_errno L a.
  Definition SCm (sp : Z) (a : Z) : Prop := sp - hl_stack L <= a < sp.

  (* [comment removed for export] *)
  Definition sub_block (LB : list (Z * Z)) (A nb : Z) : Prop :=
    exists cap, 0 < nb <= cap /\ In (A, cap) LB /\ block_range L A cap.

  (* [comment removed for export] *)
  Definition hz (A n : Z) : Prop := 4096 <= A /\ (A + n <= 0x10000 \/ 0xfe000 <= A) /\ A + n <= bv_unsigned sp0 - 8388608.

  Lemma hz_of_block_range : forall A n, block_range L A n -> hz A n.
  Proof.
    clear Hsp Hal. intros A n (B1 & B2 & B3 & B4 & B5). pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH.
    pose proof (dl_sptop L sp0 DL) as TOP. unfold hz. rewrite IL, IH in B2. rewrite TOP in B5. repeat split; try lia.
  Qed.

  Lemma hz_sub : forall A n a m, hz A n -> A <= a -> 0 <= m -> a + m <= A + n -> hz a m.
  Proof. clear Hsp Hal. intros A n a m (H1 & H2 & H3) Ha Hm Ham. unfold hz. lia. Qed.

  Lemma sub_block_hz : forall LB A nb, sub_block LB A nb -> hz A nb.
  Proof.
    clear Hsp Hal. intros LB A nb (cap & Hnb & _ & HB). apply hz_of_block_range in HB. eapply hz_sub; [exact HB | lia | lia | lia].
  Qed.

  Lemma regions_alloc : forall vals ebs so bls vbnd LB,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    - 2 ^ 22 <= so <= 0 ->
    (forall i nb, find_nz i bls = Some nb -> sub_block LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> bv_unsigned (vals_ev vals v) <= b) ->
    (forall i, In i [3%nat; 4%nat] -> bv_unsigned sp0 <= bv_unsigned (vals_ev vals i) /\ bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64) ->
    regions_ok RSEGS 0 so 16384 bls vbnd [3%nat; 4%nat] IMG_CLIENT IMG_RW E
               (CPm LB (bv_unsigned sp0 + so)) (SCm (bv_unsigned sp0 + so)).
  Proof.
    intros vals ebs so bls vbnd LB E P0 Hso Hbl Hvb Hhi.
    pose proof (dl_stack L sp0 DL) as ST. pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH.
    pose proof (dl_errno L sp0 DL) as ER. pose proof (dl_sptop L sp0 DL) as TOP.
    assert (NE : forall a, 0xdcf70 <= a \/ a < 0xdcf6c -> ~ in_errno L a) by (intros a Ha; unfold in_errno; rewrite ER; lia).
    constructor; cbn [ev E]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold CPm, client_addr. split; [right; left; rewrite TOP; lia | apply NE; lia].
    - intros z Hz. destruct (Z.lt_ge_cases (bv_unsigned sp0 + z) (bv_unsigned sp0 + so - hl_stack L)) as [A|A].
      + left. unfold CPm, client_addr. split; [right; left; rewrite TOP; lia | apply NE; lia].
      + right. unfold SCm. lia.
    - intros i nb Hf. pose proof (sub_block_hz _ _ _ (Hbl i nb Hf)) as (Z1 & Z2 & Z3).
      destruct (Hbl i nb Hf) as (cap & Hnb & Hin & HB). pose proof (hz_of_block_range _ _ HB) as (Y1 & Y2 & Y3).
      split; [lia|].
      intros z Hz. unfold CPm, client_addr.
      split; [left; exists (bv_unsigned (vals_ev vals i), cap); split; [exact Hin|]; cbn [fst snd]; lia | apply NE; lia].
    - exact Hvb.
    - intros i Hi. destruct (Hhi i Hi) as [H1 H2]. split; [exact H1|]. split; [exact H2|].
      intros z Hz. unfold CPm, client_addr. split; [right; left; rewrite TOP; lia | apply NE; lia].
    - intros lo hi Hin. unfold IMG_CLIENT in Hin.
      destruct Hin as [E1|[E1|[E1|[]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]);
        intros a Ha; unfold CPm, client_addr; (split; [| apply NE; lia]); right; right; rewrite IL, IH; (split; [lia|]);
        intros Hs; apply (dl_static L sp0 DL) in Hs; lia.
    - intros lo hi Hin. unfold IMG_RW in Hin.
      destruct Hin as [E1|[E1|[]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros Mx d m Hd Hm.
      + eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xc4000) _ 28672%nat m 0xc4000 0xcb000);
          [reflexivity | reflexivity | lia | exact wseg_c0000 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
      + eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xcb000) _ 208896%nat m 0xcb000 0xfe000);
          [reflexivity | reflexivity | lia | exact wseg_c7000 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma regs_preserved_kept : forall R R', regs_preserved R R' -> forall r : reg, In r c_kept -> getr R' r = getr R r.
  Proof.
    intros R R' HP r Hr. apply HP. unfold c_kept in Hr. unfold callee_saved_idx.
    repeat (destruct Hr as [<-|Hr]; [cbn; tauto|]). destruct Hr.
  Qed.

  Lemma c_kept_no0 : ~ In (0%bv : reg) c_kept.
  Proof. unfold c_kept. intros H. repeat (destruct H as [H|H]; [discriminate|]). exact H. Qed.

  (* [comment removed for export] *)
  Lemma has_entry_nth : forall kn K, existsb (kentry_eqb K) kn = true -> exists i, nth_error kn i = Some K.
  Proof.
    intros kn K H. apply existsb_exists in H as (K' & Hin & Heq). apply kentry_eqb_eq in Heq. subst K'.
    apply In_nth_error in Hin. exact Hin.
  Qed.

  (* [comment removed for export] *)
  Lemma block_store_ok : forall vals ebs M kn v n (A : Z) (k : Z) (m : nat),
    let E := Env (vals_ev vals) ebs in
    know_ok RSEGS E M kn -> existsb (kentry_eqb (KWr (SA (EVar v) 0) n)) kn = true ->
    vals_ev vals v = Z_to_bv 64 A -> (0 <= A)%Z -> (A < 2 ^ 64)%Z ->
    (0 <= k)%Z -> (k + Z.of_nat m <= n)%Z ->
    store_ok RSEGS M (Z_to_bv 64 (A + k)) m = true.
  Proof.
    intros vals ebs M kn v n A k m E HK Hhas Pv HA HAn Hk Hm.
    destruct (has_entry_nth kn _ Hhas) as [i Hi].
    pose proof (kwr_store_ok RSEGS E M kn i (EVar v) 0 n k m HK Hi Hk Hm) as W.
    unfold adenot in W. cbn [a_base a_off edenot ev E] in W. rewrite Pv in W. unfold v_addi in W.
    rewrite u_small in W by lia. exact W.
  Qed.

  Definition has_window (kn : list kentry) : bool := existsb (kentry_eqb (KWr (SA (EVar 0) (-8388608)) 8388608)) kn.

  Lemma has_window_nth : forall kn, has_window kn = true -> exists i, nth_error kn i = Some (KWr (SA (EVar 0) (-8388608)) 8388608).
  Proof.
    intros kn H. unfold has_window in H. apply existsb_exists in H as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
    apply In_nth_error in Hin. exact Hin.
  Qed.

  Lemma stack_ok_of_window : forall vals ebs M kn so,
    let E := Env (vals_ev vals) ebs in
    know_ok RSEGS E M kn -> has_window kn = true ->
    vals_ev vals 0 = sp0 ->
    - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
    stack_ok L M (bv_unsigned sp0 + so).
  Proof.
    intros vals ebs M kn so E HK Hw P0 Hso Hsoal. destruct (has_window_nth kn Hw) as [i Hn]. pose proof (dl_stack L sp0 DL) as ST.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'. pose proof (dl_sptop L sp0 DL) as TOP.
    unfold stack_ok. rewrite TOP. split; [|split; [lia|split; [lia|split; [lia|]]]].
    { rewrite Z.add_mod, Hal, Hsoal by lia. reflexivity. }
    intros d m Hd Hm.
    pose proof (kwr_store_ok RSEGS E M kn i (EVar 0) (-8388608) 8388608 (so - hl_stack L + d) m HK Hn ltac:(lia) ltac:(lia)) as W.
    unfold adenot in W. cbn [a_base a_off edenot ev E] in W. rewrite P0 in W. unfold v_addi in W.
    rewrite (dl_segs L sp0 DL).
    replace (bv_unsigned sp0 + so - hl_stack L + d) with (bv_unsigned sp0 + (so - hl_stack L + d)) by lia. exact W.
  Qed.

  (* [comment removed for export] *)
  Lemma kn_blk_ok : forall vals ebs M' v n A,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals v = Z_to_bv 64 A -> vals_ev vals 0 = sp0 ->
    block_range L A n -> defined M' A n ->
    know_ok RSEGS E M' (kn_blk v n).
  Proof.
    intros vals ebs M' v n A E Pv P0 HBR Hdef. pose proof HBR as (_ & _ & B2 & B3 & _).
    pose proof (hz_of_block_range _ _ HBR) as (Z1 & Z2 & Z3). pose proof Hsp as Hsp'.
    assert (EA : bv_unsigned (edenot E (EVar v)) = A) by (cbn [edenot ev E]; rewrite Pv; apply u_small; lia).
    unfold kn_blk, know_ok.
    apply Forall_cons. { cbn [kentry_ok]. rewrite EA. lia. }
    apply Forall_cons. { cbn [kentry_ok]. rewrite EA. split; [lia | exact B2]. }
    apply Forall_cons.
    { cbn [kentry_ok]. split. { unfold flat, estart. cbn [a_base a_off]. rewrite EA. lia. }
      intros d m Hd Hm. unfold estart. cbn [a_base a_off]. rewrite EA.
      destruct m as [|m']; [reflexivity|]. set (m := S m') in *.
      apply store_ok_of_all; [rewrite u_small by lia; lia|].
      intros x Hx. rewrite u_small in Hx by lia.
      specialize (Hdef (bv_unsigned x - A) ltac:(lia)). replace (A + (bv_unsigned x - A)) with (bv_unsigned x) in Hdef by lia.
      rewrite Z_to_bv_bv_unsigned in Hdef. unfold wview. destruct (M' x); [discriminate | exfalso; apply Hdef; reflexivity]. }
    apply Forall_cons. { cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev E]. rewrite P0.
                         change (ev E v) with (vals_ev vals v). rewrite Pv, u_small by lia. right. lia. }
    apply Forall_cons. { cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev E].
                         change (ev E v) with (vals_ev vals v). rewrite Pv, !u_small by lia. lia. }
    apply Forall_nil.
  Qed.


  (* [comment removed for export] *)
  Definition IMG_W : list (Z * Z) := [(0xcb000, 0xfd280); (0xfd288, 0xfd2a0); (0xfd7d8, 0xfdc04); (0xfdc08, 0xfe000)]%Z.

  (* [comment removed for export] *)
  Definition CW (LB : list (Z * Z)) (a : Z) : Prop := ~ alloc_private L LB a.

  Lemma regions_write : forall vals ebs bls LB,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_block LB (bv_unsigned (vals_ev vals i)) nb) ->
    regions_ok RSEGS 0 (2 ^ 40) (2 ^ 40) bls [] [] IMG_W [] E (CW LB) (fun _ => True).
  Proof.
    intros vals ebs bls LB E P0 Hbl.
    pose proof (dl_stack L sp0 DL) as ST. pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH.
    pose proof (dl_sptop L sp0 DL) as TOP.
    assert (RO := dl_ro L sp0 DL). assert (STA := dl_static L sp0 DL).
    constructor; cbn [ev E]; rewrite ?P0.
    - lia.
    - lia.
    - (* [comment removed for export] *) intros z Hz Hnot. unfold CW, alloc_private. intros [[A _]|A]; [rewrite TOP in A; lia|].
      apply RO in A. lia.
    - intros z Hz. right. exact I.
    - intros i nb Hf. destruct (Hbl i nb Hf) as (Hi & HSB). pose proof (sub_block_hz _ _ _ HSB) as (Z1 & Z2 & Z3).
      destruct HSB as (cap & Hnb & Hin & HB). pose proof (hz_of_block_range _ _ HB) as (Y1 & Y2 & Y3).
      split; [lia|]. intros z Hz. unfold CW, alloc_private. intros [[_ [A _]]|A].
      + apply A. exists (bv_unsigned (vals_ev vals i), cap). split; [exact Hin|]. cbn [fst snd]. lia.
      + apply RO in A. lia.
    - intros v b Hf. discriminate.
    - intros i [].
    - intros lo hi Hin. unfold IMG_W in Hin.
      destruct Hin as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]);
        intros a Ha; unfold CW, alloc_private; intros [[_ [_ A]]|A];
        [ apply A; rewrite IL, IH; split; [lia|]; intros Hs; apply STA in Hs; lia
        | apply RO in A; lia
        | apply A; rewrite IL, IH; split; [lia|]; intros Hs; apply STA in Hs; lia
        | apply RO in A; lia
        | apply A; rewrite IL, IH; split; [lia|]; intros Hs; apply STA in Hs; lia
        | apply RO in A; lia
        | apply A; rewrite IL, IH; split; [lia|]; intros Hs; apply STA in Hs; lia
        | apply RO in A; lia ].
    - intros lo hi [].
  Qed.

  (* [comment removed for export] *)
  Lemma heap_block : forall vals ebs bls LB cr M VM log,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_block LB (bv_unsigned (vals_ev vals i)) nb) ->
    log_in_b 0 (2 ^ 40) (2 ^ 40) bls [] IMG_W log = true ->
    hi_heap HI LB cr M VM -> hi_heap HI LB cr (mem_denot E M log) VM.
  Proof.
    intros vals ebs bls LB cr M VM log E P0 Hbl Hlog HH.
    apply (hio_frame L scfg HI HIok LB cr M (mem_denot E M log) VM HH).
    - intros a Ha Hp. apply (mem_denot_frame_Z RSEGS 0 (2 ^ 40) (2 ^ 40) bls [] [] IMG_W E (CW LB) (fun _ => True) []
                               (regions_write vals ebs bls LB P0 Hbl) M log a Hlog Ha).
      unfold CW. tauto.
    - intros x Hx. exact (mem_denot_grows E M log x Hx).
  Qed.


  (* [comment removed for export] *)
  Definition CPstk (a : Z) : Prop := a < 4096 \/ (0x10000 <= a < 0xfe000) \/ bv_unsigned sp0 - 8388608 <= a.

  Lemma regions_stk : forall vals ebs,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    regions_ok RSEGS 0 (2 ^ 40) (2 ^ 40) [] [] [] IMG_W [] E CPstk (fun _ => True).
  Proof.
    intros vals ebs E P0.
    constructor; cbn [ev E]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold CPstk. lia.
    - intros z Hz. right. exact I.
    - intros i nb Hf. discriminate.
    - intros v b Hf. discriminate.
    - intros i [].
    - intros lo hi Hin. unfold IMG_W in Hin.
      destruct Hin as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros a Ha; unfold CPstk; lia.
    - intros lo hi [].
  Qed.

  Lemma mem_heap_frame : forall vals ebs M log (a : Z),
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    log_in_b 0 (2 ^ 40) (2 ^ 40) [] [] IMG_W log = true ->
    hz a 1 ->
    mem_denot E M log (Z_to_bv 64 a) = M (Z_to_bv 64 a).
  Proof.
    intros vals ebs M log a E P0 Hlog (Z1 & Z2 & Z3). pose proof Hsp as Hsp'.
    apply (mem_denot_frame_Z RSEGS 0 (2 ^ 40) (2 ^ 40) [] [] [] IMG_W E CPstk (fun _ => True) [] (regions_stk vals ebs P0) M log a Hlog).
    - lia.
    - unfold CPstk. lia.
  Qed.

  Lemma rdn_heap_frame : forall vals ebs M log (a : Z) (n : nat),
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    log_in_b 0 (2 ^ 40) (2 ^ 40) [] [] IMG_W log = true ->
    hz a (Z.of_nat n) ->
    rdn RSEGS (mem_denot E M log) (Z_to_bv 64 a) n = rdn RSEGS M (Z_to_bv 64 a) n.
  Proof.
    intros vals ebs M log a n E P0 Hlog HZ. pose proof HZ as (Z1 & Z2 & Z3). pose proof Hsp as Hsp'.
    apply rdn_agree. intros j Hj. rewrite u_small by lia.
    apply (mem_heap_frame vals ebs M log); [exact P0 | exact Hlog | eapply hz_sub; [exact HZ| lia | lia | lia]].
  Qed.

  (* [comment removed for export] *)
  Lemma heap_wbytes : forall LB cr M VM (A n a : Z) bs,
    hi_heap HI LB cr M VM -> In (A, n) LB -> A <= a -> a + Z.of_nat (length bs) <= A + n -> A + n <= 2 ^ 64 ->
    hi_heap HI LB cr (wbytes M (Z_to_bv 64 a) bs) VM.
  Proof.
    intros LB cr M VM A n a bs HH Hin H1 H2 H3.
    destruct (hio_wf L scfg HI HIok LB cr M VM HH) as [WF _]. destruct (WF _ Hin) as (HBR & _ & _). cbn [fst snd] in *.
    pose proof (hz_of_block_range _ _ HBR) as (Z1 & Z2 & Z3).
    apply (hio_frame L scfg HI HIok LB cr M _ VM HH).
    - intros x Hx Hp. apply wbytes_out; [rewrite u_small by lia; lia|]. rewrite !u_small by lia.
      destruct (Z.lt_ge_cases x a) as [Hlt|Hge]; [left; exact Hlt|]. right.
      destruct (Z.lt_ge_cases x (a + Z.of_nat (length bs))) as [Hlt2|Hge2]; [|exact Hge2].
      exfalso. destruct Hp as [[_ [Hnb _]]|Hro].
      + apply Hnb. exists (A, n). split; [exact Hin|]. cbn [fst snd]. lia.
      + apply (dl_ro L sp0 DL) in Hro. pose proof Hsp. lia.
    - intros x Hx. exact (wbytes_grows bs M (Z_to_bv 64 a) x Hx).
  Qed.


  (* [comment removed for export] *)
  Definition CPout (A n : Z) (a : Z) : Prop := ~ (A <= a < A + n).

  Lemma regions_blockwrite : forall vals ebs A n,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 -> hz A n ->
    (forall i, In i [3%nat; 4%nat] -> bv_unsigned sp0 <= bv_unsigned (vals_ev vals i) /\ bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64) ->
    regions_ok RSEGS 0 0 0 [] [] [3%nat; 4%nat] IMG_CLIENT IMG_RW E (CPout A n) (fun _ => False).
  Proof.
    intros vals ebs A n E P0 (Z1 & Z2 & Z3) Hhi. pose proof Hsp as Hsp'.
    constructor; cbn [ev E]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold CPout. lia.
    - intros z Hz. exfalso. lia.
    - intros i nb Hf. discriminate.
    - intros v b Hf. discriminate.
    - intros i Hi. destruct (Hhi i Hi) as [H1 H2]. split; [exact H1|]. split; [exact H2|]. intros z Hz. unfold CPout. lia.
    - intros lo hi Hin. unfold IMG_CLIENT in Hin.
      destruct Hin as [E1|[E1|[E1|[]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros a Ha; unfold CPout; lia.
    - intros lo hi Hin. unfold IMG_RW in Hin.
      destruct Hin as [E1|[E1|[]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros Mx d m Hd Hm.
      + eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xc4000) _ 28672%nat m 0xc4000 0xcb000);
          [reflexivity | reflexivity | lia | exact wseg_c0000 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
      + eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xcb000) _ 208896%nat m 0xcb000 0xfe000);
          [reflexivity | reflexivity | lia | exact wseg_c7000 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
  Qed.

  Lemma know_blockwrite : forall vals ebs M (A n a : Z) bs kn,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 -> hz A n -> A <= a -> a + Z.of_nat (length bs) <= A + n ->
    (forall i, In i [3%nat; 4%nat] -> bv_unsigned sp0 <= bv_unsigned (vals_ev vals i) /\ bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64) ->
    know_ok RSEGS E M kn ->
    know_ok RSEGS E (wbytes M (Z_to_bv 64 a) bs) (kn_keep_g 0 0 0 [] [] [3%nat; 4%nat] IMG_CLIENT IMG_RW kn).
  Proof.
    intros vals ebs M A n a bs kn E P0 HZ Ha Hbs Hhi HK. pose proof HZ as (Z1 & Z2 & Z3). pose proof Hsp as Hsp'.
    eapply (know_keep_g_sound RSEGS 0 0 0 [] [] [3%nat; 4%nat] IMG_CLIENT IMG_RW E (CPout A n) (fun _ => False)
              (regions_blockwrite vals ebs A n P0 HZ Hhi) M).
    - intros x Hx Hout. unfold CPout in Hout. apply wbytes_out; rewrite ?u_small by lia; [lia|lia].
    - intros x [].
    - apply wbytes_grows.
    - exact HK.
  Qed.

  Lemma vals_ev_junk : forall vals R' i, (i < 32)%nat ->
    vals_ev (vals ++ junk_vals R') (length vals + i) = getr R' (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros vals R' i Hi. rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite nth_map_seq by exact Hi. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma malloc_site : forall vals ebs sr kn R M (model : Model) LB cr n so bls vbnd (ra : Z) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok RSEGS E M kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true ->
    (5 <= length vals)%nat ->
    vals_ev vals 0 = sp0 ->
    (forall i, In i [3%nat; 4%nat] -> bv_unsigned sp0 <= bv_unsigned (vals_ev vals i) /\ bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64) ->
    has_window kn = true ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
    getr R 10 = Z_to_bv 64 n -> 0 < n <= 2 ^ 27 -> credit_ok L cr n ->
    getr R 4 = Z_to_bv 64 0xdd010 -> getr R 1 = Z_to_bv 64 ra -> (0 <= ra < 2 ^ 64)%Z -> (ra mod 2 = 0)%Z ->
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_block LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    K [] ->
    (forall R' M' (model' : Model) (A : Z),
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       vals_ev vals' (length vals + 10) = Z_to_bv 64 A ->
       regs_ok E' (sr_after_call_j sr (map ridx c_kept) (length vals)) R' ->
       know_ok RSEGS E' M' (kn_blk (length vals + 10) n ++ keep_alloc so bls vbnd kn) ->
       hi_heap HI ((A, n) :: LB) (debit L cr n) M' (m_vmmaps model') ->
       model_but_vm model model' -> block_range L A n -> blocks_apart A n LB ->
       (forall x : word, bv_unsigned sp0 <= bv_unsigned x -> M' x = M x) ->
       (forall a, 0 <= a < 2 ^ 64 -> in_block LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall a, 0x10000 <= a < 0xfe000 -> ~ (0xfd418 <= a < 0xfd7c0) -> ~ (0xdcf6c <= a < 0xdcf70) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       srealizes RSEGS scfg (mkCfg (mkst R' (Z_to_bv 64 ra) M' (seg_rom RSEGS)) model') K) ->
    srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xaf8f8) M (seg_rom RSEGS)) model) K.
  Proof.
    intros vals ebs sr kn R M model LB cr n so bls vbnd ra K E HR HK Hsv Hkv HL5 P0 Hhi Hiw
           R2 Hso Hsoal R10 Hn Hcr R4 R1 Hra Hra2 HH Hh Hlz Hmt Hbl Hvb HK0 CONT.
    pose proof (hio_malloc L scfg HI HIok fx R M model LB cr n K) as MS.
    rewrite (dl_segs L sp0 DL), (dl_malloc L sp0 DL), (dl_tp L sp0 DL) in MS.
    rewrite R1 in MS.
    apply MS; clear MS; try assumption.
    - (* [comment removed for export] *) apply ret_ok_even. rewrite u_small by lia. exact Hra2.
    - (* [comment removed for export] *) rewrite R2, u_small by lia. eapply stack_ok_of_window; eassumption.
    - intros R' M' model' A HA HP HBR HAP HDEF HPRES HBUT HH'.
      assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
      assert (HA' : vals_ev (vals ++ junk_vals R') (length vals + 10) = Z_to_bv 64 A).
      { rewrite vals_ev_junk by lia. exact HA. }
      assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0).
      { rewrite vals_ev_app_l by lia. exact P0. }
      apply (CONT R' M' model' A HL' HA').
      + (* [comment removed for export] *) apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_kept R R' HP) c_kept_no0).
      + (* [comment removed for export] *) apply Forall_app. split.
        * eapply kn_blk_ok; [exact HA' | exact P0' | exact HBR | exact HDEF].
        * unfold keep_alloc.
          pose proof (env_app_know RSEGS vals (junk_vals R') ebs M kn Hkv HK) as HK1.
          destruct HPRES as (PR1 & PR2).
          eapply (know_keep_sound RSEGS 0 so 16384 bls vbnd [3%nat; 4%nat] IMG_CLIENT IMG_RW
                    (Env (vals_ev (vals ++ junk_vals R')) ebs) (CPm LB (bv_unsigned sp0 + so)) (SCm (bv_unsigned sp0 + so))).
          -- apply regions_alloc; try assumption.
             ++ intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1).
                rewrite vals_ev_app_l by exact Hi32. exact H1.
             ++ intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
             ++ intros i Hi. rewrite vals_ev_app_l; [apply Hhi; exact Hi|]. destruct Hi as [<-|[<-|[]]]; lia.
          -- intros a Ha [HC HE]. rewrite R2, u_small in PR1 by lia. apply PR1; assumption.
          -- intros a HS. rewrite R2, u_small in PR2 by lia. apply PR2. exact HS.
          -- exact HK1.
      + exact HH'.
      + exact HBUT.
      + exact HBR.
      + exact HAP.
      + intros x Hx. destruct HPRES as (PR1 & _). rewrite R2, u_small in PR1 by lia.
        rewrite <- (Z_to_bv_bv_unsigned 64 x). apply PR1.
        * pose proof (u64_range x). lia.
        * unfold client_addr. right. left. rewrite (dl_sptop L sp0 DL).
          pose proof (u64_range x). pose proof (dl_stack L sp0 DL). lia.
        * unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
      + intros a Ha Hb. destruct HPRES as (PR1 & _). rewrite R2, u_small in PR1 by lia. apply PR1; [exact Ha | left; exact Hb |].
        destruct Hb as (b & Hbin & Hr). destruct (hio_wf L scfg HI HIok LB cr M (m_vmmaps model) HH) as [WF _].
        destruct (WF b Hbin) as (HBRb & _ & _). pose proof (hz_of_block_range _ _ HBRb) as (Y1 & Y2 & Y3).
        unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
      + intros a Ha Hs He. destruct HPRES as (PR1 & _). rewrite R2, u_small in PR1 by lia. apply PR1; [lia | |].
        * unfold client_addr. right. right. rewrite (dl_img_lo L sp0 DL), (dl_img_hi L sp0 DL). split; [lia|].
          intros Hst. apply (dl_static L sp0 DL) in Hst. lia.
        * unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma free_site : forall vals ebs sr kn R M (model : Model) LB cr (A n : Z) so bls vbnd (ra : Z) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok RSEGS E M kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true ->
    (5 <= length vals)%nat ->
    vals_ev vals 0 = sp0 ->
    (forall i, In i [3%nat; 4%nat] -> bv_unsigned sp0 <= bv_unsigned (vals_ev vals i) /\ bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64) ->
    has_window kn = true ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
    In (A, n) LB -> getr R 10 = Z_to_bv 64 A ->
    getr R 4 = Z_to_bv 64 0xdd010 -> getr R 1 = Z_to_bv 64 ra -> (0 <= ra < 2 ^ 64)%Z -> (ra mod 2 = 0)%Z ->
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_block (lb_remove A LB) (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    K [] ->
    (forall R' M' (model' : Model),
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       regs_ok E' (sr_after_call_j sr (map ridx c_kept) (length vals)) R' ->
       know_ok RSEGS E' M' (keep_alloc so bls vbnd kn) ->
       hi_heap HI (lb_remove A LB) cr M' (m_vmmaps model') ->
       model_but_vm model model' ->
       (forall x : word, bv_unsigned sp0 <= bv_unsigned x -> M' x = M x) ->
       (forall a, 0 <= a < 2 ^ 64 -> in_block (lb_remove A LB) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall a, 0x10000 <= a < 0xfe000 -> ~ (0xfd418 <= a < 0xfd7c0) -> ~ (0xdcf6c <= a < 0xdcf70) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       srealizes RSEGS scfg (mkCfg (mkst R' (Z_to_bv 64 ra) M' (seg_rom RSEGS)) model') K) ->
    srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xaf7b8) M (seg_rom RSEGS)) model) K.
  Proof.
    intros vals ebs sr kn R M model LB cr A n so bls vbnd ra K E HR HK Hsv Hkv HL5 P0 Hhi Hiw
           R2 Hso Hsoal Hin R10 R4 R1 Hra Hra2 HH Hh Hlz Hmt Hbl Hvb HK0 CONT.
    pose proof (hio_free L scfg HI HIok fx R M model LB cr A n K) as MS.
    rewrite (dl_segs L sp0 DL), (dl_free L sp0 DL), (dl_tp L sp0 DL) in MS.
    rewrite R1 in MS.
    apply MS; clear MS; try assumption.
    - (* [comment removed for export] *) apply ret_ok_even. rewrite u_small by lia. exact Hra2.
    - (* [comment removed for export] *) rewrite R2, u_small by lia. eapply stack_ok_of_window; eassumption.
    - intros R' M' model' HP HPRES HBUT HH'.
      assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
      assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0).
      { rewrite vals_ev_app_l by lia. exact P0. }
      apply (CONT R' M' model' HL').
      + apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_kept R R' HP) c_kept_no0).
      + unfold keep_alloc.
        pose proof (env_app_know RSEGS vals (junk_vals R') ebs M kn Hkv HK) as HK1.
        destruct HPRES as [[PR1 PR2] _].
        eapply (know_keep_sound RSEGS 0 so 16384 bls vbnd [3%nat; 4%nat] IMG_CLIENT IMG_RW
                  (Env (vals_ev (vals ++ junk_vals R')) ebs) (CPm (lb_remove A LB) (bv_unsigned sp0 + so)) (SCm (bv_unsigned sp0 + so))).
        * apply regions_alloc; try assumption.
          -- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1).
             rewrite vals_ev_app_l by exact Hi32. exact H1.
          -- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
          -- intros i Hi. rewrite vals_ev_app_l; [apply Hhi; exact Hi|]. destruct Hi as [<-|[<-|[]]]; lia.
        * intros a Ha [HC HE]. rewrite R2, u_small in PR1 by lia. apply PR1; assumption.
        * intros a HS. rewrite R2, u_small in PR2 by lia. apply PR2. exact HS.
        * exact HK1.
      + exact HH'.
      + exact HBUT.
      + intros x Hx. destruct HPRES as [[PR1 _] _]. rewrite R2, u_small in PR1 by lia.
        rewrite <- (Z_to_bv_bv_unsigned 64 x). apply PR1.
        * pose proof (u64_range x). lia.
        * unfold client_addr. right. left. rewrite (dl_sptop L sp0 DL).
          pose proof (u64_range x). pose proof (dl_stack L sp0 DL). lia.
        * unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
      + intros a Ha Hb. destruct HPRES as [[PR1 _] _]. rewrite R2, u_small in PR1 by lia. apply PR1; [exact Ha | left; exact Hb |].
        destruct Hb as (b & Hbin & Hr).
        assert (Hbin' : In b LB).
        { clear -Hbin. induction LB as [|c LB' IH]; [destruct Hbin|]. cbn [lb_remove] in Hbin.
          destruct (Z.eqb (fst c) A); [right; exact Hbin|]. destruct Hbin as [<-|Hbin]; [left; reflexivity | right; apply IH; exact Hbin]. }
        destruct (hio_wf L scfg HI HIok LB cr M (m_vmmaps model) HH) as [WF _].
        destruct (WF b Hbin') as (HBRb & _ & _). pose proof (hz_of_block_range _ _ HBRb) as (Y1 & Y2 & Y3).
        unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
      + intros a Ha Hs He. destruct HPRES as [[PR1 _] _]. rewrite R2, u_small in PR1 by lia. apply PR1; [lia | |].
        * unfold client_addr. right. right. rewrite (dl_img_lo L sp0 DL), (dl_img_hi L sp0 DL). split; [lia|].
          intros Hst. apply (dl_static L sp0 DL) in Hst. lia.
        * unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
  Qed.
End DrvLayout.
End FPX_1.
