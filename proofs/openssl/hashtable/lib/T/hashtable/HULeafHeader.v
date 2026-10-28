(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Spec LibWritev RefNodes HUExitBase HUStdioDefs HUExit HULibStdioCall RefMemcpyLib HUReadBase Hoare LibMaskBits StreamSim HUWorld HUTargetPre.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require HUHeader_defs PhaseG ExistsRun.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Spec HUReadBase HUWorld HUTargetPre.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)

(* [comment removed for export] *)
Module H0Header.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PhaseG.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PropExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SeqExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StoreOk OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ShapeAlg OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Nodes ShapeLaws OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SpecConsts OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MmapSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.AllocSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FileSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.AgentLib OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2 OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2Sound OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymRun OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDrive OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDriveX Spec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibWritev OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefNodes HUExitBase HUStdioDefs HUExit HULibStdioCall OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefMemcpyLib HUReadBase OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Hoare OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibMaskBits OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StreamSim HUWorld HUTargetPre.
Import HUHeader_defs.
Import ConeCfg.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import ConeCfg.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUELh STOPSh scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUELh STOPSh scr NX true.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hdr_img_ranges : list (Z * Z) :=
  [(0x10000,0x31eec0); (0x31eec1,0x31ef09); (0x32ef09,0x331a18); (0x351af0,0x351b10); (0x331a4c,0x331a98); (0x331aa0,0x331ab8); (0x331ac0,0x331ad8); (0x331ae8,0x331af8); (0x331b00,0x351af0); (0x351b30,0x351d68); (0x351d79,0x351d80); (0x351d88,0x351d90); (0x351da0,0x351da8); (0x351db0,0x351de0); (0x351de8,0x351df0); (0x351e40,0x351fa0); (0x351fa8,0x352120); (0x352128,0x352180); (0x352181,0x352188); (0x352190,0x354000)]%Z.

(* [comment removed for export] *)
Record header_pre (sp0 p1 gm tid : word) (area can sec : Z) (content : list byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := HDR_PRE {
  (* [comment removed for export] *)
  hp_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
  hp_gp : getr R 3 = Z_to_bv 64 0x10800;
  hp_tp : getr R 4 = Z_to_bv 64 0x331ae8;
  hp_s0 : getr R 8 = Z_to_bv 64 2;
  hp_s1 : getr R 9 = Z_to_bv 64 (bv_unsigned gm + 32);
  hp_s2 : getr R 18 = p1;
  hp_s3 : getr R 19 = Z_to_bv 64 (Z.of_nat (length content));
  hp_s4 : getr R 20 = Z_to_bv 64 3;
  hp_s5 : getr R 21 = Z_to_bv 64 65536;
  hp_s6 : getr R 22 = Z_to_bv 64 0x31ef09;                 (* [comment removed for export] *)
  hp_s7 : getr R 23 = Z_to_bv 64 0;
  (* [comment removed for export] *)
  hp_sp0 : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z /\ (bv_unsigned sp0 mod 16 = 0)%Z;
  hp_gm  : (0x354000 <= bv_unsigned gm)%Z /\ (bv_unsigned gm + 69632 <= bv_unsigned sp0 - 8388608)%Z
           /\ (bv_unsigned gm mod 4096 = 0)%Z;
  hp_area : (0x2000 <= area)%Z /\ (area + 4096 <= bv_unsigned sp0 - 8388608)%Z /\ (area mod 4096 = 0)%Z;
  hp_area_img : (area + 4096 <= 0x10000 \/ 0x355000 <= area)%Z;   (* [comment removed for export] *)
  hp_disj : (area + 4096 <= bv_unsigned gm \/ bv_unsigned gm + 69632 <= area)%Z;
  hp_tid : (0 < bv_unsigned tid < 2 ^ 22)%Z;
  hp_L   : (Z.of_nat (length content) < 65536)%Z;
  (* [comment removed for export] *)
  hp_stack : stack_writable M sp0;
  hp_ra   : cell M (bv_unsigned sp0 - 56) 8 0x2b1158;
  hp_f64  : cell M (bv_unsigned sp0 - 64) 8 (bv_unsigned sp0 + 8);
  hp_f72  : cell M (bv_unsigned sp0 - 72) 8 2;
  hp_f80  : cell M (bv_unsigned sp0 - 80) 8 0xe1984;
  hp_f88  : cell M (bv_unsigned sp0 - 88) 8 (bv_unsigned sp0 + 32);
  hp_f96  : cell M (bv_unsigned sp0 - 96) 8 0;
  hp_f104 : cell M (bv_unsigned sp0 - 104) 8 0;
  hp_f112 : cell M (bv_unsigned sp0 - 112) 8 0;
  hp_f120 : cell M (bv_unsigned sp0 - 120) 8 0;
  (* [comment removed for export] *)
  hp_group : group_writable M gm;
  hp_gmeta : cell M (bv_unsigned gm) 8 (area + 24);
  hp_pm4   : M (Z_to_bv 64 (bv_unsigned gm + 28)) = Some (Z_to_bv 8 0);
  hp_pm3   : M (Z_to_bv 64 (bv_unsigned gm + 29)) = Some (Z_to_bv 8 160);
  hp_pm2   : cell M (bv_unsigned gm + 30) 2 1;
  hp_gzr   : M (Z_to_bv 64 (bv_unsigned gm + 65568)) = Some (Z_to_bv 8 0);
  hp_ge5   : M (Z_to_bv 64 (bv_unsigned gm + 69623)) = Some (Z_to_bv 8 0);
  hp_ge4   : cell M (bv_unsigned gm + 69624) 4 0xfdc;
  hp_gend  : zero_bytes M (bv_unsigned gm + 69628) 4;
  hp_content : rdn RSEGS M (Z_to_bv 64 (bv_unsigned gm + 32)) (length content) = Some content;
  (* [comment removed for export] *)
  hp_marea : forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= 4096)%Z ->
               store_ok RSEGS M (Z_to_bv 64 (area + d)) m = true;
  hp_check : cell M area 8 sec;
  hp_gprev : cell M (area + 24) 8 (area + 24);
  hp_gnext : cell M (area + 32) 8 (area + 24);
  hp_gmem  : cell M (area + 40) 8 (bv_unsigned gm);
  hp_gavail : cell M (area + 48) 4 0;
  hp_gfreed : cell M (area + 52) 4 0;
  hp_gW    : cell M (area + 56) 8 0x11b20;
  (* [comment removed for export] *)
  hp_secret : cell M 0x351df0 8 sec;
  hp_fmh    : cell M 0x351e00 8 0;
  hp_active : cell M 0x351fa0 8 (area + 24);
  hp_usage  : cell M 0x352120 8 1;
  hp_seq    : cell M 0x352180 1 1;
  hp_tidc   : cell M 0x331a40 4 (bv_unsigned tid);
  hp_errno  : exists e, (0 <= e < 2 ^ 32)%Z /\ cell M 0x331a44 4 e;
  hp_guard  : cell M 0x351b28 8 can;
  hp_canr   : (0 <= can < 2 ^ 64)%Z;
  hp_secr   : (0 <= sec < 2 ^ 64)%Z;
  hp_img    : forall lo hi i, In (lo, hi) hdr_img_ranges -> (lo <= i < hi)%Z -> M (Z_to_bv 64 i) = None
}.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma data_wseg : wseg_ok RSEGS (Z_to_bv 64 0x31e000) 221184 = true.
Proof. replace (Z_to_bv 64 0x31e000) with (0x31e000 : word) by (apply bv_eq; reflexivity). exact ref_wseg_1c. Qed.  (* [comment removed for export] *)

Lemma data_store_ok : forall M d m, (0 <= d)%Z -> (d + Z.of_nat m <= 0x36000)%Z ->
  store_ok RSEGS M (Z_to_bv 64 (0x31e000 + d)) m = true.
Proof.
  intros M d m Hd Hm.
  eapply (store_ok_window RSEGS M (Z_to_bv 64 0x31e000) _ 221184 m 0x31e000 0x354000);
    [reflexivity | reflexivity | cbn; lia | apply data_wseg | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Header.
  Variables (sp0 p1 gm tid : word) (area can sec : Z) (content : list byte).
  Variables (VM : VmMaps) (stdin0 : AmbIn) (fs0 : Fs).
  Variables (R0 : bvmap 5 word) (M0 : word -> option byte).
  Hypothesis HP : header_pre sp0 p1 gm tid area can sec content R0 M0.
  Hypothesis Hmap : map_has (vm_maps VM) gm (Z_to_bv 64 69632) = true.

  Let L : Z := Z.of_nat (length content).
  Definition modelh : Model := model_post VM stdin0 fs0 tid.
  #[local] Notation ENVv := (ENVh content) (only parsing).

  (* [comment removed for export] *)
  Definition valsh (e : Z) : list word :=
    [sp0; p1; Z_to_bv 64 area; gm; tid; Z_to_bv 64 L; Z_to_bv 64 (hdr_b0 content); Z_to_bv 64 (hdr_b1 content);
     Z_to_bv 64 e; Z_to_bv 64 can; Z_to_bv 64 sec] ++ junk_vals R0.

  (* [comment removed for export] *)
  Lemma w2le1_byte : forall (x : byte), word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned x)) = [x].
  Proof.
    intros x. pose proof (bv_unsigned_in_range _ x) as Hx. change (bv_modulus 8) with 256%Z in Hx.
    unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal.
    rewrite u_small by lia. apply Z_to_bv_bv_unsigned.
  Qed.

  (* [comment removed for export] *)
  Lemma hdr_sym : exists e, (0 <= e < 2 ^ 32)%Z /\
    regs_ok (ENVh content (valsh e)) sr_H R0 /\ know_ok RSEGS (ENVh content (valsh e)) M0 kn_H.
  Proof.
    destruct HP as [Rsp Rgp Rtp Rs0 Rs1 Rs2 Rs3 Rs4 Rs5 Rs6 Rs7 Hsp Hgm Har Hai Hdj Htid HL Hst
                    Hra Hf64 Hf72 Hf80 Hf88 Hf96 Hf104 Hf112 Hf120
                    Hgr Hgmeta Hpm4 Hpm3 Hpm2 Hgzr Hge5 Hge4 Hgend Hcont Hma Hck Hgp Hgn Hgmm Hgav Hgfr HgW
                    Hsec Hfmh Hact Hus Hseq Htc (e & He & Herr') Hgd Hcanr Hsecr Himg].
    exists e. split; [exact He|].
    set (vals := valsh e). set (E := ENVh content vals).
    assert (E0 : ev E 0 = sp0) by reflexivity.
    assert (E1 : ev E 1 = p1) by reflexivity.
    assert (E2 : ev E 2 = Z_to_bv 64 area) by reflexivity.
    assert (E3 : ev E 3 = gm) by reflexivity.
    assert (E4 : ev E 4 = tid) by reflexivity.
    assert (E5 : ev E 5 = Z_to_bv 64 L) by reflexivity.
    assert (E8 : ev E 8 = Z_to_bv 64 e) by reflexivity.
    assert (E9 : ev E 9 = Z_to_bv 64 can) by reflexivity.
    assert (E10 : ev E 10 = Z_to_bv 64 sec) by reflexivity.
    assert (EJ : forall i, (i < 32)%nat -> ev E (11 + i) = getr R0 (Z_to_bv 5 (Z.of_nat i))).
    { intros i Hi. unfold E, ENVh, vals, valsh. cbn [ev]. unfold vals_ev.
      change (11 + i)%nat with (length [sp0; p1; Z_to_bv 64 area; gm; tid; Z_to_bv 64 L; Z_to_bv 64 (hdr_b0 content);
                                        Z_to_bv 64 (hdr_b1 content); Z_to_bv 64 e; Z_to_bv 64 can; Z_to_bv 64 sec] + i)%nat.
      rewrite app_nth2_plus. unfold junk_vals. rewrite (nth_map_seq (fun i => getr R0 (Z_to_bv 5 (Z.of_nat i)))) by exact Hi.
      reflexivity. }
    split.
    - (* [comment removed for export] *)
      apply HUReadBase.regs_ok_by_index. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
        cbn [nth sr_H HUReadBase.all_regs].
      all: try (lazymatch goal with |- _ = edenot _ (J ?n) =>
                  unfold J; change (edenot E (EVar (11 + n))) with (ev E (11 + n)%nat); rewrite EJ by lia; reflexivity end).
      all: try (lazymatch goal with |- _ = edenot _ (spx ?k) =>
                  unfold spx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot]; rewrite E0;
                  rewrite Rsp; f_equal; lia end).
      all: try (lazymatch goal with |- _ = edenot _ (gmx ?k) =>
                  unfold gmx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot]; rewrite E3;
                  assumption end).
      all: try (change (edenot E (EVar 1)) with (ev E 1); rewrite E1; assumption).
      all: try (change (edenot E (EVar 5)) with (ev E 5); rewrite E5; assumption).
      all: cbn [edenot]; first [assumption | apply getr_zero | reflexivity].
    - (* [comment removed for export] *)
      pose proof (proj1 Hsp) as Hspr. pose proof (proj2 Hsp) as Hspa.
      destruct Hgm as (Hgm1 & Hgm2 & Hgmal). destruct Har as (Har1 & Har2 & Haral).
      pose proof (u64_range gm) as Ugm. pose proof (u64_range sp0) as Usp. pose proof (u64_range tid) as Utid.
      assert (AX : forall k, (0 <= k <= 4096)%Z -> edenot E (ax k) = Z_to_bv 64 (area + k)).
      { intros k Hk. unfold ax. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite E2.
        rewrite u_small by lia. reflexivity. }
      assert (SPX : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k)).
      { intros k. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite E0. reflexivity. }
      assert (AREA : edenot E area_x = Z_to_bv 64 area).
      { unfold area_x. cbn [edenot]. rewrite AX by lia. rewrite alu_and. unfold v_and.
        rewrite !u_small by lia. rewrite land_pagemask by lia.
        rewrite <- Zplus_mod_idemp_l, Haral. change ((0 + 24) mod 4096)%Z with 24%Z. f_equal. lia. }
      unfold kn_H, kn_Hstack, kn_Hheap, kn_Himage, know_ok. cbn [app].
      repeat apply Forall_cons; try apply Forall_nil.
      all: cbn [kentry_ok]; unfold flat, estart, elenZ, adenot, v_addi; cbn [a_base a_off];
           rewrite ?AREA; rewrite ?AX by lia; rewrite ?SPX; cbn [edenot]; rewrite ?E0, ?E1, ?E2, ?E3, ?E4, ?E5, ?E8, ?E9, ?E10;
           rewrite ?(u_small area) by lia; rewrite ?Z.add_0_r;
           change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; rewrite ?Z.add_0_l.
      (* [comment removed for export] *)
      all: try (split; [lia | first [exact Hspa | exact Haral | exact Hgmal]]; fail).
      all: lazymatch goal with
           (* [comment removed for export] *)
           | |- (_ <= _ <= _)%Z => lia
           | |- (_ <= _)%Z \/ (_ <= _)%Z => lia
           (* [comment removed for export] *)
           | |- (0 <= _)%Z /\ (_ <= 2 ^ 64)%Z /\ (forall i, _ -> M0 (Z_to_bv 64 i) = None) =>
               split; [lia|]; split; [lia|]; intros i Hi; (eapply Himg; [ | exact Hi]);
               cbn; repeat (first [left; reflexivity | right])
           | |- _ => idtac
           end.
      (* [comment removed for export] *)
      all: try (lazymatch goal with
                | |- _ /\ (forall d m, _ -> _ -> store_ok _ _ (Z_to_bv 64 (?B + d)) m = true) =>
                    split; [lia|]; intros d m Hd Hm;
                    first [ replace (B + d)%Z with (bv_unsigned sp0 - 8388608 + d)%Z by lia; apply Hst; lia
                          | replace (B + d)%Z with (bv_unsigned gm + d)%Z by lia; apply Hgr; lia
                          | apply Hma; lia
                          | replace (B + d)%Z with (0x31e000 + d)%Z by lia; apply data_store_ok; lia ]
                end).
      (* [comment removed for export] *)
      all: try (lazymatch goal with
                | |- _ /\ (forall i, _ -> M0 _ = Some (Z_to_bv 8 0)) =>
                    split; [rewrite ?u_small by lia; lia|]; intros i Hi; rewrite ?u_small in Hi by lia;
                    apply Hgend; lia
                end).
      (* [comment removed for export] *)
      all: try (lazymatch goal with
                | |- _ /\ _ /\ rdn _ _ _ 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 _)) =>
                    split; [lia|]; split; [lia|]; cbn [rdn];
                    first [rewrite Hgzr | rewrite Hge5 | rewrite Hpm4 | rewrite Hpm3]; reflexivity
                end).
      (* [comment removed for export] *)
      all: try (lazymatch goal with
                | |- _ /\ _ /\ rdn _ _ (Z_to_bv 64 ?A) _ = _ =>
                    split; [lia|]; split; [lia|]; unfold cell in *; rewrite ?Z_to_bv_bv_unsigned in *;
                    let try1 H := (lazymatch type of H with rdn _ _ (Z_to_bv 64 ?A2) _ = _ =>
                                     replace A with A2 by lia; exact H end) in
                    first [ exact Hgmeta | try1 Hpm2 | try1 Hra | try1 Hf64 | try1 Hf72 | try1 Hf80 | try1 Hf88 | try1 Hf96 | try1 Hf104 | try1 Hf112 | try1 Hf120 | try1 Hf120
                          | try1 Hgmeta | try1 Hghdr | try1 Hge4 | try1 Hck | try1 Hgp | try1 Hgn | try1 Hgmm
                          | try1 Hgav | try1 Hgfr | try1 HgW | try1 Hsec | try1 Hfmh | try1 Hact | try1 Hus | try1 Hseq
                          | try1 Htc | try1 Herr' | try1 Hgd ]
                end).
  Qed.

  (* [comment removed for export] *)
  Lemma hdr_know_short : forall e, know_ok RSEGS (ENVh content (valsh e)) M0 kn_H ->
    (length content < 6)%nat -> know_ok RSEGS (ENVh content (valsh e)) M0 kn_short.
  Proof.
    intros e HK Hlt. unfold kn_short. apply know_ok_app. split; [exact HK|].
    apply know_ok_cons; [|constructor]. apply krange_intro.
    change (edenot (ENVh content (valsh e)) (EVar 5)) with (Z_to_bv 64 L). unfold L. rewrite u_small by lia. lia.
  Qed.

  Lemma content_byte : forall j, (j < length content)%nat ->
    rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned gm + 32 + Z.of_nat j)) 1%nat
    = Some (word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned (nth j content (Z_to_bv 8 0))))).
  Proof.
    intros j Hj. pose proof (hp_gm _ _ _ _ _ _ _ _ _ _ HP) as Hgm. pose proof (hp_L _ _ _ _ _ _ _ _ _ _ HP) as HL. pose proof (hp_sp0 _ _ _ _ _ _ _ _ _ _ HP) as Hsp00.
    pose proof (hp_content _ _ _ _ _ _ _ _ _ _ HP) as Hcont.
    pose proof (rdn_nth RSEGS M0 (length content) _ content j Hcont Hj) as H.
    rewrite w_add_nat in H. rewrite u_small in H by lia. rewrite w2le1_byte. exact H.
  Qed.

  Lemma hdr_know_long : forall e, know_ok RSEGS (ENVh content (valsh e)) M0 kn_H ->
    (6 <= length content)%nat -> know_ok RSEGS (ENVh content (valsh e)) M0 kn_long.
  Proof.
    intros e HK Hge. pose proof (hp_gm _ _ _ _ _ _ _ _ _ _ HP) as Hgm. pose proof (hp_L _ _ _ _ _ _ _ _ _ _ HP) as HL. pose proof (hp_sp0 _ _ _ _ _ _ _ _ _ _ HP) as Hsp00.
    pose proof (hp_content _ _ _ _ _ _ _ _ _ _ HP) as Hcont.
    pose proof (u64_range gm) as Ugm.
    pose proof (bv_unsigned_in_range _ (nth 0 content (Z_to_bv 8 0))) as B0.
    pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1.
    change (bv_modulus 8) with 256%Z in B0, B1.
    unfold kn_long. apply know_ok_app. split; [exact HK|].
    apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|constructor]]]]].
    - apply krange_intro. change (edenot (ENVh content (valsh e)) (EVar 5)) with (Z_to_bv 64 L). unfold L. rewrite u_small by lia. lia.
    - cbn [kentry_ok]. split; [lia|]. split; [apply flat_intro; cbn [edenot ev ENVh valsh vals_ev nth app]; lia|].
      unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev (ENVh content (valsh e)) 3) with gm.
      change (ev (ENVh content (valsh e)) 6) with (Z_to_bv 64 (hdr_b0 content)). unfold hdr_b0.
      replace (bv_unsigned gm + 32)%Z with (bv_unsigned gm + 32 + Z.of_nat 0)%Z by lia. apply content_byte. lia.
    - cbn [kentry_ok]. split; [lia|]. split; [apply flat_intro; cbn [edenot ev ENVh valsh vals_ev nth app]; lia|].
      unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev (ENVh content (valsh e)) 3) with gm.
      change (ev (ENVh content (valsh e)) 7) with (Z_to_bv 64 (hdr_b1 content)). unfold hdr_b1.
      replace (bv_unsigned gm + 33)%Z with (bv_unsigned gm + 32 + Z.of_nat 1)%Z by lia. apply content_byte. lia.
    - apply krange_intro. change (edenot (ENVh content (valsh e)) (EVar 6)) with (Z_to_bv 64 (hdr_b0 content)). unfold hdr_b0.
      rewrite u_small by lia. lia.
    - apply krange_intro. change (edenot (ENVh content (valsh e)) (EVar 7)) with (Z_to_bv 64 (hdr_b1 content)). unfold hdr_b1.
      rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma fds_std_2 : fd_lookup fds_std (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. reflexivity. Qed.

  Lemma msg_short_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x3645f) 31 = Some msg_short.
  Proof. vm_compute. reflexivity. Qed.
  Lemma msg_overrun_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x1bca2) 31 = Some msg_overrun.
  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma hp_facts :
    ((0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z /\ (bv_unsigned sp0 mod 16 = 0)%Z)
    /\ ((0x354000 <= bv_unsigned gm)%Z /\ (bv_unsigned gm + 69632 <= bv_unsigned sp0 - 8388608)%Z /\ (bv_unsigned gm mod 4096 = 0)%Z)
    /\ (0 < bv_unsigned tid < 2 ^ 22)%Z /\ (Z.of_nat (length content) < 65536)%Z.
  Proof.
    split; [exact (hp_sp0 _ _ _ _ _ _ _ _ _ _ HP)|]. split; [exact (hp_gm _ _ _ _ _ _ _ _ _ _ HP)|].
    split; [exact (hp_tid _ _ _ _ _ _ _ _ _ _ HP) | exact (hp_L _ _ _ _ _ _ _ _ _ _ HP)].
  Qed.

  (* [comment removed for export] *)
  Definition err_tail_stmt (sr : list expr) (kn : list kentry) : Prop :=
    forall vals R M,
      length vals = 75%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 3 = gm -> vals_ev vals 4 = tid ->
      regs_ok (ENVh content vals) sr R -> know_ok RSEGS (ENVh content vals) M kn ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2b5f50) M (seg_rom RSEGS)) modelh)
                 (t_exit (exit_code 2) fs0).

  Ltac err_tail_1 HL P0 P3 P4 HR HK :=
    pose proof hp_facts as ((SP & SPA) & (GM1 & GM2 & GMA) & TID & LL);
    pose proof (u64_range gm) as Ugm;
    (* [comment removed for export] *)
    run_block scr0 75%nat;
    (* [comment removed for export] *)
    eapply (rz_munmap RSEGS _ _ _ modelh ECALLW gm 69632);
    [ vm_compute; reflexivity
    | apply is_ecall_ECALLW
    | reflexivity
    | reflexivity
    | regv HR (17 : reg); reflexivity
    | regv HR (10 : reg); cbn [edenot ev ENVh]; exact P3
    | exact GMA
    | regv HR (11 : reg); reflexivity
    | lia
    | change (page_round_up_Z 69632) with 69632%Z; unfold TASK_SIZE; lia
    | change (page_round_up_Z 69632) with 69632%Z; cbv [m_vmmaps modelh model_post mkModelA m_vm vmst_maps]; exact Hmap
    | ];
    rewrite v_addi_pc4 by lia; change (0x2b3f8c + 4)%Z with 0x2b3f90%Z;
    change (page_round_up_Z 69632) with 69632%Z.

  Ltac err_tail_2 HL P0 P3 P4 HR HK :=
    let HK2 := fresh "HK2" in let HR2 := fresh "HR2" in
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ ?E ?Mc ?kn =>
      pose proof (know_ok_unfill RSEGS E Mc kn (EVar 3) 0 69632 HK
                    ltac:(apply flat_intro; cbn [edenot ev ENVh]; rewrite ?P3; lia) ltac:(lia)) as HK2;
      let kn' := eval vm_compute in (kn_unfill kn (EVar 3) 0 69632) in
      change (kn_unfill kn (EVar 3) 0 69632) with kn' in HK2
    end;
    unfold adenot, v_addi in HK2; cbn [a_base a_off edenot ev ENVh] in HK2;
    rewrite P3, Z.add_0_r, Z_to_bv_bv_unsigned in HK2;
    clear HK; rename HK2 into HK;
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_set_a0 E sr Rc (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end;
    clear HR; rename HR2 into HR;
    (* [comment removed for export] *)
    run_block scr0 75%nat.

  Ltac err_tail_3 HL P0 P3 P4 HR HK :=
    let Hst := fresh "Hst" in let Ktid := fresh "Ktid" in
    (* [comment removed for export] *)
    apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255))
                                                  (m_fs (munmap_model gm (Z_to_bv 64 69632) modelh)))));
    [ | replace (m_fs (munmap_model gm (Z_to_bv 64 69632) modelh)) with fs0 by reflexivity;
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity);
        apply t_eq_sym; apply t_emit_nil_exit ];
    apply ref_exit_Z;
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_krange (EVar 4)) in exact i) _ HK eq_refl)
        as Ktid; cbn [kentry_ok edenot ev ENVh] in Ktid; rewrite P4 in Ktid
    end;
    exists (Z_to_bv 64 (bv_unsigned sp0 - 48)), (Z_to_bv 64 0x331ae8), (bv_unsigned tid),
           (Z_to_bv 64 0x3521c0), (Z_to_bv 64 0);
    split; [|split; [reflexivity|split; [reflexivity|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVh];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); reflexivity
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        lazymatch type of HK with know_ok _ ?E _ ?kn =>
          pose proof (kwr_store_ok RSEGS E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-192) 144) in exact i)
                        _ _ _ (-192) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst end;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENVh] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - 48 - 144)%Z with (bv_unsigned sp0 + -192)%Z by lia; exact Hst
      | lit_u; lia
      | lit_u; lia
      | lia
      | lit_u; change (3349224 - 168)%Z with 0x331a40%Z;
        let Htc := fresh in krd HK 0x331a40%Z 4%nat Htc; rewrite Htc; cbn [ev ENVh]; rewrite P4;
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
      | repeat split; krd_solve HK
      | repeat split; krd_solve HK ]
    | left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ].

  Ltac err_tail_tac :=
    intros vals R M HL P0 P3 P4 HR HK;
    err_tail_1 HL P0 P3 P4 HR HK;
    match goal with HR' : regs_ok _ _ _, HK' : know_ok _ _ _ _ |- _ => err_tail_2 HL P0 P3 P4 HR' HK' end;
    match goal with HR' : regs_ok _ _ _, HK' : know_ok _ _ _ _ |- _ => err_tail_3 HL P0 P3 P4 HR' HK' end.

  Lemma err_tail_short : err_tail_stmt srSB0 knSB0.
  Proof. err_tail_tac. Qed.

  Lemma err_tail_overrun : err_tail_stmt srOB0 knOB0.
  Proof. err_tail_tac. Qed.

  (* [comment removed for export] *)
  Ltac usmall_off := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 (bv_unsigned ?x + ?k))] => rewrite (u_small (bv_unsigned x + k)) by lia end.

  (* [comment removed for export] *)
  Ltac stdio_then_tail vals res msg msg_img msg_addr TAIL HL P0 P3 P4 HR HK :=
    lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
    unfold t_die, W;
    apply (stdio_call_sound vals (blobs_ev [content]) sr kn Rc Mc modelh res [] msg
             (t_exit (exit_code 2) fs0) HR HK (eq_trans (f_equal (fun n => stdio_call n sr kn) HL) ltac:(vm_compute; reflexivity)));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn res];
      try (replace (Z.of_nat (@length byte msg)) with 31%Z by reflexivity); cbn [length Z.of_nat];
    [ cbn [edenot]; lia
    | cbn [edenot]; rewrite ?u_small by lia; lia      (* [comment removed for export] *)
    | cbn [edenot]; lia
    | cbn [edenot]; lit_u; reflexivity
    | lia
    | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVh]; rewrite P0;
      usmall_off; rewrite ?u_small by lia; lia
    | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVh]; rewrite P0;
      usmall_off; rewrite ?u_small by lia; lia
    | cbn [edenot]; rewrite ?u_small by lia; lia
    | reflexivity
    | cbn [edenot]; replace (@length byte msg) with 31%nat by reflexivity;
      rewrite (kimg_rdn RSEGS (ENVh content vals) _ kn ltac:(let i := kidx kn (is_kimg_cov msg_addr 31) in exact i)
                 _ _ msg_addr 31 HK eq_refl) by (cbn; lia);
      apply msg_img
    | apply fds_std_2
    | reflexivity
    | reflexivity
    | apply t_exit_has_nil
    | clear HR HK;
      let R' := fresh "R" in let M' := fresh "M" in let HR' := fresh "HR" in let HK' := fresh "HK" in
      intros R' M' HR' HK';
      apply (TAIL (vals ++ junk_vals R') R' M');
      [ rewrite length_app, junk_vals_length, HL; reflexivity
      | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
      | rewrite vals_ev_app_l by (rewrite HL; lia); exact P3
      | rewrite vals_ev_app_l by (rewrite HL; lia); exact P4
      | exact HR' | exact HK' ] ]
    end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem header_short : (length content < 6)%nat ->
    realizes RSEGS (mkCfg (mkst R0 (Z_to_bv 64 0xe1aa0) M0 (seg_rom RSEGS)) modelh) (t_die msg_short fs0).
  Proof.
    intros Hlt. destruct hdr_sym as (e & He & HR & HK0).
    pose proof (hdr_know_short e HK0 Hlt) as HK. clear HK0.
    pose proof hp_facts as ((SP & SPA) & (GM1 & GM2 & GMA) & TID & LL).
    set (vals := valsh e) in *.
    assert (HL : length vals = 43%nat) by (subst vals; unfold valsh; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = tid) by reflexivity.
    clearbody vals.
    (* [comment removed for export] *)
    run_block scr0 43%nat.
    (* [comment removed for export] *)
    stdio_then_tail vals scS msg_short msg_short_img 0x3645f%Z err_tail_short HL P0 P3 P4 HR HK.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem header_overrun :
    (6 <= length content)%nat -> (Z.of_nat (length content) < 6 + hdr_cfglen content)%Z ->
    realizes RSEGS (mkCfg (mkst R0 (Z_to_bv 64 0xe1aa0) M0 (seg_rom RSEGS)) modelh) (t_die msg_overrun fs0).
  Proof.
    intros Hge Hov. destruct hdr_sym as (e & He & HR & HK0).
    pose proof (hdr_know_long e HK0 Hge) as HK. clear HK0.
    pose proof hp_facts as ((SP & SPA) & (GM1 & GM2 & GMA) & TID & LL).
    pose proof (hdr_cfglen_range content) as CR. assert (LB : (0 <= L < 65536)%Z) by (unfold L; lia).
    set (vals := valsh e) in *.
    assert (HL : length vals = 43%nat) by (subst vals; unfold valsh; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = tid) by reflexivity.
    assert (P5 : vals_ev vals 5 = Z_to_bv 64 L) by reflexivity.
    assert (P6 : vals_ev vals 6 = Z_to_bv 64 (hdr_b0 content)) by reflexivity.
    assert (P7 : vals_ev vals 7 = Z_to_bv 64 (hdr_b1 content)) by reflexivity.
    clearbody vals.
    (* [comment removed for export] *)
    run_block scr_taken 43%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. fold cfglen_x. cbn [edenot].
      rewrite (cfglen_val content vals P6 P7). change (ev (ENVh content vals) 5) with (vals_ev vals 5). rewrite P5.
      rewrite alu_add. unfold v_add. cbn [branch_taken]. unfold bv_ltu.
      rewrite (u_small (hdr_cfglen content)) by lia. change (bv_unsigned (Z_to_bv 64 6)) with 6%Z.
      rewrite !u_small by lia. apply Z.ltb_lt. lia. }
    (* [comment removed for export] *)
    stdio_then_tail vals scO msg_overrun msg_overrun_img 0x1bca2%Z err_tail_overrun HL P0 P3 P4 HR HK.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem header_ok : forall (mode : bool) (Q : config -> Prop) K,
    (6 + hdr_cfglen content <= Z.of_nat (length content))%Z ->
    (* [comment removed for export] *)
    (forall R', tgt_entry (bv_unsigned sp0) (bv_unsigned gm + 32) can content R' M0 ->
       GG RSEGS mode Q K (mkCfg (mkst R' (Z_to_bv 64 0xe1c8c) M0 (seg_rom RSEGS)) modelh)) ->
    GG RSEGS mode Q K (mkCfg (mkst R0 (Z_to_bv 64 0xe1aa0) M0 (seg_rom RSEGS)) modelh).
  Proof.
    intros mode Q K Hok HK_T. destruct hdr_sym as (e & He & HR & HK0).
    pose proof (hdr_cfglen_range content) as CR.
    pose proof (hdr_know_long e HK0 ltac:(lia)) as HK. clear HK0.
    pose proof hp_facts as ((SP & SPA) & (GM1 & GM2 & GMA) & TID & LL).
    pose proof (u64_range gm) as Ugm. assert (LB : (0 <= L < 65536)%Z) by (unfold L; lia).
    pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1. change (bv_modulus 8) with 256%Z in B1.
    (* [comment removed for export] *)
    set (cb := fun i : nat => Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (hdr_cfglen content) + 2 + i) content (Z_to_bv 8 0)))).
    assert (HL : length (valsh e) = 43%nat) by (unfold valsh; rewrite length_app, junk_vals_length; reflexivity).
    (* [comment removed for export] *)
    pose proof (env_app_regs (valsh e) [cb 1%nat; cb 0%nat; cb 2%nat; cb 3%nat] (blobs_ev [content]) sr_H R0
                  ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR1.
    pose proof (env_app_know RSEGS (valsh e) [cb 1%nat; cb 0%nat; cb 2%nat; cb 3%nat] (blobs_ev [content]) M0 kn_long
                  ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK1.
    clear HR HK.
    set (vals := valsh e ++ [cb 1%nat; cb 0%nat; cb 2%nat; cb 3%nat]) in *.
    change (Env (vals_ev vals) (blobs_ev [content])) with (ENVh content vals) in HR1, HK1.
    rename HR1 into HR. rename HK1 into HK.
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P5 : vals_ev vals 5 = Z_to_bv 64 L) by reflexivity.
    assert (P6 : vals_ev vals 6 = Z_to_bv 64 (hdr_b0 content)) by reflexivity.
    assert (P7 : vals_ev vals 7 = Z_to_bv 64 (hdr_b1 content)) by reflexivity.
    assert (PB41 : vals_ev vals 43 = cb 1%nat).
    { unfold vals. replace 43%nat with (length (valsh e) + 0)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (PB42 : vals_ev vals 44 = cb 0%nat).
    { unfold vals. replace 44%nat with (length (valsh e) + 1)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (PB43 : vals_ev vals 45 = cb 2%nat).
    { unfold vals. replace 45%nat with (length (valsh e) + 2)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (PB44 : vals_ev vals 46 = cb 3%nat).
    { unfold vals. replace 46%nat with (length (valsh e) + 3)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    clearbody vals.
    pose proof (cfglen_val content vals P6 P7) as CV.
    (* [comment removed for export] *)
    assert (CB : forall i, (i < 4)%nat ->
      rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned gm + hdr_cfglen content + 34 + Z.of_nat i)) 1%nat
      = Some [nth (Z.to_nat (hdr_cfglen content) + 2 + i) content (Z_to_bv 8 0)]).
    { intros i Hi.
      replace (bv_unsigned gm + hdr_cfglen content + 34 + Z.of_nat i)%Z
        with (bv_unsigned gm + 32 + Z.of_nat (Z.to_nat (hdr_cfglen content) + 2 + i))%Z by lia.
      rewrite content_byte by lia. rewrite w2le1_byte. reflexivity. }
    (* [comment removed for export] *)
    gg_block_gen FUELh STOPSh scr_fall 43%nat true.
    all: try (unfold sc_denot; fold cfglen_x).
    (* [comment removed for export] *)
    all: try (lazymatch goal with
              | |- branch_taken _ _ _ = false =>
                  cbn [edenot]; rewrite CV; change (ev (ENVh content vals) 5) with (vals_ev vals 5); rewrite P5;
                  rewrite alu_add; unfold v_add; cbn [branch_taken]; unfold bv_ltu;
                  rewrite (u_small (hdr_cfglen content)) by lia; change (bv_unsigned (Z_to_bv 64 6)) with 6%Z;
                  rewrite !u_small by lia; apply Z.ltb_ge; lia
              end).
    (* [comment removed for export] *)
    all: try (lazymatch goal with
              | |- exists bs, rdn _ _ (adenot _ (SA _ ?k)) 1 = Some bs /\ _ =>
                  let i := eval vm_compute in (Z.to_nat (k - 34)) in
                  eexists; split;
                  [ unfold adenot, v_addi; cbn [a_base a_off edenot]; rewrite CV;
                    change (ev (ENVh content vals) 3) with (vals_ev vals 3); rewrite P3;
                    rewrite alu_add; unfold v_add;
                    rewrite (u_small (hdr_cfglen content)) by lia; rewrite !u_small by lia;
                    replace (bv_unsigned gm + hdr_cfglen content + k)%Z
                      with (bv_unsigned gm + hdr_cfglen content + 34 + Z.of_nat i)%Z by lia;
                    apply (CB i); lia
                  | lazymatch goal with |- _ = edenot _ (EVar ?n) => change (edenot (ENVh content vals) (EVar n)) with (vals_ev vals n) end;
                    first [rewrite PB41 | rewrite PB42 | rewrite PB43 | rewrite PB44];
                    unfold cb, extz; cbn [lez bytes_le_to_Z Z.shiftl]; rewrite Z.lor_0_r; reflexivity ]
              | |- flat _ (SA _ ?k) _ =>
                  unfold flat, estart, elenZ; cbn [a_base a_off]; fold cfglen_x; cbn [edenot]; rewrite CV;
                  change (ev (ENVh content vals) 3) with (vals_ev vals 3); rewrite P3;
                  rewrite alu_add; unfold v_add; rewrite (u_small (hdr_cfglen content)) by lia; rewrite !u_small by lia; lia
              end).
    all: let n := numgoals in idtac "after-block goals:" n.
    (* [comment removed for export] *)
    lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst _ _ ?Mx _) _) =>
      lazymatch goal with EQ : Mx = _ |- _ => cbn [mem_denot] in EQ; subst Mx end end.
    apply HK_T.
    destruct HP as [Rsp Rgp Rtp Rs0 Rs1 Rs2 Rs3 Rs4 Rs5 Rs6 Rs7 Hsp Hgm Har Hai Hdj Htid HLL Hst
                    Hra Hf64 Hf72 Hf80 Hf88 Hf96 Hf104 Hf112 Hf120
                    Hgr Hgmeta Hpm4 Hpm3 Hpm2 Hgzr Hge5 Hge4 Hgend Hcont Hma Hck Hgp Hgn Hgmm Hgav Hgfr HgW
                    Hsec Hfmh Hact Hus Hseq Htc Herr Hgd Hcanr Hsecr Himg].
    assert (A38 : edenot (ENVh content vals) (EAlu ALU_ADD (EAlu ALU_ADD (EVar 3) cfglen_x) (ELit 38))
                  = Z_to_bv 64 (bv_unsigned gm + 32 + 6 + hdr_cfglen content)).
    { cbn [edenot]. rewrite CV. change (ev (ENVh content vals) 3) with (vals_ev vals 3); rewrite P3.
      rewrite !alu_add. unfold v_add. rewrite (alu_add gm). unfold v_add. rewrite (u_small (hdr_cfglen content)) by lia.
      rewrite (u_small (bv_unsigned gm + hdr_cfglen content)) by lia. change (bv_unsigned (Z_to_bv 64 38)) with 38%Z. f_equal. lia. }
    assert (APL : edenot (ENVh content vals) (EAlu ALU_ADD (EAlu ALU_ADD (EVar 5) (EMd M_MUL (ELit (-1)) cfglen_x)) (ELit (-6)))
                  = Z_to_bv 64 (hdr_paylen content)).
    { cbn [edenot]. rewrite CV. change (ev (ENVh content vals) 5) with (vals_ev vals 5); rewrite P5.
      rewrite !alu_add, m_mul. unfold v_add, v_mul. rewrite ?alu_add. unfold v_add.
      apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
      rewrite (Z.mod_small L), (Z.mod_small (hdr_cfglen content)) by lia.
      change ((-1) mod 2 ^ 64)%Z with 18446744073709551615%Z. change ((-6) mod 2 ^ 64)%Z with 18446744073709551610%Z.
      rewrite Zplus_mod_idemp_l.
      replace (L + (18446744073709551615 * hdr_cfglen content) mod 2 ^ 64 + 18446744073709551610)%Z
        with (L + 18446744073709551610 + (18446744073709551615 * hdr_cfglen content) mod 2 ^ 64)%Z by lia.
      rewrite Zplus_mod_idemp_r.
      apply (mod_eq_shift _ _ (hdr_cfglen content + 1)); [lia|]. unfold hdr_paylen, L. lia. }
    constructor.
    all: try (regv HR (1 : reg); reflexivity).
    - regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVh]. rewrite P0. f_equal; lia.
    - regv HR (3 : reg). reflexivity.
    - regv HR (4 : reg). reflexivity.
    - regv HR (10 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVh]. rewrite P3. f_equal; lia.
    - regv HR (11 : reg). exact CV.
    - regv HR (12 : reg). exact A38.
    - regv HR (13 : reg). exact APL.
    - regv HR (8 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVh]. rewrite P3. f_equal; lia.
    - regv HR (9 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVh]. rewrite P3. reflexivity.
    - regv HR (18 : reg). exact CV.
    - regv HR (19 : reg). exact A38.
    - regv HR (20 : reg). exact APL.
    - regv HR (21 : reg). change (edenot (ENVh content vals) (EExt true 0 1 (EVar 7))) with (sx8F (vals_ev vals 7)).
      rewrite P7. apply sx8F_val. unfold hdr_b1. lia.
    - regv HR (22 : reg). reflexivity.
    - regv HR (23 : reg). reflexivity.
    - exact Hsp.
    - unfold L in *. lia.
    - destruct Hgm as (Hgm1 & Hgm2 & Hgmal). split; [|split]; [ | lia | unfold L in *; lia].
      apply (proj1 (Z.mod_divide (bv_unsigned gm) 4096 ltac:(lia))) in Hgmal. destruct Hgmal as [q Hq]. rewrite Hq.
      replace (q * 4096 + 32)%Z with ((q * 256 + 2) * 16)%Z by lia. apply Z_mod_mult.
    - exact Hcanr.
    - exact Hst.
    - intros i Hi. apply (Himg 0x10000%Z 0x31eec0%Z i); [cbn; tauto | exact Hi].
    - apply (Himg 0x32ef09%Z 0x331a18%Z 0x32ef10%Z); [cbn; tauto | lia].
    - exact Hgd.
    - exact Hcont.
  Qed.
End Header.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma store_ok_of_defined : forall M (a : Z) (m : nat),
  (0 <= a)%Z -> (a + Z.of_nat m <= 2 ^ 64)%Z ->
  (forall i, (a <= i < a + Z.of_nat m)%Z -> M (Z_to_bv 64 i) <> None) ->
  store_ok RSEGS M (Z_to_bv 64 a) m = true.
Proof.
  intros M a m Ha Hm Hdef. destruct m as [|m]; [reflexivity|].
  apply store_ok_of_all; [rewrite u_small by lia; lia|].
  intros x Hx. rewrite u_small in Hx by lia. unfold wview.
  specialize (Hdef (bv_unsigned x) Hx). rewrite Z_to_bv_bv_unsigned in Hdef.
  destruct (M x); [discriminate | exfalso; apply Hdef; reflexivity].
Qed.

Lemma map_has_In : forall l (a n : word), In (a, n) l -> map_has l a n = true.
Proof.
  induction l as [|[b k] l IH]; intros a n Hin; [destruct Hin|].
  destruct Hin as [E|Hin].
  - injection E as -> ->. apply map_has_head.
  - apply map_has_cons. apply IH. exact Hin.
Qed.

Lemma zbv_add1 : forall A, (0 <= A)%Z -> (A + 1 < 2 ^ 64)%Z -> Z_to_bv 64 A + 1 = Z_to_bv 64 (A + 1).
Proof. intros A H0 H1. rewrite w_add_1, u_small by lia. reflexivity. Qed.

Section Intro.
  Variables (sp0 p1 gm tid : word) (area brkv mas can sec : Z) (content : list byte).
  Variables (Rr : bvmap 5 word) (Mr : word -> option byte) (R : bvmap 5 word) (M : word -> option byte).
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis RP : read_post0 sp0 p1 gm content Rr Mr R M.
  Hypothesis W0 : world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas (bv_unsigned tid) can sec M.
  Hypothesis MF : main_frame (bv_unsigned sp0) M.
  Hypothesis HL : (Z.of_nat (length content) < 65536)%Z.
  Hypothesis Hcan : (0 <= can < 2 ^ 64)%Z.
  Hypothesis Hsec : (0 <= sec < 2 ^ 64)%Z.

  Lemma header_pre_intro : header_pre sp0 p1 gm tid area can sec content R M.
  Proof.
    destruct RP as [Qsp Qgp Qtp Qs0 Qs1 Qs2 Qs3 Qs4 Qs5 Qs6 Qs7 Qkeep Qframe Qgrows Qcontent Qstack Qgroup Qstage].
    pose proof W0 as W.
    destruct W as [Wsecret Winit Wctr Wfmh Wam Wamc Wamac Wmas Wmah Wmat Wamas Wactive44 Wusage44 Wseq Wbrk
                   Wachk Wanext Wans Wsprev Wsnext Wsmem Wsmsk WsW Warest Wadef Wgmeta Wgaidx Wgpad Wenf Wgtail Wgdef
                   Waal Wgmal Wsp0 Warng Waimg Wgmrng Wdisj Wbrkv Wmasv Wtid Wtidr Werrno Wself Wcanary Wpagesz Wimg Wworld].
    destruct MF as [F1 F2 F3 F4 F5 F6 F7 F8 F9].
    pose proof (u64_range gm) as Ugm. pose proof (u64_range sp0) as Usp.
    destruct Hvsp as (SPlo & SPhi & SPal). unfold sp_window_lo, sp_window_hi in *.
    rewrite ctx_active_44 in Wactive44. rewrite ctx_usage_44 in Wusage44. rewrite W64K_val in WsW.
    unfold ctx_secret, ctx_free_meta_head, ctx_seq, CTX in Wsecret, Wfmh, Wseq.
    (* [comment removed for export] *)
    destruct Wenf as [Pp Pe Pr_ Pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr]. subst Pp Pe Pr_ Pq.
    constructor.
    - exact Qsp. - exact Qgp. - exact Qtp. - exact Qs0. - exact Qs1. - exact Qs2. - exact Qs3. - exact Qs4. - exact Qs5. - exact Qs6. - exact Qs7.
    - split; [lia | exact SPal].
    - repeat split; first [lia | exact Wgmal].
    - repeat split; first [lia | exact Waal].
    - exact Waimg.
    - exact Wdisj.
    - exact Wtidr.
    - exact HL.
    - exact Qstack.
    - exact F1. - exact F2. - exact F3. - exact F4. - exact F5. - exact F6. - exact F7. - exact F8. - exact F9.
    - exact Qgroup.
    - exact Wgmeta.
    - (* [comment removed for export] *)
      replace (bv_unsigned gm + 28)%Z with (bv_unsigned gm + 16 + 16 * 1 - 4)%Z by lia. exact Pm4.
    - (* [comment removed for export] *)
      replace (bv_unsigned gm + 29)%Z with (bv_unsigned gm + 16 + 16 * 1 - 3)%Z by lia. rewrite Pm3. reflexivity.
    - (* [comment removed for export] *)
      unfold cell. replace (bv_unsigned gm + 30)%Z with (bv_unsigned gm + 16 + 16 * 1 - 2)%Z by lia. rewrite Pm2. reflexivity.
    - (* [comment removed for export] *) replace (bv_unsigned gm + 65568)%Z with (bv_unsigned gm + 16 + 16 * 1 + 65536)%Z by lia. apply Pzr. lia.
    - replace (bv_unsigned gm + 69623)%Z with (bv_unsigned gm + 16 + 69616 - 4 - 5)%Z by lia. apply Pe5. lia.
    - unfold cell. replace (bv_unsigned gm + 69624)%Z with (bv_unsigned gm + 16 + 69616 - 4 - 4)%Z by lia.
      rewrite (Pe4 ltac:(lia)). reflexivity.
    - exact Wgtail.
    - exact Qcontent.
    - (* [comment removed for export] *)
      intros d m Hd Hm. apply store_ok_of_defined; [lia | lia |]. intros i Hi.
      replace i with (area + (i - area))%Z by lia. apply Wadef. lia.
    - exact Wachk.
    - exact Wsprev.
    - exact Wsnext.
    - exact Wsmem.
    - (* [comment removed for export] *)
      unfold cell in *. exact (rdn_firstn RSEGS M 8 _ _ 4 Wsmsk ltac:(lia)).
    - unfold cell in *.
      pose proof (rdn_skipn RSEGS M 8 (Z_to_bv 64 (area + 48)) _ 4 Wsmsk ltac:(lia)) as H4.
      rewrite w_add_nat, u_small in H4 by lia.
      replace (area + 52)%Z with (area + 48 + Z.of_nat 4)%Z by lia. exact H4.
    - exact WsW.
    - exact Wsecret.
    - exact Wfmh.
    - exact Wactive44.
    - exact Wusage44.
    - exact Wseq.
    - exact Wtid.
    - exact Werrno.
    - exact Wcanary.
    - exact Hcan.
    - exact Hsec.
    - (* [comment removed for export] *)
      intros lo hi i Hin Hi.
      assert (Hc : img_clear M lo hi).
      { apply (proj1 (Forall_forall _ _) Wimg (lo, hi)). clear -Hin.
        unfold hdr_img_ranges in Hin. unfold img_clear_ivs.
        repeat (destruct Hin as [Hin|Hin]; [rewrite <- Hin; cbn; tauto|]). destruct Hin. }
      apply Hc. exact Hi.
  Qed.
End Intro.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition t_hdr (content : list byte) (fs : Fs) (K : TSet) : TSet :=
  let len := length content in
  if (MAX_INPUT <=? Z.of_nat len)%Z then t_die msg_refused fs
  else if (len <? HDR_MIN)%nat then t_die msg_short fs
  else if (len <? HDR_MIN + config_len content)%nat then t_die msg_overrun fs
  else K.

Lemma t_body_hdr : forall content fs, t_body content fs = t_hdr content fs (t_target content fs).
Proof. reflexivity. Qed.

Lemma config_len_hdr : forall content, config_len content = Z.to_nat (hdr_cfglen content).
Proof. reflexivity. Qed.

Theorem header_phase : forall (mode : bool) (Q : config -> Prop) (sp0 p1 gm tid : word) (area brkv mas can sec : Z)
    (content : list byte) (VM : VmMaps) (stdin0 : AmbIn) (fs0 : Fs)
    (Rr : bvmap 5 word) (Mr : word -> option byte) (R : bvmap 5 word) (M : word -> option byte) (K : TSet),
  valid_sp sp0 ->
  read_post0 sp0 p1 gm content Rr Mr R M ->
  world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas (bv_unsigned tid) can sec M ->
  main_frame (bv_unsigned sp0) M ->
  (Z.of_nat (length content) < 65536)%Z ->
  (0 <= can < 2 ^ 64)%Z -> (0 <= sec < 2 ^ 64)%Z ->
  In (gm, Z_to_bv 64 69632) (vm_maps VM) ->
  (mode = false -> (6 + hdr_cfglen content <= Z.of_nat (length content))%Z) ->
  (forall R', tgt_entry (bv_unsigned sp0) (bv_unsigned gm + 32) can content R' M ->
     GG RSEGS mode Q K (mkCfg (mkst R' (Z_to_bv 64 0xe1c8c) M (seg_rom RSEGS)) (model_post VM stdin0 fs0 tid))) ->
  GG RSEGS mode Q (t_hdr content fs0 K)
     (mkCfg (mkst R (Z_to_bv 64 0xe1aa0) M (seg_rom RSEGS)) (model_post VM stdin0 fs0 tid)).
Proof.
  intros mode Q sp0 p1 gm tid area brkv mas can sec content VM stdin0 fs0 Rr Mr R M K Hvsp RP W0 MF HL Hcan Hsec Hin Hmode HT.
  pose proof (header_pre_intro sp0 p1 gm tid area brkv mas can sec content Rr Mr R M Hvsp RP W0 MF HL Hcan Hsec) as HP.
  pose proof (map_has_In _ _ _ Hin) as Hmap.
  pose proof (Z.mod_pos_bound (hdr_cfg content) 32768 ltac:(lia)) as CR.
  unfold t_hdr. rewrite config_len_hdr. unfold HDR_MIN.
  destruct (MAX_INPUT <=? Z.of_nat (length content))%Z eqn:E1; [apply Z.leb_le in E1; unfold MAX_INPUT in E1; lia|].
  destruct (length content <? 6)%nat eqn:E2.
  - apply Nat.ltb_lt in E2. destruct mode.
    + apply gg_of_rz. apply (header_short sp0 p1 gm tid area can sec content VM stdin0 fs0 R M HP Hmap E2).
    + exfalso. specialize (Hmode eq_refl). unfold hdr_cfglen in *. lia.
  - apply Nat.ltb_ge in E2.
    destruct (length content <? 6 + Z.to_nat (hdr_cfglen content))%nat eqn:E3.
    + apply Nat.ltb_lt in E3. destruct mode.
      * apply gg_of_rz. apply (header_overrun sp0 p1 gm tid area can sec content VM stdin0 fs0 R M HP Hmap E2).
        unfold hdr_cfglen in *. lia.
      * exfalso. specialize (Hmode eq_refl). unfold hdr_cfglen in *. lia.
    + apply Nat.ltb_ge in E3.
      apply (header_ok sp0 p1 gm tid area can sec content VM stdin0 fs0 R M HP mode Q K); [|exact HT].
      unfold hdr_cfglen in *. lia.
Qed.
End H0Header.

(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PropExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SeqExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StoreOk OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ShapeAlg Spec HUReadBase HUWorld HUTargetPre H0Header.
Import ConeCfg.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition t_hdr := H0Header.t_hdr.
Definition header_phase := H0Header.header_phase.
Definition t_body_hdr := H0Header.t_body_hdr.
