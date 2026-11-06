(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.H Require GcFlushY10.  (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.skcms.iccprofile_info.images Require Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Amb PropExec CatExec CatSim SeqExec StoreOk ShapeAlg ShapeLaws SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Spec UbStartup UbMainEntry UbReadDefs UbReadBase UbReadStage UbWorld UbWorldK UbTargetPre UbTargetPreK UbSymPlanSoundA UbPilotOOM UbDirMid UbReadBig.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require UbHeader.
Unset Nia Cache.  (* [comment removed for export] *)

Module UbLeafHeader.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbWorld OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbTargetPre OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbHeader.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section WithFP1. Context {FP : PropExec.FPState}.
Theorem header_phase {AMB : Amb} : forall (sp0 p1 gm tid sec cnr : word) (area brkv mas : Z) (content : list byte)
    (VM : VmMaps) (stdin0 : InputStream) (fs0 : Fs)
    (Rr : bvmap 5 word) (Mr : word -> option byte) (R : bvmap 5 word) (M : word -> option byte),
  valid_sp sp0 ->
  read_post0 sp0 p1 gm content Rr Mr R M ->
  world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned sec) (bv_unsigned cnr) Mr ->
  main_frame (bv_unsigned sp0) Mr ->
  (bv_unsigned gm + 69632 <= bv_unsigned sp0 - 8388608)%Z ->
  (Z.of_nat (length content) < 65536)%Z ->
  In (gm, Z_to_bv 64 69632) (vm_maps VM) ->
  (forall R' M', target_pre (bv_unsigned sp0) (bv_unsigned gm) area brkv mas (bv_unsigned tid) (bv_unsigned sec) (bv_unsigned cnr)
                            content R' M' ->
     realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x12db8) M' (seg_rom RSEGS)) (model_post VM stdin0 fs0 tid))
                (t_target content fs0)) ->
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12be4) M (seg_rom RSEGS)) (model_post VM stdin0 fs0 tid))
             (t_body content fs0).
Proof. exact (@UbHeader.header_phase FP AMB). Qed.
End WithFP1.
End UbLeafHeader.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require MmapSim AllocSim MallocDefs UbEnframeBase.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PerfWalkBz.
From Stdlib Require Zify.

Module UbHeaderK.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbEnframeBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbReadStage OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbWorld OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbTargetPre OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbWorldK OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbTargetPreK OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbHeader.UbHeader_defs.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
Definition sr_HK : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x314d8; J 5; J 6; J 7;
   ELit 2; EVar 2; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 1; EVar 3; ELit 3; EVar 4; ELit 0x213c9; ELit 0;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].

Definition kn_HK : list kentry :=
  [KRange (EVar 2) 0x52000 0x7fffff800000; KRange (EVar 3) 65536 67108863;
   KWord (SA (EVar 2) 0) 1 (EVar 6); KWord (SA (EVar 2) 1) 1 (EVar 7);
   KRange (EVar 6) 0 255; KRange (EVar 7) 0 255].

(* [comment removed for export] *)
Definition NXk : nat := 41.
Definition hkK := Eval vm_compute in runh scr_fall (SS 0x12be4 sr_HK [] kn_HK NXk).

Lemma hdrk_itinerary_ok :
  s_pc (fst (fst hkK)) = 0x12db8%Z /\ s_log (fst (fst hkK)) = [] /\ s_next (fst (fst hkK)) = 45%nat
  /\ nth 11 (s_regs (fst (fst hkK))) (ELit 0) = cfglen_x.
Proof using . vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition off_image (x : Z) : Prop := (x + 1 <= 0x10000 \/ 0x52000 <= x)%Z.

Lemma find_segment_skip : forall seg rest a n,
  (0 < n)%Z ->
  (a < Z.of_N (seg_base seg) \/ Z.of_N (seg_base seg) + Z.of_N (seg_size seg) < a + n)%Z ->
  find_segment (seg :: rest) a n = find_segment rest a n.
Proof using .
  intros seg rest a n Hn H. cbn [find_segment].
  destruct (Z.leb_spec (Z.of_N (seg_base seg)) a); destruct (Z.leb_spec (a + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)));
    cbn [andb]; try reflexivity. lia.
Qed.

Lemma find_segment_off : forall a n, (0 < n)%Z -> (a + n <= 0x10000 \/ 0x52000 <= a)%Z ->
  find_segment RSEGS a n = None.
Proof using .
  intros a n Hn H. unfold M.loaded_segments, Ubsan_loaded_segments.
  rewrite 4 find_segment_skip; [reflexivity | exact Hn | | exact Hn | | exact Hn | | exact Hn |];
    cbn [seg_base seg_size Ubsan_segment_000 Ubsan_segment_001 Ubsan_segment_002 Ubsan_segment_003]; lia.
Qed.

Lemma seg_rom_off : forall x : word, off_image (bv_unsigned x) -> seg_rom RSEGS x = None.
Proof using .
  intros x Hx. unfold seg_rom, memory_read. rewrite find_segment_off; [reflexivity | cbn; lia | unfold off_image in Hx; cbn; lia].
Qed.

Lemma store_ok1_off : forall M (x : word), off_image (bv_unsigned x) ->
  store_ok RSEGS M x 1 = true -> M x <> None.
Proof using .
  intros M x Hx H. cbn [store_ok] in H. unfold wview in H.
  destruct (M x); [discriminate|]. rewrite find_segment_off in H; [discriminate | lia | unfold off_image in Hx; lia].
Qed.

(* [comment removed for export] *)
Lemma byte_of_cell : forall M a v,
  (0 <= a < 2 ^ 64)%Z -> off_image a -> (0 <= v < 256)%Z ->
  cell M a 1 v -> M (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Proof using .
  intros M a v Ha Hoff Hv C. unfold cell in C. cbn [rdn] in C.
  rewrite (seg_rom_off (Z_to_bv 64 a)) in C by (rewrite u64_lit by lia; exact Hoff).
  destruct (M (Z_to_bv 64 a)) as [b|]; [|discriminate].
  unfold word_to_le_bytes in C. cbn [Z_to_le_bytes] in C. rewrite u64_lit in C by lia.
  injection C as ->. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma defined_of_wr : forall M (base n : Z),
  (0 <= base)%Z -> (base + n <= 2 ^ 64)%Z -> (base + n <= 0x10000 \/ 0x52000 <= base)%Z ->
  (forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= n)%Z -> store_ok RSEGS M (Z_to_bv 64 (base + d)) m = true) ->
  forall i, (0 <= i < n)%Z -> M (Z_to_bv 64 (base + i)) <> None.
Proof using .
  intros M base n Hb Hn Hoff W i Hi. apply store_ok1_off.
  - rewrite u64_lit by lia. unfold off_image. lia.
  - apply (W i 1%nat); cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cell_ofw : forall M A n (w : word) A' V',
  rdn RSEGS M (Z_to_bv 64 A) n = Some (word_to_le_bytes n w) ->
  A = A' -> w = Z_to_bv 64 V' -> cell M A' n V'.
Proof using . intros M A n w A' V' H <- ->. exact H. Qed.

Lemma w2le_8_inj : forall (v w : word), word_to_le_bytes 8 v = word_to_le_bytes 8 w -> v = w.
Proof using .
  intros v w H. apply bv_eq. rewrite <- (bytes_le_to_Z_8 v), <- (bytes_le_to_Z_8 w). rewrite H. reflexivity.
Qed.

Lemma w2le_4_mod : forall (e : word),
  word_to_le_bytes 4 e = word_to_le_bytes 4 (Z_to_bv 64 (bv_unsigned e mod 2 ^ 32)).
Proof using .
  intros e. unfold word_to_le_bytes. pose proof (Z.mod_pos_bound (bv_unsigned e) (2 ^ 32) ltac:(lia)).
  rewrite (u64_lit (bv_unsigned e mod 2 ^ 32)) by lia.
  symmetry. exact (Z_to_le_bytes_mod 4 (bv_unsigned e)).
Qed.

Lemma w2le1_byte_k : forall (x : byte), word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned x)) = [x].
Proof using .
  intros x. pose proof (bv_unsigned_in_range _ x) as Hx. change (bv_modulus 8) with 256%Z in Hx.
  unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal.
  rewrite u_small by lia. apply Z_to_bv_bv_unsigned.
Qed.

Lemma live_bytes_cons : forall (a n : word) r, live_bytes ((a, n) :: r) = (bv_unsigned n + live_bytes r)%Z.
Proof using . reflexivity. Qed.

(* [comment removed for export] *)
Lemma pres_cell : forall M0 M sp0 a n v,
  pres M0 M sp0 -> (0x10000 <= a)%Z -> (a + Z.of_nat n <= 0x52000)%Z ->
  (a + Z.of_nat n <= 0x213c9 \/ 0x313c9 <= a)%Z ->
  (forall i, (a <= i < a + Z.of_nat n)%Z -> ~ rd_cell i) ->
  cell M0 a n v -> cell M a n v.
Proof using .
  intros M0 M sp0 a n v P Ha Hn Hst Hrd C. unfold cell in *. rewrite <- C.
  apply rdn_agree. intros j Hj. rewrite (u_small a) by lia. apply P. left. rewrite u_small by lia.
  split; [lia|]. apply Hrd. lia.
Qed.

Lemma pres_img_clear : forall M0 M sp0 lo hi,
  pres M0 M sp0 -> (0x10000 <= lo)%Z -> (hi <= 0x52000)%Z ->
  (hi <= 0x213c9 \/ 0x313c9 <= lo)%Z ->
  (forall i, (lo <= i < hi)%Z -> ~ rd_cell i) ->
  img_clear M0 lo hi -> img_clear M lo hi.
Proof using .
  intros M0 M sp0 lo hi P Hlo Hhi Hst Hrd C i Hi. rewrite (P (Z_to_bv 64 i)); [apply C; exact Hi|].
  left. rewrite u_small by lia. split; [lia|]. apply Hrd. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma curslot_eq : forall k, (0 <= k)%Z -> (curslot k = 4120 + 40 * (k mod 2))%Z.
Proof using .
  intros k Hk. unfold curslot. rewrite Zodd_mod. pose proof (Z.mod_pos_bound k 2 ltac:(lia)).
  destruct (Z.eq_dec (k mod 2) 1) as [E|E]; [rewrite E; reflexivity|].
  replace (k mod 2)%Z with 0%Z by lia. reflexivity.
Qed.

Lemma freeslot_eq : forall k, (0 <= k)%Z -> (freeslot k = 4160 - 40 * (k mod 2))%Z.
Proof using .
  intros k Hk. unfold freeslot. rewrite Zodd_mod. pose proof (Z.mod_pos_bound k 2 ltac:(lia)).
  destruct (Z.eq_dec (k mod 2) 1) as [E|E]; [rewrite E; reflexivity|].
  replace (k mod 2)%Z with 0%Z by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Section KnowFacts.
  Variables (E : env) (M : word -> option byte) (kn : list kentry).
  Hypothesis HK : know_ok RSEGS E M kn.

  Lemma kf_word : forall b o n v, In (KWord (SA b o) n v) kn ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned (edenot E b) + o)) n = Some (word_to_le_bytes n (edenot E v)).
  Proof using HK.
    intros b o n v Hin. pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X.
    destruct X as (_ & _ & X). exact X.
  Qed.

  Lemma kf_zero : forall b o len, In (KZero (SA b o) len) kn ->
    zero_bytes M (bv_unsigned (edenot E b) + o) (bv_unsigned (edenot E len)).
  Proof using HK.
    intros b o len Hin. pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X.
    destruct X as (_ & X). unfold estart, elenZ in X. cbn [a_base a_off] in X. exact X.
  Qed.

  Lemma kf_img : forall lo hi, In (KImg lo hi) kn -> img_clear M lo hi.
  Proof using HK.
    intros lo hi Hin. pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X.
    destruct X as (_ & _ & X). exact X.
  Qed.

  Lemma kf_range : forall x lo hi, In (KRange x lo hi) kn -> (lo <= bv_unsigned (edenot E x) <= hi)%Z.
  Proof using HK.
    intros x lo hi Hin. pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X. lia.
  Qed.

  Lemma kf_align : forall x m, In (KAlign x m) kn -> (bv_unsigned (edenot E x) mod m = 0)%Z.
  Proof using HK.
    intros x m Hin. pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X. lia.
  Qed.

  Lemma kf_wr : forall b o n, In (KWr (SA b o) n) kn ->
    forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= n)%Z ->
      store_ok RSEGS M (Z_to_bv 64 (bv_unsigned (edenot E b) + o + d)) m = true.
  Proof using HK.
    intros b o n Hin. pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X.
    destruct X as (_ & X). unfold estart in X. cbn [a_base a_off] in X. exact X.
  Qed.

  Lemma kf_disj : forall b1 o1 n1 b2 o2 n2, In (KDisj (SA b1 o1) n1 (SA b2 o2) n2) kn ->
    (bv_unsigned (edenot E b1) + o1 + n1 <= bv_unsigned (edenot E b2) + o2
     \/ bv_unsigned (edenot E b2) + o2 + n2 <= bv_unsigned (edenot E b1) + o1)%Z.
  Proof using HK.
    intros b1 o1 n1 b2 o2 n2 Hin. pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X.
    unfold estart in X. cbn [a_base a_off] in X. exact X.
  Qed.
End KnowFacts.
End WithFP1.


(* [comment removed for export] *)
Ltac kin :=
  unfold kn_POST, kn_static, kn_ctx, kn_meta; cbn [app];
  repeat (first [ apply in_eq | apply in_cons ]);
  lazymatch goal with |- In _ nil => fail "kin: entry not found" | |- _ => idtac end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithFP2. Context {FP : PropExec.FPState}.
Section HeaderK.
  Context {AMB : Amb}.
  Variables (k : Z) (sp0 p1 mb gm B e tid sec cnr : word) (area brkv mas : Z) (content : list byte).
  Variables (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps).
  Variables (stdin0 : InputStream) (fs0 : Fs).
  Hypothesis Hk : (1 <= k <= 10)%Z.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis RP : read_post k sp0 p1 mb gm B e sec cnr content M0 R M VM.
  Hypothesis W0 : world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned sec) (bv_unsigned cnr) M0.
  Hypothesis MF : main_frame (bv_unsigned sp0) M0.
  Hypothesis HL : (capk (k - 1) <= Z.of_nat (length content) < capk k)%Z.

  Let L : Z := Z.of_nat (length content).

  (* [comment removed for export] *)
  Definition EK (extra : list word) : env := ENV_RD sp0 p1 mb gm L B e sec cnr extra content.

  Lemma ek0 : forall extra, ev (EK extra) 0 = sp0. Proof using . reflexivity. Qed.
  Lemma ek2 : forall extra, ev (EK extra) 2 = mb. Proof using . reflexivity. Qed.
  Lemma ek5 : forall extra, ev (EK extra) 5 = B. Proof using . reflexivity. Qed.
  Lemma ek6 : forall extra, ev (EK extra) 6 = e. Proof using . reflexivity. Qed.
  Lemma ek7 : forall extra, ev (EK extra) 7 = sec. Proof using . reflexivity. Qed.
  Lemma ek8 : forall extra, ev (EK extra) 8 = cnr. Proof using . reflexivity. Qed.

  (* [comment removed for export] *)
  Ltac get_know extra Hlen HK :=
    destruct (rk_know _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as (extra & Hlen & HK);
    change (ENV_RD sp0 p1 mb gm (Z.of_nat (length content)) B e sec cnr extra content) with (EK extra) in HK.

  (* [comment removed for export] *)
  Ltac kclean X :=
    unfold LA, MBA, BA, mbx, bx in X; rewrite ?edenot_add_lit in X; unfold adenot, v_addi in X; cbn [a_base a_off edenot] in X;
    rewrite ?ek0, ?ek2, ?ek5, ?ek6, ?ek7, ?ek8 in X;
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in X; rewrite ?Z.add_0_l in X.

  Lemma capk_split : capk k = (capk (k - 1) + capk (k - 1))%Z.
  Proof using Hk L.
    unfold capk. replace k with (k - 1 + 1)%Z at 1 by lia. rewrite Z.pow_add_r by lia. lia.
  Qed.

  Lemma hk_nums : (65536 <= capk (k - 1))%Z /\ (capk k <= 67108864)%Z /\ (65536 <= L < 67108864)%Z
                  /\ nb_of k = nbk k /\ cap_of k = capk k /\ off_of k = offk k /\ W_of k = Wk k /\ res_of k = resk k.
  Proof using HL Hk.
    pose proof (capk_pos (k - 1) ltac:(lia)). pose proof (capk_le k ltac:(lia)). unfold L. repeat split; try lia; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma area_eq : area = (bv_unsigned mb + 4096)%Z.
  Proof using L RP W0.
    get_know extra Hlen HK.
    pose proof (rk_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as P.
    pose proof (kf_word _ _ _ HK (ELit 0) 0x51818 8 (mbx 4096) ltac:(kin)) as X. kclean X.
    pose proof (kf_range _ _ _ HK (EVar 2) 0x52000 (0x7fff7f800000 - 8192) ltac:(kin)) as Rmb. cbn [edenot] in Rmb. rewrite ek2 in Rmb.
    pose proof (w_mah _ _ _ _ _ _ _ _ W0) as C0. unfold ctx_meta_area_head, CTX in C0.
    pose proof (w_area_rng _ _ _ _ _ _ _ _ W0) as Ar.
    assert (C : cell M (0x517e0 + 56) 8 area).
    { eapply pres_cell; [exact P | lia | cbn; lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact C0]. }
    unfold cell in C. replace (0x517e0 + 56)%Z with 0x51818%Z in C by reflexivity. rewrite X in C.
    apply (f_equal (fun o => match o with Some l => bytes_le_to_Z l | None => 0%Z end)) in C.
    rewrite !bytes_le_to_Z_8 in C. rewrite !u_small in C by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac kcell HK b o n v :=
    let X := fresh "X" in
    pose proof (kf_word _ _ _ HK b o n v ltac:(kin)) as X; kclean X;
    rewrite ?curslot_eq, ?freeslot_eq in X by lia;
    unfold nb_of, cap_of, off_of, W_of, res_of, held_of in X;
    lazymatch goal with |- cell _ ?A ?w ?V =>
      eapply (cell_ofw _ _ w _ A V X);
      [ lia | first [ reflexivity | symmetry; apply Z_to_bv_bv_unsigned | f_equal; lia ] ]
    end.

  (* [comment removed for export] *)
  Ltac kbyte HK b o v :=
    lazymatch goal with |- ?Mm (Z_to_bv 64 ?A) = Some (Z_to_bv 8 ?V) =>
      let C := fresh "C" in
      assert (C : cell Mm A 1 V); [kcell HK b o 1%nat v | apply (byte_of_cell Mm A V); [lia | unfold off_image; lia | lia | exact C] ]
    end.

  Lemma world_k_intro : world_k k area (bv_unsigned B) brkv mas (bv_unsigned tid) (bv_unsigned sec) (bv_unsigned cnr) M.
  Proof using HL Hk L RP W0.
    get_know extra Hlen HK. pose proof (rk_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as P. pose proof area_eq as AE.
    pose proof hk_nums as (Hc1 & Hc2 & HLr & _).
    pose proof (u64_range mb) as Umb. pose proof (u64_range B) as UB. pose proof (u64_range e) as Ue.
    destruct W0 as [Wsecret Winit Wctr Wfmh Wam Wamc Wamac Wmas Wmah Wmat Wamas Wactive44 Wusage44 Wseq Wbrk
                    Wachk Wanext Wans Wsprev Wsnext Wsmem Wsmsk WsW Warest Wadef Wgmeta Wgaidx Wgpad Wenf Wgtail Wgdef
                    Waal Wgmal Warng Waimg Wgmrng Wdisj Wbrkv Wmasv Wtid Wtidr Werrno Wself Wcanary Wpagesz Wimg].
    (* [comment removed for export] *)
    pose proof (kf_range _ _ _ HK (EVar 2) 0x52000 (0x7fff7f800000 - 8192) ltac:(kin)) as Rmb. cbn [edenot] in Rmb. rewrite ek2 in Rmb.
    pose proof (kf_range _ _ _ HK (EVar 5) 0x52000 (CEIL - nb_of k) ltac:(kin)) as RB. cbn [edenot] in RB. rewrite ek5 in RB.
    pose proof (kf_align _ _ _ HK (EVar 2) 4096 ltac:(kin)) as Amb. cbn [edenot] in Amb. rewrite ek2 in Amb.
    pose proof (kf_align _ _ _ HK (EVar 5) 4096 ltac:(kin)) as AB. cbn [edenot] in AB. rewrite ek5 in AB.
    pose proof (kf_disj _ _ _ HK (EVar 5) 0 (nb_of k) (EVar 2) 4096 4096 ltac:(kin)) as DB. kclean DB.
    pose proof (kf_wr _ _ _ HK (EVar 2) 4096 4096 ltac:(kin)) as Wmb. kclean Wmb.
    pose proof (kf_wr _ _ _ HK (EVar 5) 0 (nb_of k) ltac:(kin)) as WB. kclean WB.
    pose proof (kf_zero _ _ _ HK (EVar 2) 4200 (ELit 3992) ltac:(kin)) as Zarea. kclean Zarea.
    pose proof (kf_zero _ _ _ HK (EVar 5) 8 (ELit 5) ltac:(kin)) as Zhdr. kclean Zhdr.
    pose proof (kf_zero _ _ _ HK (EVar 5) (nb_of k - 4) (ELit 4) ltac:(kin)) as Ztail. kclean Ztail.
    change (bv_unsigned (Z_to_bv 64 3992)) with 3992%Z in Zarea.
    change (bv_unsigned (Z_to_bv 64 5)) with 5%Z in Zhdr.
    change (bv_unsigned (Z_to_bv 64 4)) with 4%Z in Ztail.
    unfold CEIL, nb_of, cap_of in *.
    constructor.
    all: unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta, ctx_avail_meta_count,
      ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta_areas,
      ctx_active, ctx_usage, ctx_seq, ctx_brk, CTX in *.
    all: unfold slotC, slotF, nbk, capk, offk, Wk, resk.
    - exact Hk.
    - kcell HK (ELit 0) 0x517e0%Z 8%nat (EVar 7).
    - kcell HK (ELit 0) 0x517e8%Z 4%nat (ELit 1).
    - kcell HK (ELit 0) 0x517ec%Z 4%nat (ELit (1 + k)).
    - kcell HK (ELit 0) 0x517f0%Z 8%nat (mbx (freeslot k)).
    - kcell HK (ELit 0) 0x517f8%Z 8%nat (mbx 4200).
    - kcell HK (ELit 0) 0x51800%Z 8%nat (ELit 99).
    - kcell HK (ELit 0) 0x51808%Z 8%nat (ELit 0).
    - (* [comment removed for export] *)
      eapply pres_cell; [exact P | lia | cbn; lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact Wmas].
    - kcell HK (ELit 0) 0x51818%Z 8%nat (mbx 4096).
    - kcell HK (ELit 0) 0x51820%Z 8%nat (mbx 4096).
    - kcell HK (ELit 0) 0x51828%Z 8%nat (mbx 8192).
    - kcell HK (ELit 0) 0x51990%Z 8%nat (ELit 0).
    - kcell HK (ELit 0) 0x51b10%Z 8%nat (ELit 0).
    - kcell HK (ELit 0) 0x51b70%Z 1%nat (ELit (1 + 2 * k)).
    - eapply pres_cell; [exact P | lia | cbn; lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact Wbrk].
    - kcell HK (EVar 2) 4096%Z 8%nat (EVar 7).
    - kcell HK (EVar 2) 4104%Z 8%nat (ELit 0).
    - kcell HK (EVar 2) 4112%Z 4%nat (ELit 101).
    - kcell HK (EVar 2) (curslot k) 8%nat (ELit 0).
    - kcell HK (EVar 2) (curslot k + 8)%Z 8%nat (ELit 0).
    - kcell HK (EVar 2) (curslot k + 16)%Z 8%nat (EVar 5).
    - kcell HK (EVar 2) (curslot k + 24)%Z 4%nat (ELit 0).
    - kcell HK (EVar 2) (curslot k + 28)%Z 4%nat (ELit 0).
    - kcell HK (EVar 2) (curslot k + 32)%Z 8%nat (ELit (W_of k)).
    - kcell HK (EVar 2) (freeslot k) 8%nat (mbx (freeslot k)).
    - kcell HK (EVar 2) (freeslot k + 8)%Z 8%nat (mbx (freeslot k)).
    - kcell HK (EVar 2) (freeslot k + 16)%Z 8%nat (ELit 0).
    - kcell HK (EVar 2) (freeslot k + 24)%Z 8%nat (ELit 0).
    - kcell HK (EVar 2) (freeslot k + 32)%Z 8%nat (ELit 0).
    - (* [comment removed for export] *) intros i Hi. replace (area + 104 + i)%Z with (bv_unsigned mb + 4200 + i)%Z by lia. apply Zarea. lia.
    - (* [comment removed for export] *)
      apply (defined_of_wr M area 4096); [lia | lia | lia |].
      intros d m Hd Hm. replace (area + d)%Z with (bv_unsigned mb + 4096 + d)%Z by lia. apply Wmb; assumption.
    - kcell HK (EVar 5) 0%Z 8%nat (mbx (curslot k)).
    - (* [comment removed for export] *)
      pose proof (Zhdr 0%Z ltac:(lia)) as Z0. rewrite Z.add_0_r in Z0.
      unfold cell. cbn [rdn]. rewrite Z0. reflexivity.
    - intros i Hi. replace (bv_unsigned B + 9 + i)%Z with (bv_unsigned B + 8 + (1 + i))%Z by lia. apply Zhdr. lia.
    - (* [comment removed for export] *)
      constructor; cbn zeta; intros.
      + replace (bv_unsigned B + 16 + 16 * (k + 1) - 4)%Z with (bv_unsigned B + (16 * (k + 2) - 4))%Z by lia.
        kbyte HK (EVar 5) (off_of k - 4)%Z (ELit 0).
      + replace (0 + 32 * res_code (65536 * 2 ^ k + 4096 - 16 - 4 - 65536 * 2 ^ k - 16 * (k + 1)))%Z with 160%Z
          by (unfold res_code; destruct (Z.ltb_spec (65536 * 2 ^ k + 4096 - 16 - 4 - 65536 * 2 ^ k - 16 * (k + 1)) 5); lia).
        replace (bv_unsigned B + 16 + 16 * (k + 1) - 3)%Z with (bv_unsigned B + (16 * (k + 2) - 3))%Z by lia.
        kbyte HK (EVar 5) (off_of k - 3)%Z (ELit 160).
      + change (rdn RSEGS M (Z_to_bv 64 (bv_unsigned B + 16 + 16 * (k + 1) - 2)) 2
                = Some (word_to_le_bytes 2 (Z_to_bv 64 ((65536 * 2 ^ k + 4096 - 16) * 0 / 16 + (k + 1)))))
          with (cell M (bv_unsigned B + 16 + 16 * (k + 1) - 2) 2 ((65536 * 2 ^ k + 4096 - 16) * 0 / 16 + (k + 1))).
        rewrite Z.mul_0_r. change (0 / 16)%Z with 0%Z.
        kcell HK (EVar 5) (off_of k - 2)%Z 2%nat (ELit (k + 1)).
      + replace (bv_unsigned B + 16 + 16 * (k + 1) + 65536 * 2 ^ k)%Z with (bv_unsigned B + (16 * (k + 2) + 65536 * 2 ^ k))%Z by lia.
        kbyte HK (EVar 5) (off_of k + cap_of k)%Z (ELit 0).
      + replace (bv_unsigned B + 16 + (65536 * 2 ^ k + 4096 - 16) - 4 - 5)%Z with (bv_unsigned B + (65536 * 2 ^ k + 4096 - 9))%Z by lia.
        kbyte HK (EVar 5) (nb_of k - 9)%Z (ELit 0).
      + change (rdn RSEGS M (Z_to_bv 64 (bv_unsigned B + 16 + (65536 * 2 ^ k + 4096 - 16) - 4 - 4)) 4
                = Some (word_to_le_bytes 4 (Z_to_bv 64 (65536 * 2 ^ k + 4096 - 16 - 4 - 65536 * 2 ^ k - 16 * (k + 1)))))
          with (cell M (bv_unsigned B + 16 + (65536 * 2 ^ k + 4096 - 16) - 4 - 4) 4 (65536 * 2 ^ k + 4096 - 16 - 4 - 65536 * 2 ^ k - 16 * (k + 1))).
        kcell HK (EVar 5) (nb_of k - 8)%Z 4%nat (ELit (res_of k)).
      + replace (bv_unsigned B + 16 - 3)%Z with (bv_unsigned B + 13)%Z by lia. kbyte HK (EVar 5) 13%Z (ELit 224).
      + change (rdn RSEGS M (Z_to_bv 64 (bv_unsigned B + 16 - 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (k + 1))))
          with (cell M (bv_unsigned B + 16 - 2) 2 (k + 1)).
        kcell HK (EVar 5) 14%Z 2%nat (ELit (k + 1)).
      + rewrite Z.mul_0_r. change (0 / 16)%Z with 0%Z. lia.
    - intros i Hi. replace (bv_unsigned B + (65536 * 2 ^ k + 4096) - 4 + i)%Z with (bv_unsigned B + (65536 * 2 ^ k + 4096 - 4) + i)%Z by lia.
      apply Ztail. lia.
    - apply (defined_of_wr M (bv_unsigned B) (65536 * 2 ^ k + 4096)); [lia | lia | lia |].
      intros d m Hd Hm. replace (bv_unsigned B + d)%Z with (bv_unsigned B + 0 + d)%Z by lia. apply WB; assumption.
    - (* [comment removed for export] *) rewrite AE. rewrite <- Zplus_mod_idemp_l, Amb. reflexivity.
    - exact AB.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact Wbrkv.
    - exact Wmasv.
    - eapply pres_cell; [exact P | lia | cbn; lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact Wtid].
    - exact Wtidr.
    - pose proof (kf_word _ _ _ HK (ELit 0) 0x31434%Z 4%nat (EVar 6) ltac:(kin)) as X. kclean X.
      pose proof (Z.mod_pos_bound (bv_unsigned e) (2 ^ 32) ltac:(lia)).
      exists (bv_unsigned e mod 2 ^ 32)%Z. split; [lia|]. unfold cell. rewrite X. f_equal. apply w2le_4_mod.
    - eapply pres_cell; [exact P | lia | cbn; lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact Wself].
    - eapply pres_cell; [exact P | lia | cbn; lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact Wcanary].
    - eapply pres_cell; [exact P | lia | cbn; lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact Wpagesz].
    - (* [comment removed for export] *)
      unfold img_clear_ivs in *. apply Forall_cons_iff in Wimg as [_ Wimg].
      apply Forall_cons; [exact (kf_img _ _ _ HK 0 0x1000 ltac:(kin))|].
      repeat (apply Forall_cons_iff in Wimg as [?C Wimg]).
      repeat (apply Forall_cons; [eapply pres_img_clear; [exact P | cbn; lia | cbn; lia | cbn; lia | unfold rd_cell; cbn; intros; lia | assumption] |]).
      apply Forall_nil.
  Qed.

  Lemma sp0_facts : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z /\ (bv_unsigned sp0 mod 16 = 0)%Z.
  Proof using Hvsp L. destruct Hvsp as (A & B_ & C). unfold sp_window_lo, sp_window_hi in *. lia. Qed.

  Lemma main_frame_k : main_frame (bv_unsigned sp0) M.
  Proof using Hvsp L MF RP.
    pose proof (rk_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as P. pose proof sp0_facts as [SP _].
    eapply main_frame_frame; [lia | lia | | exact MF].
    intros i Hi. apply P. right. rewrite u_small by lia. lia.
  Qed.

  Lemma stack_k : stack_writable M sp0.
  Proof using L RP.
    get_know extra Hlen HK.
    pose proof (kf_wr _ _ _ HK (EVar 0) (-8388608) 8388608 ltac:(kin)) as W. kclean W.
    intros d m Hd Hm. replace (bv_unsigned sp0 - 8388608 + d)%Z with (bv_unsigned sp0 + -8388608 + d)%Z by lia.
    apply W; assumption.
  Qed.

  Lemma target_vm_k_intro : target_vm_k k (bv_unsigned sp0) (bv_unsigned B) area VM.
  Proof using HL Hk L RP W0.
    pose proof (rk_vm _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as VS.
    pose proof VS as (Hres & Hlim & Hsp & rest & Hmaps & Hsm & Hlen & Hlive & (p & Hp & Hp1 & Hp2) & Hapart & Hseps).
    pose proof area_eq as AE. pose proof hk_nums as (Hc1 & Hc2 & _ & Enb & _). pose proof capk_split as CS.
    pose proof world_k_intro as WK. pose proof (wk_B_rng _ _ _ _ _ _ _ _ _ WK) as RB.
    rewrite Enb in *. unfold nbk in *.
    destruct (vm_stage_seps VM sp0 mb B (capk k + 4096) ltac:(lia) ltac:(lia) VS) as [SEPS NW].
    constructor.
    - exact Hres.
    - rewrite Hsp. symmetry. apply Z_to_bv_bv_unsigned.
    - exact Hlim.
    - rewrite Hmaps, Z_to_bv_bv_unsigned. left. reflexivity.
    - exists (fst p), (snd p). split; [rewrite Hmaps; right; destruct p; exact Hp | lia].
    - rewrite Hmaps. cbn [length]. lia.
    - rewrite Hmaps. constructor; [|exact Hsm]. cbn [fst snd]. rewrite u_small by lia. lia.
    - exact SEPS.
    - rewrite Hmaps. rewrite live_bytes_cons. rewrite u_small by lia. unfold nbk. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition modelk : Model := model_post VM stdin0 fs0 tid.

  Definition valsk : list word :=
    [sp0; p1; Z_to_bv 64 (bv_unsigned B + offk k); Z_to_bv 64 L; Z_to_bv 64 (capk k); tid;
     Z_to_bv 64 (hdr_b0 content); Z_to_bv 64 (hdr_b1 content); Z_to_bv 64 0] ++ junk_vals R.

  Lemma content_byte_k : forall j, (j < length content)%nat ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned B + offk k + Z.of_nat j)) 1%nat
    = Some (word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned (nth j content (Z_to_bv 8 0))))).
  Proof using HL Hk RP.
    intros j Hj. pose proof (rk_content _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as Hcont.
    pose proof hk_nums as (Hc1 & Hc2 & HLr & Enb & Ecap & Eoff & _). rewrite Eoff in Hcont.
    get_know extra Hlen HK.
    pose proof (kf_range _ _ _ HK (EVar 5) 0x52000 (CEIL - nb_of k) ltac:(kin)) as RB. cbn [edenot] in RB. rewrite ek5 in RB.
    unfold CEIL in RB. rewrite Enb in RB. unfold nbk, offk in *.
    pose proof (rdn_nth RSEGS M (length content) _ content j Hcont Hj) as H.
    rewrite w_add_nat in H. rewrite u_small in H by lia. rewrite w2le1_byte_k. exact H.
  Qed.

  Lemma hdrk_sym : regs_ok (ENVh content valsk) sr_HK R /\ know_ok RSEGS (ENVh content valsk) M kn_HK.
  Proof using HL Hk RP.
    destruct RP as [Rsp Rgp Rtp Rs0 Rs1 Rs2 Rs3 Rs4 Rs5 Rs6 Rs7 Hcont P HKx Hvm].
    pose proof hk_nums as (Hc1 & Hc2 & HLr & Enb & Ecap & Eoff & _).
    set (E := ENVh content valsk).
    assert (E0 : ev E 0 = sp0) by reflexivity.
    assert (E1 : ev E 1 = p1) by reflexivity.
    assert (E2 : ev E 2 = Z_to_bv 64 (bv_unsigned B + offk k)) by reflexivity.
    assert (E3 : ev E 3 = Z_to_bv 64 L) by reflexivity.
    assert (E4 : ev E 4 = Z_to_bv 64 (capk k)) by reflexivity.
    assert (E6 : ev E 6 = Z_to_bv 64 (hdr_b0 content)) by reflexivity.
    assert (E7 : ev E 7 = Z_to_bv 64 (hdr_b1 content)) by reflexivity.
    assert (EJ : forall i, (i < 32)%nat -> ev E (9 + i) = getr R (Z_to_bv 5 (Z.of_nat i))).
    { intros i Hi. unfold E, ENVh, valsk. cbn [ev]. unfold vals_ev.
      change (9 + i)%nat with (length [sp0; p1; Z_to_bv 64 (bv_unsigned B + offk k); Z_to_bv 64 L; Z_to_bv 64 (capk k); tid;
                                        Z_to_bv 64 (hdr_b0 content); Z_to_bv 64 (hdr_b1 content); Z_to_bv 64 0] + i)%nat.
      rewrite app_nth2_plus. unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi.
      reflexivity. }
    split.
    - apply UbReadBase.regs_ok_by_index. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
        cbn [nth sr_HK UbReadBase.all_regs].
      all: try (lazymatch goal with |- _ = edenot _ (J ?n) =>
                  unfold J; change (edenot E (EVar (9 + n))) with (ev E (9 + n)%nat); rewrite EJ by lia; reflexivity end).
      all: try (lazymatch goal with |- _ = edenot _ (spx ?z) =>
                  unfold spx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot]; rewrite E0;
                  rewrite Rsp; f_equal; lia end).
      all: try (change (edenot E (EVar 1)) with (ev E 1); rewrite E1; assumption).
      all: try (change (edenot E (EVar 2)) with (ev E 2); rewrite E2; rewrite <- Eoff; assumption).
      all: try (change (edenot E (EVar 3)) with (ev E 3); rewrite E3; assumption).
      all: try (change (edenot E (EVar 4)) with (ev E 4); rewrite E4; rewrite <- Ecap; assumption).
      all: cbn [edenot]; first [assumption | apply getr_zero | reflexivity].
    - get_know extra Hlen HK.
      pose proof (kf_range _ _ _ HK (EVar 5) 0x52000 (CEIL - nb_of k) ltac:(kin)) as RB. cbn [edenot] in RB. rewrite ek5 in RB.
      unfold CEIL in RB. rewrite Enb in RB.
      pose proof (bv_unsigned_in_range _ (nth 0 content (Z_to_bv 8 0))) as B0.
      pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1.
      change (bv_modulus 8) with 256%Z in B0, B1.
      unfold nbk, offk in *.
      unfold kn_HK. repeat apply Forall_cons; try apply Forall_nil.
      + apply krange_intro. change (edenot E (EVar 2)) with (ev E 2). rewrite E2. rewrite u_small by lia. lia.
      + apply krange_intro. change (edenot E (EVar 3)) with (ev E 3). rewrite E3. unfold L. rewrite u_small by lia. lia.
      + cbn [kentry_ok]. split; [lia|]. split; [apply flat_intro; change (edenot E (EVar 2)) with (ev E 2); rewrite ?E2; rewrite ?u_small by lia; lia|].
        unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev E 2) with (Z_to_bv 64 (bv_unsigned B + 16 * (k + 2))).
        change (ev E 6) with (Z_to_bv 64 (hdr_b0 content)). unfold hdr_b0. rewrite u_small by lia.
        replace (bv_unsigned B + 16 * (k + 2) + 0)%Z with (bv_unsigned B + 16 * (k + 2) + Z.of_nat 0)%Z by lia.
        apply content_byte_k. lia.
      + cbn [kentry_ok]. split; [lia|]. split; [apply flat_intro; change (edenot E (EVar 2)) with (ev E 2); rewrite ?E2; rewrite ?u_small by lia; lia|].
        unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev E 2) with (Z_to_bv 64 (bv_unsigned B + 16 * (k + 2))).
        change (ev E 7) with (Z_to_bv 64 (hdr_b1 content)). unfold hdr_b1. rewrite u_small by lia.
        replace (bv_unsigned B + 16 * (k + 2) + 1)%Z with (bv_unsigned B + 16 * (k + 2) + Z.of_nat 1)%Z by lia.
        apply content_byte_k. lia.
      + apply krange_intro. change (edenot E (EVar 6)) with (ev E 6). rewrite E6. unfold hdr_b0. rewrite u_small by lia. lia.
      + apply krange_intro. change (edenot E (EVar 7)) with (ev E 7). rewrite E7. unfold hdr_b1. rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUELh STOPSh scr NX true.

  Theorem header_ok_k : forall K,
    (forall R' M', target_pre_k k (bv_unsigned sp0) (bv_unsigned B) area brkv mas (bv_unsigned tid) (bv_unsigned sec) (bv_unsigned cnr)
                                content R' M' ->
       target_vm_k k (bv_unsigned sp0) (bv_unsigned B) area VM ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x12db8) M' (seg_rom RSEGS)) modelk) K) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12be4) M (seg_rom RSEGS)) modelk) K.
  Proof using HL Hk Hvsp MF RP W0.
    intros K HK_T. destruct hdrk_sym as [HR HK].
    pose proof (hdr_cfglen_range content) as CR.
    pose proof hk_nums as (Hc1 & Hc2 & HLr & Enb & Ecap & Eoff & _).
    pose proof sp0_facts as [SP SPA].
    pose proof (u64_range B) as UB.
    pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1. change (bv_modulus 8) with 256%Z in B1.
    pose proof world_k_intro as WK. pose proof (wk_B_rng _ _ _ _ _ _ _ _ _ WK) as RB. unfold nbk in RB.
    pose proof capk_split as CS. unfold L in HLr.
    (* [comment removed for export] *)
    set (cb := fun i : nat => Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (hdr_cfglen content) + 2 + i) content (Z_to_bv 8 0)))).
    assert (HL0 : length valsk = 41%nat) by (unfold valsk; rewrite length_app, junk_vals_length; reflexivity).
    pose proof (env_app_regs valsk [cb 1%nat; cb 0%nat; cb 2%nat; cb 3%nat] (blobs_ev [content]) sr_HK R
                  ltac:(rewrite HL0; vm_compute; reflexivity) HR) as HR1.
    pose proof (env_app_know RSEGS valsk [cb 1%nat; cb 0%nat; cb 2%nat; cb 3%nat] (blobs_ev [content]) M kn_HK
                  ltac:(rewrite HL0; vm_compute; reflexivity) HK) as HK1.
    clear HR HK.
    set (vals := valsk ++ [cb 1%nat; cb 0%nat; cb 2%nat; cb 3%nat]) in *.
    change (Env (vals_ev vals) (blobs_ev [content])) with (ENVh content vals) in HR1, HK1.
    rename HR1 into HR. rename HK1 into HK.
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P2 : vals_ev vals 2 = Z_to_bv 64 (bv_unsigned B + offk k)) by reflexivity.
    assert (P3 : vals_ev vals 3 = Z_to_bv 64 L) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 (capk k)) by reflexivity.
    assert (P6 : vals_ev vals 6 = Z_to_bv 64 (hdr_b0 content)) by reflexivity.
    assert (P7 : vals_ev vals 7 = Z_to_bv 64 (hdr_b1 content)) by reflexivity.
    assert (PB41 : vals_ev vals 41 = cb 1%nat).
    { unfold vals. replace 41%nat with (length valsk + 0)%nat by (rewrite HL0; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (PB42 : vals_ev vals 42 = cb 0%nat).
    { unfold vals. replace 42%nat with (length valsk + 1)%nat by (rewrite HL0; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (PB43 : vals_ev vals 43 = cb 2%nat).
    { unfold vals. replace 43%nat with (length valsk + 2)%nat by (rewrite HL0; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (PB44 : vals_ev vals 44 = cb 3%nat).
    { unfold vals. replace 44%nat with (length valsk + 3)%nat by (rewrite HL0; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    clearbody vals.
    pose proof (cfglen_val content vals P6 P7) as CV.
    unfold offk in P2.
    (* [comment removed for export] *)
    assert (CB : forall i, (i < 4)%nat ->
      rdn RSEGS M (Z_to_bv 64 (bv_unsigned B + 16 * (k + 2) + hdr_cfglen content + 2 + Z.of_nat i)) 1%nat
      = Some [nth (Z.to_nat (hdr_cfglen content) + 2 + i) content (Z_to_bv 8 0)]).
    { intros i Hi.
      replace (bv_unsigned B + 16 * (k + 2) + hdr_cfglen content + 2 + Z.of_nat i)%Z
        with (bv_unsigned B + offk k + Z.of_nat (Z.to_nat (hdr_cfglen content) + 2 + i))%Z by (unfold offk; lia).
      rewrite content_byte_k by lia. rewrite w2le1_byte_k. reflexivity. }
    (* [comment removed for export] *)
    run_block_keep scr_fall 41%nat.
    all: try (unfold sc_denot; fold cfglen_x).
    (* [comment removed for export] *)
    all: try (lazymatch goal with
              | |- branch_taken _ _ _ = false =>
                  cbn [edenot]; rewrite CV; change (ev (ENVh content vals) 3) with (vals_ev vals 3); rewrite P3;
                  rewrite alu_add; unfold v_add; cbn [branch_taken]; unfold bv_ltu;
                  rewrite (u_small (hdr_cfglen content)) by lia; change (bv_unsigned (Z_to_bv 64 6)) with 6%Z;
                  rewrite !u_small by lia; apply Z.ltb_ge; lia
              end).
    (* [comment removed for export] *)
    all: try (lazymatch goal with
              | |- exists bs, rdn _ _ (adenot _ (SA _ ?o)) 1 = Some bs /\ _ =>
                  let i := eval vm_compute in (Z.to_nat (o - 2)) in
                  eexists; split;
                  [ unfold adenot, v_addi; cbn [a_base a_off edenot]; rewrite CV;
                    change (ev (ENVh content vals) 2) with (vals_ev vals 2); rewrite P2;
                    rewrite alu_add; unfold v_add;
                    rewrite (u_small (hdr_cfglen content)) by lia; rewrite (u_small (bv_unsigned B + 16 * (k + 2))) by lia; rewrite !u_small by lia;
                    replace (bv_unsigned B + 16 * (k + 2) + hdr_cfglen content + o)%Z
                      with (bv_unsigned B + 16 * (k + 2) + hdr_cfglen content + 2 + Z.of_nat i)%Z by lia;
                    apply (CB i); lia
                  | lazymatch goal with |- _ = edenot _ (EVar ?n) => change (edenot (ENVh content vals) (EVar n)) with (vals_ev vals n) end;
                    first [rewrite PB41 | rewrite PB42 | rewrite PB43 | rewrite PB44];
                    unfold cb, extz; cbn [bytes_le_to_Z Z.shiftl]; rewrite Z.lor_0_r; reflexivity ]
              | |- flat _ (SA _ ?o) _ =>
                  unfold flat, estart, elenZ; cbn [a_base a_off]; fold cfglen_x; cbn [edenot]; rewrite CV;
                  change (ev (ENVh content vals) 2) with (vals_ev vals 2); rewrite P2;
                  rewrite alu_add; unfold v_add; rewrite (u_small (hdr_cfglen content)) by lia; rewrite (u_small (bv_unsigned B + 16 * (k + 2))) by lia; rewrite !u_small by lia; lia
              end).
    (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mx _) _) _ =>
      lazymatch goal with EQ : Mx = _ |- _ => cbn [mem_denot] in EQ; subst Mx end end.
    apply HK_T; [| exact target_vm_k_intro].
    assert (A6 : edenot (ENVh content vals) (EAlu ALU_ADD (EAlu ALU_ADD (EVar 2) cfglen_x) (ELit 6))
                  = Z_to_bv 64 (bv_unsigned B + offk k + 6 + hdr_cfglen content)).
    { cbn [edenot]. rewrite CV. change (ev (ENVh content vals) 2) with (vals_ev vals 2); rewrite P2.
      rewrite !alu_add. unfold v_add. rewrite (alu_add (Z_to_bv 64 (bv_unsigned B + 16 * (k + 2)))). unfold v_add.
      rewrite (u_small (hdr_cfglen content)) by lia. rewrite (u_small (bv_unsigned B + 16 * (k + 2))) by lia.
      rewrite (u_small (bv_unsigned B + 16 * (k + 2) + hdr_cfglen content)) by lia. change (bv_unsigned (Z_to_bv 64 6)) with 6%Z.
      f_equal. unfold offk. lia. }
    assert (APL : edenot (ENVh content vals) (EAlu ALU_ADD (EAlu ALU_ADD (EVar 3) (EMd M_MUL (ELit (-1)) cfglen_x)) (ELit (-6)))
                  = Z_to_bv 64 (hdr_paylen content)).
    { cbn [edenot]. rewrite CV. change (ev (ENVh content vals) 3) with (vals_ev vals 3); rewrite P3.
      rewrite !alu_add, m_mul. unfold v_add, v_mul. rewrite ?alu_add. unfold v_add.
      apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
      unfold L. rewrite (Z.mod_small (Z.of_nat (length content))), (Z.mod_small (hdr_cfglen content)) by lia.
      change ((-1) mod 2 ^ 64)%Z with 18446744073709551615%Z. change ((-6) mod 2 ^ 64)%Z with 18446744073709551610%Z.
      rewrite Zplus_mod_idemp_l.
      replace (Z.of_nat (length content) + (18446744073709551615 * hdr_cfglen content) mod 2 ^ 64 + 18446744073709551610)%Z
        with (Z.of_nat (length content) + 18446744073709551610 + (18446744073709551615 * hdr_cfglen content) mod 2 ^ 64)%Z by lia.
      rewrite Zplus_mod_idemp_r.
      apply (mod_eq_shift _ _ (hdr_cfglen content + 1)); [lia|]. unfold hdr_paylen. lia. }
    assert (A2 : edenot (ENVh content vals) (EAlu ALU_ADD (EVar 2) (ELit 2)) = Z_to_bv 64 (bv_unsigned B + offk k + 2)).
    { rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev (ENVh content vals) 2) with (vals_ev vals 2).
      rewrite P2. rewrite u_small by lia. unfold offk. f_equal; lia. }
    constructor.
    - regv HR (1 : reg). reflexivity.
    - regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev (ENVh content vals) 0) with (vals_ev vals 0).
      rewrite P0. f_equal; lia.
    - regv HR (3 : reg). reflexivity.
    - regv HR (4 : reg). reflexivity.
    - regv HR (10 : reg). exact A2.
    - regv HR (11 : reg). exact CV.
    - regv HR (12 : reg). exact A6.
    - regv HR (13 : reg). exact APL.
    - regv HR (8 : reg). exact A2.
    - regv HR (9 : reg). change (edenot (ENVh content vals) (EVar 2)) with (vals_ev vals 2). rewrite P2. unfold offk. reflexivity.
    - regv HR (18 : reg). exact CV.
    - regv HR (19 : reg). exact A6.
    - regv HR (20 : reg). exact APL.
    - regv HR (21 : reg). change (edenot (ENVh content vals) (EExt true 0 1 (EVar 7))) with (sx8F (vals_ev vals 7)).
      rewrite P7. apply sx8F_val. unfold hdr_b1. lia.
    - regv HR (22 : reg). reflexivity.
    - regv HR (23 : reg). reflexivity.
    - exact sp0_facts.
    - (* [comment removed for export] *)
      get_know extra Hlen HKk.
      pose proof (kf_disj _ _ _ HKk (EVar 0) (-8388608) BAND (EVar 5) 0 (nb_of k) ltac:(kin)) as DBand. kclean DBand.
      pose proof (kf_range _ _ _ HKk (EVar 5) 0x52000 (CEIL - nb_of k) ltac:(kin)) as RB5. cbn [edenot] in RB5. rewrite ek5 in RB5.
      unfold BAND, CEIL in *. rewrite Enb in *. unfold nbk in *. lia.
    - lia.
    - exact HL.
    - pose proof stack_k as ST. intros d m Hd Hm. apply ST; assumption.
    - exact main_frame_k.
    - exact WK.
    - pose proof (rk_content _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as Hcont. rewrite Eoff in Hcont. exact Hcont.
  Qed.

  (* [comment removed for export] *)
  Theorem header_phase_k_sec :
    (forall R' M', target_pre_k k (bv_unsigned sp0) (bv_unsigned B) area brkv mas (bv_unsigned tid) (bv_unsigned sec) (bv_unsigned cnr)
                                content R' M' ->
       target_vm_k k (bv_unsigned sp0) (bv_unsigned B) area VM ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x12db8) M' (seg_rom RSEGS)) modelk) (t_target content fs0)) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12be4) M (seg_rom RSEGS)) modelk) (t_body content fs0).
  Proof using HL Hk Hvsp MF RP W0.
    intros HT. rewrite (t_body_target_k k content fs0 Hk HL). apply header_ok_k. exact HT.
  Qed.
End HeaderK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem header_phase_k {AMB : Amb} : forall (k : Z) (sp0 p1 mb gm B e tid sec cnr : word) (area brkv mas : Z) (content : list byte)
    (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps)
    (stdin0 : InputStream) (fs0 : Fs),
  (1 <= k <= 10)%Z ->
  valid_sp sp0 ->
  read_post k sp0 p1 mb gm B e sec cnr content M0 R M VM ->
  world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned sec) (bv_unsigned cnr) M0 ->
  main_frame (bv_unsigned sp0) M0 ->
  (capk (k - 1) <= Z.of_nat (length content) < capk k)%Z ->
  (forall R' M', target_pre_k k (bv_unsigned sp0) (bv_unsigned B) area brkv mas (bv_unsigned tid) (bv_unsigned sec) (bv_unsigned cnr)
                              content R' M' ->
     target_vm_k k (bv_unsigned sp0) (bv_unsigned B) area VM ->
     realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x12db8) M' (seg_rom RSEGS)) (model_post VM stdin0 fs0 tid))
                (t_target content fs0)) ->
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12be4) M (seg_rom RSEGS)) (model_post VM stdin0 fs0 tid))
             (t_body content fs0).
Proof using .
  intros k sp0 p1 mb gm B e tid sec cnr area brkv mas content M0 R M VM stdin0 fs0 Hk Hvsp RP W0 MF HL HT.
  eapply header_phase_k_sec; eassumption.
Qed.

(* [comment removed for export] *)
Theorem world_k_of_read_post : forall (k : Z) (sp0 p1 mb gm B e tid sec cnr : word) (area brkv mas : Z) (content : list byte)
    (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps),
  (1 <= k <= 10)%Z -> valid_sp sp0 ->
  read_post k sp0 p1 mb gm B e sec cnr content M0 R M VM ->
  world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned sec) (bv_unsigned cnr) M0 ->
  main_frame (bv_unsigned sp0) M0 ->
  (capk (k - 1) <= Z.of_nat (length content) < capk k)%Z ->
  area = (bv_unsigned mb + 4096)%Z
  /\ world_k k area (bv_unsigned B) brkv mas (bv_unsigned tid) (bv_unsigned sec) (bv_unsigned cnr) M
  /\ main_frame (bv_unsigned sp0) M
  /\ stack_writable M sp0
  /\ target_vm_k k (bv_unsigned sp0) (bv_unsigned B) area VM.
Proof using .
  intros k sp0 p1 mb gm B e tid sec cnr area brkv mas content M0 R M VM Hk Hvsp RP W0 MF HL.
  split; [eapply area_eq; eassumption|].
  split; [eapply world_k_intro; eassumption|].
  split; [eapply main_frame_k; eassumption|].
  split; [eapply stack_k; eassumption|].
  eapply target_vm_k_intro; eassumption.
Qed.
End WithFP2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End UbHeaderK.
From Stdlib Require String.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Nodes Hoare Frame SpecConsts FileSim AgentLib SymDriveH4 LibWritev UbExitBase UbStdioDefs UbExit UbLibStdioCall RefMemcpyLib UbMemcpyBase UbMemcpy LibTail.

Module UbRefused_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveH4 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbLibStdioCall.
Unset Lia Cache.
Import ListNotations. Import SX2. Import SX2S.
#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section WithFP1. Context {FP : PropExec.FPState}.
Definition STOPS : list Z := [0x1e6dc; 0x1eae0; 0x1ebd8; 0x1ec1c; 0x12f88; 0x18e44; 0x1755c; 0x19ae4]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition KEPT_MC : list nat := map ridx callee_kept.
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
Definition srRF_base : list expr :=
  [ELit 0; ELit 0; spx (-128); ELit 0x10800; ELit 0x314d8; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0].
Definition KEPT_RF : list nat := [2; 3; 4]%nat.
Definition srRF0 : list expr := Eval vm_compute in sr_after_call_j srRF_base KEPT_RF 6.
Definition knRF0 : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) 8388608;
   KWr (SA (ELit 0) 0x21000) 0x31000;
   KImg 0x10000 0x21380; KImg 0x21381 0x213c9; KImg 0x313c9 0x31408; KImg 0x514e0 0x51500;
   KWord (SA (ELit 0) 0x31410) 8 (ELit 0x31410);
   KWord (SA (ELit 0) 0x31430) 4 (EVar 5);
   KImg 0x3143c 0x31488; KImg 0x31490 0x314a8; KImg 0x314b0 0x314c8;
   KImg 0x314d8 0x314e8; KImg 0x314f0 0x514e0; KImg 0x51518 0x51744;
   KWord (SA (ELit 0) 0x51748) 8 (EVar 38);
   KImg 0x51750 0x51758; KImg 0x51769 0x51770; KImg 0x51778 0x51780; KImg 0x51790 0x51798;
   KWord (SA (ELit 0) 0x51798) 8 (ELit 4096);
   KImg 0x517a0 0x517d0; KImg 0x517d8 0x517e0;
   KImg 0x51830 0x51990; KImg 0x51998 0x51b10; KImg 0x51b18 0x51b70; KImg 0x51b71 0x51b78;
   KImg 0x51b88 0x52000;
   KRange (EVar 5) 1 4194303].
(* [comment removed for export] *)
Definition ssB0 : sym_state := SS 0x12d30 srRF0 [] knRF0 39.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRF0.
(* [comment removed for export] *)
Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-548)) 2 (ELit 8253);
   SE (SA (EVar 0) (-552)) 4 (ELit 1042314357);
   SE (SA (EVar 0) (-560)) 8 (ELit 8101528366825958499)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : sym_state := SS 0x19794 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0x19794 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_MC 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0x19794 srE0 [] knD 135.
Definition rE := Eval vm_compute in run scr0 ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knD.
(* [comment removed for export] *)
Definition logM4 : list sentry := [SE (SA (EVar 0) (-546)) 8 (ELit 3762256352692483894)].
Definition knF0 : list kentry := Eval vm_compute in fst (fst (carry logM4 knE [])).
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0x19794 srF0 [] knF0 167.
Definition rF := Eval vm_compute in run scr0 ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knF0.
Definition logM5 : list sentry :=
  [SE (SA (EVar 0) (-530)) 8 (ELit 748834984615634290);
   SE (SA (EVar 0) (-538)) 8 (ELit 2318354787771965984)].
Definition knG0 : list kentry := Eval vm_compute in fst (fst (carry logM5 knF [])).
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0x19794 srG0 [] knG0 199.
Definition rG := Eval vm_compute in run scr0 ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition scRF : stdio_res := Eval vm_compute in
  match stdio_call 199 srG knG with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srH0 : list expr := Eval vm_compute in sc_sr scRF.
Definition knH0 : list kentry := Eval vm_compute in sc_kn scRF.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS (sc_ret scRF) srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.

Lemma itinerary_rf :
  (s_pc (fst (fst rB)), snd (fst rB)) = (0x1e6dc%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x1e6dc%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x1e6dc%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE)) = (0x1e6dc%Z, [])
  /\ (s_pc (fst (fst rF)), snd (fst rF)) = (0x1e6dc%Z, [])
  /\ (s_pc (fst (fst rG)), snd (fst rG)) = (0x19ae4%Z, [])
  /\ stdio_call 199 srG knG = Some scRF
  /\ (sc_ret scRF, sc_f scRF, sc_fd scRF) = (0x19e44%Z, 0x21198%Z, 2%Z)
  /\ (sc_wb scRF, sc_wp scRF, sc_l scRF) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-522)), ELit 0)
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0x1755c%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.
End WithFP1.
End UbRefused_defs.

Module UbRefused.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SpecConsts OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveH4 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeLaws OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWritev OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExitBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbStdioDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbLibStdioCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMemcpyBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMemcpy OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTail OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbReadStage OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbWorld.
Import UbRefused_defs.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.

(* [comment removed for export] *)
Definition ENV {FP : PropExec.FPState} (BL : list (list byte)) (vals : list word) : env := Env (vals_ev vals) (blobs_ev BL).


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
Definition PRE14 : list byte := s2b "cli: input >= "%string.
Definition DIG8 : list byte := s2b "67108864"%string.
Definition SUF16 : list byte := s2b " bytes, refused"%string ++ [Z_to_bv 8 10].

Lemma msg_refused_split : msg_refused = PRE14 ++ DIG8 ++ SUF16.
Proof. reflexivity. Qed.

Lemma PRE14_words :
  word_to_le_bytes 8 (Z_to_bv 64 8101528366825958499) ++ word_to_le_bytes 4 (Z_to_bv 64 1042314357)
  ++ word_to_le_bytes 2 (Z_to_bv 64 8253) = PRE14.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
Lemma DIG8_word : word_to_le_bytes 8 (Z_to_bv 64 3762256352692483894) = DIG8.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
Lemma DIG8_bytes :
  word_to_le_bytes 1 (Z_to_bv 64 54) ++ word_to_le_bytes 1 (Z_to_bv 64 55) ++ word_to_le_bytes 1 (Z_to_bv 64 49)
  ++ word_to_le_bytes 1 (Z_to_bv 64 48) ++ word_to_le_bytes 1 (Z_to_bv 64 56) ++ word_to_le_bytes 1 (Z_to_bv 64 56)
  ++ word_to_le_bytes 1 (Z_to_bv 64 54) ++ word_to_le_bytes 1 (Z_to_bv 64 52) = DIG8.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
Lemma SUF16_words :
  word_to_le_bytes 8 (Z_to_bv 64 2318354787771965984) ++ word_to_le_bytes 8 (Z_to_bv 64 748834984615634290) = SUF16.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
Lemma pre14_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x1033d) 14 = Some PRE14.
Proof. vm_compute. reflexivity. Qed.
Lemma suf16_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x1034d) 16 = Some SUF16.
Proof. vm_compute. reflexivity. Qed.
Lemma PRE14_len : length PRE14 = 14%nat. Proof. reflexivity. Qed.
Lemma DIG8_len : length DIG8 = 8%nat. Proof. reflexivity. Qed.
Lemma SUF16_len : length SUF16 = 16%nat. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition rf_ivs : list (Z * Z) :=
  [(0x10000,0x21380); (0x21381,0x213c9); (0x313c9,0x31408); (0x514e0,0x51500); (0x3143c,0x31488); (0x31490,0x314a8);
   (0x314b0,0x314c8); (0x314d8,0x314e8); (0x314f0,0x514e0); (0x51518,0x51744); (0x51750,0x51758); (0x51769,0x51770);
   (0x51778,0x51780); (0x51790,0x51798); (0x517a0,0x517d0); (0x517d8,0x517e0);
   (0x51830,0x51990); (0x51998,0x51b10); (0x51b18,0x51b70); (0x51b71,0x51b78); (0x51b88,0x52000)]%Z.

Section Refused.
  Variable sp0 : word.
  Ltac at_addr k H :=
    lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with (bv_unsigned sp0 + k)%Z by lia; exact H end.
  Variable BL : list (list byte).
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let T : TSet := t_emit (W 2 msg_refused) (t_exit (exit_code 2) (m_fs model)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segH : forall vals R M,
    length vals = 231%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srH0 R -> know_ok RSEGS (ENV BL vals) M knH0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x19e44) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 231%nat.
    apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model)))).
    2:{ cbn [W map].
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity).
        apply t_eq_sym. apply t_emit_nil_exit. }
    apply ref_exit_Z.
    pose proof (know_nth RSEGS _ _ knH ltac:(let i := kidx knH (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid.
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x314d8), (bv_unsigned (vals_ev vals 5)),
           (Z_to_bv 64 0), (Z_to_bv 64 0).
    split; [|split; [exact Hh|split; [exact Hlazy|]]].
    + constructor.
      * regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
        rewrite P0. f_equal; lia.
      * regv HR (4 : reg). reflexivity.
      * regv HR (10 : reg). reflexivity.
      * rewrite u_small by lia. lia.
      * rewrite u_small by lia. lia.
      * rewrite u_small by lia.
        pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knH ltac:(let i := kidx knH (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                      _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia. exact Hst.
      * lit_u. lia.
      * lit_u. lia.
      * lia.
      * lit_u. change (201944 - 168)%Z with 0x31430%Z.
        krd HK 0x31430%Z 4%nat Htc. rewrite Htc. cbn [ev ENV].
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia).
        rewrite Z_to_bv_bv_unsigned. reflexivity.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * repeat split; krd_solve HK.
      * repeat split; krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * left. unfold ax_empty. krd_solve HK.
    + left. split; [reflexivity|].
      exists (Z_to_bv 64 0), (Z_to_bv 64 0). repeat split; krd_solve HK.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segG : forall vals R M,
    length vals = 199%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srG0 R -> know_ok RSEGS (ENV BL vals) M knG0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x19794) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 199%nat.
    (* [comment removed for export] *)
    krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-552)%Z 4%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-548)%Z 2%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-546)%Z 8%nat Hw3. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-538)%Z 8%nat Hw4. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-530)%Z 8%nat Hw5. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0, Hw1, Hw2, Hw3, Hw4, Hw5.
    cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2, Hw3, Hw4, Hw5.
    rewrite P0 in Hw0, Hw1, Hw2, Hw3, Hw4, Hw5.
    assert (MSG : rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 + -560)) ((8 + (4 + 2)) + (8 + (8 + 8)))
                  = Some msg_refused).
    { rewrite msg_refused_split, <- PRE14_words, <- DIG8_word, <- SUF16_words.
      apply rdn_app_Z; [ | | lia | lia].
      - apply rdn_app_Z; [exact Hw0 | | lia | lia].
        apply rdn_app_Z; [at_addr (-552)%Z Hw1 | at_addr (-548)%Z Hw2 | lia | lia].
      - apply rdn_app_Z; [at_addr (-546)%Z Hw3 | | lia | lia].
        apply rdn_app_Z; [at_addr (-538)%Z Hw4 | at_addr (-530)%Z Hw5 | lia | lia]. }
    (* [comment removed for export] *)
    unfold T.
    replace (W 2 msg_refused) with (map (WriteEv (Z_to_bv 64 2)) (msg_refused ++ []))
      by (unfold W; rewrite app_nil_r; reflexivity).
    pose proof itinerary_rf as (_ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srG knG Rc Mc model scRF msg_refused []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srG knG) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scRF];
      change (@length byte msg_refused) with 38%nat; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. reflexivity.
    - pose proof rw_bytes_max_ge17. lia.
    - lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      change 38%nat with ((8 + (4 + 2)) + (8 + (8 + 8)))%nat. exact MSG.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (rf_segH (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma memcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV BL vals) M logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 560)) PRE14.
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- PRE14_words. cbn [mem_denot logM1]. rewrite !wbytes_app.
    unfold adenot, v_addi, at_. cbn [a_base a_off edenot ev ENV length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite P0.
    rewrite !length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unorm.
    repeat (f_equal; try (f_equal; lia)).
  Qed.
  Lemma memcpy4_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV BL vals) M logM4 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 546)) DIG8.
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- DIG8_word. cbn [mem_denot logM4].
    unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0.
    repeat (f_equal; try (f_equal; lia)).
  Qed.
  Lemma memcpy5_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV BL vals) M logM5 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 538)) SUF16.
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- SUF16_words. cbn [mem_denot logM5]. rewrite !wbytes_app.
    unfold adenot, v_addi, at_. cbn [a_base a_off edenot ev ENV length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite P0.
    rewrite !length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unorm.
    repeat (f_equal; try (f_equal; lia)).
  Qed.

  (* [comment removed for export] *)
  Ltac after_memcpy HL Hms Hkeep :=
    replace (Z_to_bv 64 124636) with (0x1e6dc : word) by (apply bv_eq; reflexivity);
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]; clear Hms;
    replace (0x19794 : word) with (Z_to_bv 64 0x19794) by (apply bv_eq; reflexivity);
    lazymatch goal with H : regs_ok ?E ?sr ?Rc |- realizes _ (mkCfg (mkst ?R2 _ _ _) _) _ =>
      pose proof (regs_after_keeps _ (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) H Hkeep callee_kept_no0) as HR2;
      rewrite HL in HR2; clear H Hkeep; rename HR2 into HR
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segF : forall vals R M,
    length vals = 167%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srF0 R -> know_ok RSEGS (ENV BL vals) M knF0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x19794) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 167%nat.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 538)).
    assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x1034d) 16 = Some SUF16).
    { rewrite (kimg_rdn RSEGS (ENV BL vals) _ knF ltac:(let i := kidx knF (is_kimg_cov 0x1034d 16) in exact i)
                 _ _ 0x1034d 16 HK eq_refl) by (cbn; lia). apply suf16_img. }
    assert (Hdst : store_ok RSEGS M dst 16 = true).
    { pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knF ltac:(let i := kidx knF (is_kwr_cov (EVar 0) (-538) 16) in exact i)
                    _ _ _ (-538) 16 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 538)%Z with (bv_unsigned sp0 + -538)%Z by lia. exact Hst. }
    assert (MC : mcH M dst (Z_to_bv 64 0x1034d) 16 SUF16).
    { constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x19794 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x1034d) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 16) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst (Z_to_bv 64 0x1034d) 16 _ (seg_rom RSEGS) MC Rc (0x19794 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    after_memcpy HL Hms Hkeep.
    assert (HK2 : know_ok RSEGS (ENV BL vals) (wbytes M dst SUF16) knG0).
    { subst dst. rewrite <- (memcpy5_denot vals M P0).
      eapply (carry_after RSEGS (ENV BL vals) M logM5 knF [] knG0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat logM5].
      repeat match goal with
             | |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
             | |- (_ <= _)%nat => lia
             | |- True => exact I
             | |- _ /\ _ => split
             end. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M dst SUF16) knG0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 199%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    eapply (rf_segG vals1); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segE : forall vals R M,
    length vals = 135%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srE0 R -> know_ok RSEGS (ENV BL vals) M knD ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x19794) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 135%nat.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 546)).
    set (src := Z_to_bv 64 (bv_unsigned sp0 - 952)).
    (* [comment removed for export] *)
    krdv HK 0%nat (-952)%Z 1%nat Hd0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-951)%Z 1%nat Hd1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-950)%Z 1%nat Hd2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-949)%Z 1%nat Hd3. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-948)%Z 1%nat Hd4. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-947)%Z 1%nat Hd5. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-946)%Z 1%nat Hd6. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-945)%Z 1%nat Hd7. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hd0, Hd1, Hd2, Hd3, Hd4, Hd5, Hd6, Hd7.
    cbn [a_base a_off edenot ev ENV] in Hd0, Hd1, Hd2, Hd3, Hd4, Hd5, Hd6, Hd7.
    rewrite P0 in Hd0, Hd1, Hd2, Hd3, Hd4, Hd5, Hd6, Hd7.
    assert (Hsrc : rdn RSEGS M src (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))) = Some DIG8).
    { subst src. replace (bv_unsigned sp0 - 952)%Z with (bv_unsigned sp0 + -952)%Z by lia. rewrite <- DIG8_bytes.
      apply rdn_app_Z; [exact Hd0 | | lia | lia].
      apply rdn_app_Z; [at_addr (-951)%Z Hd1 | | lia | lia].
      apply rdn_app_Z; [at_addr (-950)%Z Hd2 | | lia | lia].
      apply rdn_app_Z; [at_addr (-949)%Z Hd3 | | lia | lia].
      apply rdn_app_Z; [at_addr (-948)%Z Hd4 | | lia | lia].
      apply rdn_app_Z; [at_addr (-947)%Z Hd5 | | lia | lia].
      apply rdn_app_Z; [at_addr (-946)%Z Hd6 | at_addr (-945)%Z Hd7 | lia | lia]. }
    assert (Hdst : store_ok RSEGS M dst 8 = true).
    { pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knE ltac:(let i := kidx knE (is_kwr_cov (EVar 0) (-546) 8) in exact i)
                    _ _ _ (-546) 8 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 546)%Z with (bv_unsigned sp0 + -546)%Z by lia. exact Hst. }
    assert (MC : mcH M dst src 8 DIG8).
    { constructor; subst dst src; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x19794 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = src)
        by (regv HR (11 : reg); subst src; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A12 : getr Rc 12 = Z_to_bv 64 8) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst src 8 _ (seg_rom RSEGS) MC Rc (0x19794 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    after_memcpy HL Hms Hkeep.
    assert (HK2 : know_ok RSEGS (ENV BL vals) (wbytes M dst DIG8) knF0).
    { subst dst. rewrite <- (memcpy4_denot vals M P0).
      eapply (carry_after RSEGS (ENV BL vals) M logM4 knE [] knF0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat logM4].
      repeat match goal with
             | |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
             | |- (_ <= _)%nat => lia
             | |- True => exact I
             | |- _ /\ _ => split
             end. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M dst DIG8) knF0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 167%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    eapply (rf_segF vals1); eassumption.
  Qed.

  (* [comment removed for export] *)
  Ltac memcpy0_step HL P0 srcZ :=
    let dst := fresh "dst" in
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 546));
    lazymatch goal with HR : regs_ok _ _ ?Rc |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
      assert (MC : mcH Mc dst (Z_to_bv 64 srcZ) 0 [])
        by (constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity);
      assert (A1 : getr Rc 1 = (0x19794 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 srcZ) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy Mc dst (Z_to_bv 64 srcZ) 0 _ (seg_rom RSEGS) MC Rc (0x19794 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12 MC;
      after_memcpy HL Hms Hkeep;
      change (wbytes Mc dst []) with Mc
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segD : forall vals R M,
    length vals = 103%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srD0 R -> know_ok RSEGS (ENV BL vals) M knC ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x19794) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 103%nat.
    memcpy0_step HL P0 0x10298%Z.
    lazymatch goal with |- realizes _ (mkCfg (mkst ?R2 _ ?Mc _) _) _ =>
      pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) Mc knD ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2;
      clear HK; rename HK2 into HK;
      set (vals1 := vals ++ junk_vals R2) in *
    end.
    assert (HL1 : length vals1 = 135%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    eapply (rf_segE vals1); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segC : forall vals R M,
    length vals = 71%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srC0 R -> know_ok RSEGS (ENV BL vals) M knC0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x19794) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 71%nat.
    memcpy0_step HL P0 0x1034b%Z.
    lazymatch goal with |- realizes _ (mkCfg (mkst ?R2 _ ?Mc _) _) _ =>
      pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) Mc knC ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2;
      clear HK; rename HK2 into HK;
      set (vals1 := vals ++ junk_vals R2) in *
    end.
    assert (HL1 : length vals1 = 103%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    eapply (rf_segD vals1); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segB : forall vals R M,
    length vals = 39%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srRF0 R -> know_ok RSEGS (ENV BL vals) M knRF0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12d30) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 39%nat.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
    assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x1033d) 14 = Some PRE14).
    { rewrite (kimg_rdn RSEGS (ENV BL vals) _ knB ltac:(let i := kidx knB (is_kimg_cov 0x1033d 14) in exact i)
                 _ _ 0x1033d 14 HK eq_refl) by (cbn; lia). apply pre14_img. }
    assert (Hdst : store_ok RSEGS M dst 14 = true).
    { pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-560) 14) in exact i)
                    _ _ _ (-560) 14 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
    assert (MC : mcH M dst (Z_to_bv 64 0x1033d) 14 PRE14).
    { constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x19794 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x1033d) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 14) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst (Z_to_bv 64 0x1033d) 14 _ (seg_rom RSEGS) MC Rc (0x19794 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    after_memcpy HL Hms Hkeep.
    assert (HK2 : know_ok RSEGS (ENV BL vals) (wbytes M dst PRE14) knC0).
    { subst dst. rewrite <- (memcpy1_denot vals M P0).
      eapply (carry_after RSEGS (ENV BL vals) M logM1 knB [] knC0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat logM1].
      repeat match goal with
             | |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
             | |- (_ <= _)%nat => lia
             | |- True => exact I
             | |- _ /\ _ => split
             end. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M dst PRE14) knC0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 71%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    eapply (rf_segC vals1); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variables (tid : Z) (cnr : word) (R : bvmap 5 word) (M : word -> option byte).
  Hypothesis Rsp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
  Hypothesis Rgp : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis Rtp : getr R 4 = Z_to_bv 64 0x314d8.
  Hypothesis Mstack : stack_writable M sp0.
  Hypothesis Mimg : Forall (fun iv => img_clear M (fst iv) (snd iv)) rf_ivs.
  Hypothesis Mtid : cell M 0x31430 4 tid.
  Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
  Hypothesis Mself : cell M 0x31410 8 0x31410.
  Hypothesis Mcanary : cell M 0x51748 8 (bv_unsigned cnr).
  Hypothesis Mpagesz : cell M 0x51798 8 4096.

  Definition valsRF : list word := [sp0; sp0; sp0; sp0; sp0; Z_to_bv 64 tid] ++ junk_vals R ++ [cnr].
  Let E : env := ENV BL valsRF.

  Lemma valsRF_len : length valsRF = 39%nat.
  Proof. unfold valsRF. rewrite !length_app, junk_vals_length. reflexivity. Qed.

  Lemma evRF_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold E, ENV. cbn [ev]. unfold valsRF.
    change (6 + i)%nat with (length [sp0; sp0; sp0; sp0; sp0; Z_to_bv 64 tid] + i)%nat.
    unfold vals_ev. rewrite app_nth2_plus, app_nth1 by (rewrite junk_vals_length; exact Hi).
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma evRF38 : ev E 38 = cnr.
  Proof. reflexivity. Qed.

  Ltac reg_caseRF :=
    cbn [nth srRF0 all_regs];
    first [ lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot E (EVar n)) with (ev E n);
              first [ rewrite (evRF_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact Rgp | exact Rtp
          | rewrite Rsp, alu_add; change (ev E 0) with sp0; unfold v_add; apply bv_eq;
            rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia
          | idtac ].

  Lemma regs_okRF : regs_ok E srRF0 R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseRF.
  Qed.

  Lemma img_clear_of : forall lo hi, In (lo, hi) rf_ivs -> img_clear M lo hi.
  Proof. intros lo hi Hin. exact (proj1 (Forall_forall _ _) Mimg (lo, hi) Hin). Qed.

  Ltac kimg := split; [lia|]; split; [lia|]; apply img_clear_of; cbn; tauto.
  Ltac kcell H := split; [lia|]; split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|];
                 rewrite adenot_lit0; cbn [edenot];
                 first [exact H | rewrite H; reflexivity | idtac].

  Lemma know_okRF : know_ok RSEGS E M knRF0.
  Proof.
    pose proof SPlo. pose proof SPhi. pose proof SPal.
    unfold know_ok, knRF0.
    repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok].
    - (* [comment removed for export] *) split; [lia|]. change (edenot E (EVar 0)) with sp0. exact SPal.
    - change (edenot E (EVar 0)) with sp0. lia.
    - (* [comment removed for export] *) split; [apply flat_intro; cbn; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off]. change (edenot E (EVar 0)) with sp0.
      replace (bv_unsigned sp0 + -8388608 + d)%Z with (bv_unsigned sp0 - 8388608 + d)%Z by lia.
      apply Mstack; lia.
    - (* [comment removed for export] *) split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia.
      apply store_ok_data; rewrite u_small by lia; lia.
    - kimg. - kimg. - kimg. - kimg.
    - kcell Mself.
    - kcell Mtid.
    - kimg. - kimg. - kimg. - kimg. - kimg. - kimg.
    - pose proof Mcanary as MC. unfold cell in MC. rewrite Z_to_bv_bv_unsigned in MC.
      change (edenot E (EVar 38)) with cnr. kcell MC.
    - kimg. - kimg. - kimg. - kimg.
    - kcell Mpagesz.
    - kimg.
    - kimg. - kimg. - kimg. - kimg. - kimg. - kimg.
    - change (edenot E (EVar 5)) with (Z_to_bv 64 tid : word). rewrite u_small by lia. lia.
  Qed.

  Theorem ref_refused_tail :
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12d30) M (seg_rom RSEGS)) model)
               (t_die msg_refused (m_fs model)).
  Proof.
    pose proof SPlo. pose proof SPhi.
    unfold t_die.
    exact (rf_segB valsRF R M valsRF_len eq_refl regs_okRF know_okRF).
  Qed.
End Refused.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rf_pres_cell : forall M0 M sp0 a n v,
  pres M0 M sp0 -> (0x10000 <= a)%Z -> (a + Z.of_nat n <= 0x52000)%Z ->
  (a + Z.of_nat n <= 0x213c9 \/ 0x313c9 <= a)%Z ->
  (forall i, (a <= i < a + Z.of_nat n)%Z -> ~ rd_cell i) ->
  cell M0 a n v -> cell M a n v.
Proof.
  intros M0 M sp0 a n v P Ha Hn Hst Hrd C. unfold cell in *. rewrite <- C.
  apply rdn_agree. intros j Hj. rewrite (u_small a) by lia. apply P. left. rewrite u_small by lia.
  split; [lia|]. apply Hrd. lia.
Qed.

Lemma rf_pres_img_clear : forall M0 M sp0 lo hi,
  pres M0 M sp0 -> (0x10000 <= lo)%Z -> (hi <= 0x52000)%Z ->
  (hi <= 0x213c9 \/ 0x313c9 <= lo)%Z ->
  (forall i, (lo <= i < hi)%Z -> ~ rd_cell i) ->
  img_clear M0 lo hi -> img_clear M lo hi.
Proof.
  intros M0 M sp0 lo hi P Hlo Hhi Hst Hrd C i Hi. rewrite (P (Z_to_bv 64 i)); [apply C; exact Hi|].
  left. rewrite u_small by lia. split; [lia|]. apply Hrd. exact Hi.
Qed.

Theorem refused_leaf_ok {AMB : Amb} : forall (sp0 : word) (path : list byte) (stdin0 : InputStream) (fs0 : Fs)
    (gm tid sec cnr : word) (area brkv mas : Z) (M0 : word -> option byte),
  valid_sp sp0 ->
  world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned sec) (bv_unsigned cnr) M0 ->
  forall (R : bvmap 5 word) (M : word -> option byte) (off : Z) (V : VmMaps),
    refused_leaf sp0 M0 R M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12d30) M (seg_rom RSEGS)) (modelG path stdin0 fs0 tid off V))
             (t_die msg_refused fs0).
Proof.
  intros sp0 path stdin0 fs0 gm tid sec cnr area brkv mas M0 Hvsp W0 R M off V (Rsp & Rgp & Rtp & P & Hst).
  pose proof (w_tid _ _ _ _ _ _ _ _ W0) as Wtid. pose proof (w_tidr _ _ _ _ _ _ _ _ W0) as Wtidr.
  pose proof (w_self _ _ _ _ _ _ _ _ W0) as Wself. pose proof (w_canary _ _ _ _ _ _ _ _ W0) as Wcan.
  pose proof (w_pagesz _ _ _ _ _ _ _ _ W0) as Wpgs.
  pose proof (w_img _ _ _ _ _ _ _ _ W0) as Wimg.
  change fs0 with (m_fs (modelG path stdin0 fs0 tid off V)).
  apply (ref_refused_tail sp0 [] (modelG path stdin0 fs0 tid off V) Hvsp eq_refl eq_refl eq_refl
           (bv_unsigned tid) cnr R M Rsp Rgp Rtp Hst).
  - (* [comment removed for export] *)
    unfold rf_ivs. unfold img_clear_ivs in Wimg. apply Forall_cons_iff in Wimg as [_ Wimg].
    repeat (apply Forall_cons_iff in Wimg as [?C Wimg]).
    repeat (apply Forall_cons; [eapply rf_pres_img_clear; [exact P | cbn; lia | cbn; lia | cbn; lia
                                                           | unfold rd_cell; cbn; intros; lia | assumption] |]).
    apply Forall_nil.
  - eapply rf_pres_cell; [exact P | lia | cbn; lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact Wtid].
  - exact Wtidr.
  - eapply rf_pres_cell; [exact P | lia | cbn; lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact Wself].
  - eapply rf_pres_cell; [exact P | lia | cbn; lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact Wcan].
  - eapply rf_pres_cell; [exact P | lia | cbn; lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact Wpgs].
Qed.
End WithFP1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End UbRefused.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require RefNodes.

Module UbDirFront.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWritev OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExitBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMemcpyBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMemcpy OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbStartup OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMainEntry OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbPilotOOM.UbPilotOOM_defs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbPilotOOM.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

Section WithFP1. Context {FP : PropExec.FPState}.
Section DirFront.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variable a0s : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rndb : EntryDraw.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Hypothesis Hva : valid_argv [a0s; dot_path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; dot_path] envv tid rndb regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.

  (* [comment removed for export] *)
  Definition fdsD1 : list (word * FdEntry) := fd_insert (fds0) (Z_to_bv 64 3) FdDir.
  Definition modelD1 : Model := model1g sp0 tid brk mbase fs0 stdin0 FdDir.

  (* [comment removed for export] *)
  Definition dir_seg2_kont (T : TSet) : Prop :=
    forall vals R M,
      length vals = 38%nat -> vals_ev vals 0 = sp0 ->
      vals_ev vals 1 = p0 sp0 a0s dot_path envv -> vals_ev vals 2 = p1 sp0 a0s dot_path envv ->
      vals_ev vals 5 = tid ->
      regs_ok (ENV a0s dot_path vals) srB0 R -> know_ok RSEGS (ENV a0s dot_path vals) M knA ->
      (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1f004) M (seg_rom RSEGS)) modelD1) T.

  Lemma dot_nonul : ~ In (Z_to_bv 8 0) dot_path.
  Proof. cbn. intros [E|[]]. apply (f_equal bv_unsigned) in E. vm_compute in E. lia. Qed.

  Lemma dir_seg1 : forall KA T,
    open_err_branch sp0 a0s dot_path envv tid mem0 brk mbase fs0 stdin0 KA -> dir_seg2_kont T ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x12ae8) mem0 (seg_rom RSEGS))
                            (model0 sp0 a0s dot_path envv tid brk mbase fs0 stdin0))
               (t_alt2 KA T).
  Proof.
    intros KA T HKA HT.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (main_regs_ok sp0 a0s dot_path envv tid rndb regs0 mem0 Hvsp Htid ME) as HR.
    pose proof (main_know_ok sp0 a0s dot_path envv tid rndb regs0 mem0 Hva Hve Hvsp Htid ME) as HK.
    change (E0 sp0 a0s dot_path envv tid rndb regs0) with (ENV a0s dot_path (vals0 sp0 a0s dot_path envv tid rndb regs0)) in HR, HK.
    set (vals := vals0 sp0 a0s dot_path envv tid rndb regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals0; rewrite length_app, length_skipn, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0 sp0 a0s dot_path envv) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 sp0 a0s dot_path envv) by reflexivity.
    assert (P5t : vals_ev vals 5 = tid) by reflexivity.
    destruct (main_str sp0 a0s dot_path envv tid rndb regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
    cbn [nth] in Sr, Slo, Shi, Slen.
    clearbody vals.
    (* [comment removed for export] *)
    run_block_keep scr0 38%nat.
    assert (ABOVE : forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x).
    { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV a0s dot_path vals) mem0 _ 0%nat 0x52000);
        [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
    (* [comment removed for export] *)
    assert (Sr' : rdn RSEGS M (p1 sp0 a0s dot_path envv) (length dot_path + 1) = Some (dot_path ++ [Z_to_bv 8 0])).
    { rewrite <- Sr. apply rdn_agree. intros j Hj. apply ABOVE.
      pose proof (u64_range (p1 sp0 a0s dot_path envv)). unfold p1 in *. rewrite u_small by lia. lia. }
    (* [comment removed for export] *)
    eapply (rz_openat_dot RSEGS _ _ _ (model0 sp0 a0s dot_path envv tid brk mbase fs0 stdin0) ECALLW); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). apply bv_eq. reflexivity.
    - regv HR (12 : reg). vm_compute. reflexivity.
    - (* [comment removed for export] *) rewrite m0_fds. rewrite alloc_fd_fds0. apply fd_lookup_fds0_3.
    - (* [comment removed for export] *) split; [cbn; lia|]. split; [apply dot_nonul|].
      regv HR (11 : reg). cbn [edenot ev ENV]. rewrite P2. exact Sr'.
    - (* [comment removed for export] *)
      intros e He. rewrite v_addi_pc4 by lia. change (0x1f000 + 4)%Z with 0x1f004%Z.
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s dot_path)))
        with (ENV a0s dot_path (vals ++ [errno_ret e])) in HR2, HK2.
      eapply (HKA e (vals ++ [errno_ret e])); try eassumption.
      + rewrite length_app, HL. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
      + rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P1.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P5t.
      + apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
        rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x1f000 + 4)%Z with 0x1f004%Z.
      rewrite m0_fds. rewrite alloc_fd_fds0.
      change (with_fds (fd_insert fds0 (Z_to_bv 64 3) FdDir) (model0 sp0 a0s dot_path envv tid brk mbase fs0 stdin0)) with modelD1.
      pose proof (regs_set_a0 (ENV a0s dot_path vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2.
      eapply (HT vals); try eassumption.
  Qed.
End DirFront.
End WithFP1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End UbDirFront.

Module UbLeafDir.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbStartup OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMainEntry OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbWorld OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbPilotOOM.UbPilotOOM_defs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbPilotOOM UbDirFront OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbDirMid.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section WithFP1. Context {FP : PropExec.FPState}.
Section LeafDir.
  Context {AMB : Amb}.
  (* [comment removed for export] *)
  Hypothesis cannot_open_branch : forall (sp0 : word) (a0s : list byte) (envv : list (list byte)) (tid : word)
      (rndb : EntryDraw) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream),
    valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 -> entry_stack_fits sp0 [a0s; dot_path] envv ->
    main_entry sp0 [a0s; dot_path] envv tid rndb regs0 mem0 ->
    open_err_branch sp0 a0s dot_path envv tid mem0 brk mbase fs0 stdin0 (t_die (msg_cannot_open dot_path) fs0).
  (* [comment removed for export] *)
  Hypothesis dir_tail_h : forall (sp0 : word) (a0s : list byte) (envv : list (list byte)) (tid : word)
      (rndb : EntryDraw) (regs0 : bvmap 5 word) (mem0 : word -> option byte),
    valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
    main_entry sp0 [a0s; dot_path] envv tid rndb regs0 mem0 ->
    forall (cnr : Z) (R : bvmap 5 word) (M : word -> option byte) (model : Model),
      m_halted model = None -> m_vm_lazy model = [] ->
      fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
      dir_tail_pre sp0 (p1 sp0 a0s dot_path envv) (bv_unsigned tid) cnr mem0 R M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12d14) M (seg_rom RSEGS)) model)
                 (t_die (msg_read_error dot_path) (m_fs model)).

  Lemma ref_dir_path : forall (sp0 : word) (a0s : list byte) (envv : list (list byte)) (tid : word) (rndb : EntryDraw)
      (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream),
    valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
    entry_stack_fits sp0 [a0s; dot_path] envv ->
    main_entry sp0 [a0s; dot_path] envv tid rndb regs0 mem0 -> valid_brk RSEGS brk ->
    realizes RSEGS (mkCfg (mkst regs0 (0x12ae8 : word) mem0 (seg_rom RSEGS))
                            (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputC [a0s; dot_path] envv fs0 stdin0))))
               (t_alt2 (t_die (msg_cannot_open dot_path) fs0) (t_opened_dir dot_path fs0)).
  Proof using cannot_open_branch dir_tail_h.
    intros sp0 a0s envv tid rndb regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hfit ME Hbrk.
    set (K := t_die (msg_read_error dot_path) fs0).
    assert (AM : after_malloc_dir sp0 a0s envv tid mem0 fs0 stdin0 K).
    { apply (dir_read sp0 a0s envv tid mem0 fs0 stdin0 Hvsp). intros R' M' VM' cnr P. subst K.
      change fs0 with (m_fs (modelDir tid fs0 stdin0 VM')).
      apply (dir_tail_h sp0 a0s envv tid rndb regs0 mem0 Hva Hve Hvsp Htid ME (bv_unsigned cnr) R' M'
               (modelDir tid fs0 stdin0 VM') eq_refl eq_refl eq_refl P). }
    replace (0x12ae8 : word) with (Z_to_bv 64 0x12ae8) by (apply bv_eq; reflexivity).
    change (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputC [a0s; dot_path] envv fs0 stdin0)))
      with (model0 sp0 a0s dot_path envv tid brk mbase fs0 stdin0).
    apply (dir_seg1 sp0 a0s envv tid rndb regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME).
    - apply (cannot_open_branch sp0 a0s envv tid rndb regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Hfit ME).
    - unfold dir_seg2_kont. intros vals R M HL P0 P1 P2 P5 HR HK HA.
      change (modelD1 sp0 tid brk mbase fs0 stdin0) with (model1g sp0 tid brk mbase fs0 stdin0 FdDir).
      apply (oom_seg2 sp0 a0s dot_path envv tid mem0 brk mbase fs0 stdin0 Hvsp Hbrk ltac:(cbn; lia) FdDir K
               vals R M
               (dir_brk sp0 a0s envv tid rndb mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk K AM)
               HL P0 P1 P2 P5 HR HK HA).
  Qed.
End LeafDir.
End WithFP1.
End UbLeafDir.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require UbMain UbUsage.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require ArgvEnv MuslStrlen RefLayout UbMemchr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require LibKnowFrame.

Module UbOpenFail_tail2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeLaws OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SpecConsts OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveH4 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWritev OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExitBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbStdioDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbLibStdioCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMemcpyBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMemcpy OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMemchr OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbUsage.UbStrnlen OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbStartup OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMainEntry OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTail.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbUsage.UbOpenFail_defs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbUsage.UbOpenFail_tail.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac close_exit HR HK P0 Hh Hlazy sp0 :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
  lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
    apply (rz_conseq segs _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
    [ | cbn [W map];
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity);
        apply t_eq_sym; apply t_emit_nil_exit ];
    apply ref_exit_Z;
    let Ktid := fresh "Ktid" in
    pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid;
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x314d8), (bv_unsigned (ev E 5)),
           (Z_to_bv 64 0), (Z_to_bv 64 0);
    split; [|split; [exact Hh|split; [exact Hlazy|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); reflexivity
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        let Hst := fresh "Hst" in
        pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                      _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENV] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia; exact Hst
      | lit_u; cbn [ev ENV] in Ktid |- *; lia
      | lit_u; cbn [ev ENV] in Ktid |- *; lia
      | cbn [ev ENV] in Ktid |- *; lia
      | lit_u; change (201944 - 168)%Z with 0x31430%Z;
        let Htc := fresh "Htc" in
        krd HK 0x31430%Z 4%nat Htc; rewrite Htc; cbn [ev ENV] in Ktid |- *;
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
      | repeat split; krd_solve HK
      | repeat split; krd_solve HK
      | krd_solve HK | krd_solve HK | left; unfold ax_empty; krd_solve HK ]
    | left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
  end end end.

Section WithFP1. Context {FP : PropExec.FPState}.
Section Tail2.
  Variable sp0 : word.
  Variable BL : list (list byte).
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma of_segI3 : forall vals R M,
    length vals = 263%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srI30 R -> know_ok RSEGS (ENV BL vals) M knI30 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x19e44) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 263%nat.
    close_exit HR HK P0 Hh Hlazy sp0.
  Qed.

  Lemma of_segH3 : forall vals R M,
    length vals = 231%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srH30 R -> know_ok RSEGS (ENV BL vals) M knH30 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1a014) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk scr0 231%nat.
    apply (rz_conseq RSEGS _ (t_emit (map (WriteEv (Z_to_bv 64 2)) ([] ++ [])) (t_exit (exit_code 2) (m_fs model)))).
    2:{ cbn [map app]. apply t_eq_sym. apply t_emit_nil_exit. }
    pose proof itinerary_63_64 as (_ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srH3 knH3 Rc Mc model scH3 [] []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH3 knH3) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scH3 length Z.of_nat] end.
    - lia.
    - lia.
    - cbn [edenot]. apply u_small. lia.
    - pose proof rw_bytes_max_ge17. lia.
    - lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - (* [comment removed for export] *)
      first [ lia | (ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia) | (cbn [edenot]; unorm; lia)
            | (ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113); unorm; lia)
            | (ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112); unorm; lia)
            | (cbn [edenot]; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia) ].
    - reflexivity.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 HR HK.
      eapply (of_segI3 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  Lemma of_segG3 : forall (path : list byte), Z.of_nat (length path) = 63%Z ->
    atG0 sp0 BL model path 63 (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path HP vals R M HL P0 P113 HR HK SBp.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scrG3 199%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113).
      replace (-1 * 63 + 63)%Z with 0%Z by lia.
      rewrite ltu_ZZ by lia. reflexivity. }
    assert (WOK : win_ok (ENV BL vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV BL vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    clear EQM SBp. rename M0 into M'.
    krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-552)%Z 8%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-544)%Z 1%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0, Hw1, Hw2. cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2.
    rewrite P0 in Hw0, Hw1, Hw2.
    assert (H17 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) 17 = Some PRE17).
    { rewrite <- PRE17_words. change 17%nat with (8 + (8 + 1))%nat.
      apply rdn_app_Z; [exact Hw0 | | lia | lia].
      apply rdn_app_Z; [ | | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -552)%Z by lia. exact Hw1.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -544)%Z by lia. exact Hw2. }
    assert (B80 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (17 + length path) = Some (PRE17 ++ path)).
    { apply rdn_app_Z; [exact H17 | | lia | lia].
      replace (bv_unsigned sp0 + -560 + Z.of_nat 17)%Z with (bv_unsigned sp0 - 543)%Z by lia. exact SBp'. }
    assert (Hnl : rdn RSEGS M' (Z_to_bv 64 0x10371) 1 = Some [Z_to_bv 8 10]).
    { rewrite (kimg_rdn RSEGS (ENV BL vals) _ knG3 ltac:(let i := kidx knG3 (is_kimg_cov 0x10371 1) in exact i)
                 _ _ 0x10371 1 HK eq_refl) by (cbn; lia). apply nl_img. }
    (* [comment removed for export] *)
    unfold msg_cannot_open. change (s2b _) with PRE17. rewrite app_assoc. unfold W.
    pose proof itinerary_63_64 as (_ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srG3 knG3 Rc Mc model scG3 (PRE17 ++ path) [Z_to_bv 8 10]
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srG3 knG3) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scG3];
      rewrite ?length_app, ?PRE17_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - cbn [edenot length]. apply u_small. lia.
    - cbn [length Z.of_nat]. lia.   (* [comment removed for export] *)
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - (* [comment removed for export] *)
      first [ lia | (ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia) | (cbn [edenot]; unorm; lia)
            | (ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113); unorm; lia)
            | (ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112); unorm; lia)
            | (cbn [edenot]; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia) ].
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm.
      replace (17 + length path)%nat with (17 + length path)%nat by lia. exact B80.
    - cbn [edenot]. exact Hnl.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (of_segH3 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma NL_word : word_to_le_bytes 1 (Z_to_bv 64 10) = [Z_to_bv 8 10].
  Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.

  Lemma of_segI4 : forall vals R M,
    length vals = 263%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srI40 R -> know_ok RSEGS (ENV BL vals) M knI40 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x19e44) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 263%nat.
    close_exit HR HK P0 Hh Hlazy sp0.
  Qed.

  Lemma of_segH4 : forall vals R M,
    length vals = 231%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srH40 R -> know_ok RSEGS (ENV BL vals) M knH40 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x19794) M (seg_rom RSEGS)) model)
               (t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk scr0 231%nat.
    krdv HK 0%nat (-560)%Z 1%nat Hb. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    rewrite NL_word in Hb.
    unfold adenot, v_addi in Hb. cbn [a_base a_off edenot ev ENV] in Hb. rewrite P0 in Hb.
    replace (W 2 [Z_to_bv 8 10]) with (map (WriteEv (Z_to_bv 64 2)) ([Z_to_bv 8 10] ++ [])) by reflexivity.
    pose proof itinerary_63_64 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srH4 knH4 Rc Mc model scH4 [Z_to_bv 8 10] []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH4 knH4) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scH4 length Z.of_nat] end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. apply u_small. lia.
    - pose proof rw_bytes_max_ge17. lia.
    - lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - (* [comment removed for export] *)
      first [ lia | (ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia) | (cbn [edenot]; unorm; lia)
            | (ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113); unorm; lia)
            | (ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112); unorm; lia)
            | (cbn [edenot]; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia) ].
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hb.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 HR HK.
      eapply (of_segI4 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  Lemma of_segFG4 : forall (path : list byte) (pp : word) (P : Z) vals R M,
    Z.of_nat (length path) = P -> (64 <= P <= 131071)%Z ->
    length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    (bv_unsigned pp + P <= 2 ^ 47)%Z ->   (* [comment removed for export] *)
    regs_ok (ENV BL vals) srF0 R -> know_ok RSEGS (ENV BL vals) M knE ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x19794) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path pp P vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 Hpp47 HR HK Hstr.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (Psmall : (bv_unsigned (edenot (ENV BL vals) (EVar 113)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite P113, u_small by lia. lia. }
    (* [comment removed for export] *)
    run_blk_keep scrF4 167%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P113).
      rewrite ltu_ZZ by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken].
      rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    assert (WOKS : win_ok (ENV BL vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV BL vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    clear EQM Hstr. rename M0 into M'.
    assert (Hsrc : rdn RSEGS M' pp (length path) = Some path).
    { replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
    krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-552)%Z 8%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-544)%Z 1%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0, Hw1, Hw2. cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2.
    rewrite P0 in Hw0, Hw1, Hw2.
    assert (H17 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) 17 = Some PRE17).
    { rewrite <- PRE17_words. change 17%nat with (8 + (8 + 1))%nat.
      apply rdn_app_Z; [exact Hw0 | | lia | lia].
      apply rdn_app_Z; [ | | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -552)%Z by lia. exact Hw1.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -544)%Z by lia. exact Hw2. }
    (* [comment removed for export] *)
    apply (rz_conseq RSEGS _ (t_emit (W 2 (PRE17 ++ path)) (t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model))))).
    2:{ unfold msg_cannot_open. change (s2b _) with PRE17. rewrite app_assoc. unfold W. rewrite (map_app _ (PRE17 ++ path)).
        apply t_eq_sym. apply t_emit_app. }
    unfold W at 1.
    pose proof itinerary_63_64 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srF4 knF4 Rc Mc model scF4 PRE17 path
             (t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model))) HR HK
             (eq_trans (f_equal (fun n => stdio_call n srF4 knF4) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scF4];
      rewrite ?PRE17_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot ev ENV PX]. rewrite P113. rewrite u_small by lia. lia.
    - cbn [length Z.of_nat]. lia.   (* [comment removed for export] *)
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - right. cbn [edenot ev ENV PX]. rewrite P2. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot ev ENV PX]. rewrite P2, P113. rewrite u_small by lia. lia.
    - (* [comment removed for export] *)
      first [ lia | (ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia) | (cbn [edenot]; unorm; lia)
            | (ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113); unorm; lia)
            | (ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P112); unorm; lia)
            | (cbn [edenot]; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia) ].
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact H17.
    - cbn [edenot ev ENV PX]. rewrite P2. exact Hsrc.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_emit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R1 M1 HR HK.
      clear Hstr' Hsrc Hw0 Hw1 Hw2 H17 Psmall.
      lazymatch type of HK with know_ok _ _ _ ?k => change k with knG40 in HK end.
      lazymatch type of HR with regs_ok _ ?sr _ => change sr with srG40 in HR end.
      set (vals0 := vals) in P2, P113.
      set (vals1 := vals ++ junk_vals R1) in *.
      assert (HL1 : length vals1 = 199%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals1 vals0. clear HL P0 WOKS. clear vals. rename HL1 into HL. rename Q0 into P0.
      change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
      run_blk scr0 199%nat.
      lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ => rename Mc into MG end.
      (* [comment removed for export] *)
      set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
      assert (Hnl : rdn RSEGS MG (Z_to_bv 64 0x10371) 1 = Some [Z_to_bv 8 10]).
      { rewrite (kimg_rdn RSEGS (ENV BL vals1) _ knG4 ltac:(let i := kidx knG4 (is_kimg_cov 0x10371 1) in exact i)
                   _ _ 0x10371 1 HK eq_refl) by (cbn; lia). apply nl_img. }
      assert (Hdst : store_ok RSEGS MG dst 1 = true).
      { pose proof (kwr_store_ok RSEGS (ENV BL vals1) _ knG4 ltac:(let i := kidx knG4 (is_kwr_cov (EVar 0) (-560) 1) in exact i)
                      _ _ _ (-560) 1 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
        subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
      assert (MC : mcH MG dst (Z_to_bv 64 0x10371) 1 [Z_to_bv 8 10]).
      { constructor; cbn [length Z.to_nat Z.of_nat Pos.to_nat]; subst dst; rewrite ?u_small by lia; try lia.
        - exact Hnl.
        - exact Hdst. }
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        assert (A1 : getr Rc 1 = (0x19794 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
        assert (A10 : getr Rc 10 = dst)
          by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
        assert (A11 : getr Rc 11 = Z_to_bv 64 0x10371) by (regv HR (11 : reg); reflexivity);
        assert (A12 : getr Rc 12 = Z_to_bv 64 1) by (regv HR (12 : reg); reflexivity);
        destruct (ref_memcpy MG dst (Z_to_bv 64 0x10371) 1 _ (seg_rom RSEGS) MC Rc (0x19794 : word)
                    ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
        clear A1 A10 A11 A12
      end.
      replace (Z_to_bv 64 124636) with (0x1e6dc : word) by (apply bv_eq; reflexivity).
      eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
      replace (0x19794 : word) with (Z_to_bv 64 0x19794) by (apply bv_eq; reflexivity).
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R2 callee_kept
                      ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
      rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
      (* [comment removed for export] *)
      pose proof (know_after_store RSEGS (ENV BL vals1) MG knG4 (SA (EVar 0) (-560)) 1 (ELit 10) [Z_to_bv 8 10]
                    knH40 [] [] ltac:(vm_compute; reflexivity) eq_refl HK ltac:(lia)
                    ltac:(apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia)
                    ltac:(cbn [edenot]; symmetry; apply NL_word)) as HK2.
      clear HK.
      assert (Edst : adenot (ENV BL vals1) (SA (EVar 0) (-560)) = dst).
      { unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0. subst dst. f_equal; lia. }
      rewrite Edst in HK2.
      pose proof (env_app_know RSEGS vals1 (junk_vals R2) (blobs_ev BL) (wbytes MG dst [Z_to_bv 8 10]) knH40
                    ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
      clear HK2.
      set (vals2 := vals1 ++ junk_vals R2) in *.
      assert (HL2 : length vals2 = 231%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals2.
      change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV BL vals2) in HR, HK.
      eapply (of_segH4 vals2); [exact HL2 | exact Q0 | exact HR | exact HK].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem of_tail : forall (path : list byte) (pp : word) (t8 : list byte) vals R M,
    ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) <= 131071)%Z ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    (2 ^ 64 - 4095 <= bv_unsigned (vals_ev vals 38))%Z ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z ->
    (bv_unsigned pp + Z.of_nat (length path) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    (bv_unsigned pp + Z.of_nat (length path) <= 2 ^ 47)%Z ->   (* [comment removed for export] *)
    regs_ok (ENV BL vals) (sr_upd srA (ridx 10) (EVar 38)) R -> know_ok RSEGS (ENV BL vals) M knA ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length path))) 8 = Some t8 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1f004) M (seg_rom RSEGS)) model)
               (t_die (msg_cannot_open path) (m_fs model)).
  Proof.
    intros path pp t8 vals R M Hnonul HPl HL P0 P2 P38 Hpp1 Hpp2 Hpp47 HR HK Hstr Ht8.
    unfold t_die.
    eapply (of_segBC sp0 BL model Hvsp Hh Hlazy path pp (Z.of_nat (length path)) _ t8 vals);
      try eassumption; try lia.
    intros vals' R' M' HL' Q0 Q2 Q113 HR' HK' Hstr'.
    destruct (Z.le_gt_cases (Z.of_nat (length path)) 62) as [Hle | Hgt].
    - eapply (of_segF sp0 BL model Hvsp Hh Hlazy Hfd2 path pp _ vals'); try eassumption; lia.
    - destruct (Z.le_gt_cases (Z.of_nat (length path)) 63) as [Hle2 | Hgt2].
      + assert (E63 : Z.of_nat (length path) = 63%Z) by lia. rewrite E63 in Q113.
        eapply (of_segF_gen sp0 BL model Hvsp Hh Hlazy path pp 63 _ vals'); try eassumption; try lia.
        apply of_segG3. exact E63.
      + eapply (of_segFG4 path pp _ vals'); try eassumption; lia.
  Qed.

End Tail2.
End WithFP1.

End UbOpenFail_tail2.

Module UbOpenFail.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ArgvEnv OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MuslStrlen OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefLayout OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveH4 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWritev OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExitBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMemcpyBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMemcpy OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMemchr OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbUsage.UbStrnlen OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbStartup OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMainEntry.UbStartupFacts OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMainEntry OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTail.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbUsage.UbOpenFail_defs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbUsage.UbOpenFail_tail UbOpenFail_tail2.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.
Lemma errno_ret_range : forall e, (1 <= e <= 4095)%Z ->
  (2 ^ 64 - 4095 <= bv_unsigned (errno_ret e))%Z.
Proof. intros e He. unfold errno_ret. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  replace ((- e) mod 2 ^ 64)%Z with (2 ^ 64 - e)%Z; [lia|].
  apply Z.mod_unique with (q := (-1)%Z); lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma In_firstn : forall {A} (l : list A) n x, In x (firstn n l) -> In x l.
Proof.
  intros A l n x H. rewrite <- (firstn_skipn n l). apply in_app_iff. left. exact H.
Qed.

Lemma openat_errnos_range : forall e, In e openat_errnos -> (1 <= e <= 4095)%Z.
Proof.
  intros e He. unfold openat_errnos in He. cbn in He.
  unfold ENOMEM, EACCES, EMFILE, ENFILE in He. lia.
Qed.

(* [comment removed for export] *)
Lemma path_task : forall (sp0 : word) a0s path envv,
  valid_argv [a0s; path] -> valid_envp envv -> valid_sp sp0 -> entry_stack_fits sp0 [a0s; path] envv ->
  (bv_unsigned (cat_argv_ptr sp0 [a0s; path] envv 1) + Z.of_nat (length path) + 1 <= 2 ^ 47)%Z.
Proof.
  intros sp0 a0s path envv Hva Hve [Hlo [Hhi Hal]] Hfits.
  rewrite (u_cat_argv_ptr RPH sp0 [a0s; path] envv (Z_to_bv 64 0) (Z_to_bv 64 0) (mkDraw (Z_to_bv 128 0) (fun _ => Z_to_bv 8 0)) Hva Hve Hlo Hhi 1%nat ltac:(cbn; lia)).
  unfold entry_stack_fits, entry_stack_span in Hfits. unfold cat_struct_size.
  rewrite !total_arg_bytes_Z in Hfits.
  cbn [firstn total_arg_bytes_nat fold_right length] in *. unfold auxv_size in *.
  unfold sp_window_hi in Hfits. lia.
Qed.

Section OpenFail.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rndb : EntryDraw.   (* [comment removed for export] *)
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  (* [comment removed for export] *)
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hfit : entry_stack_fits sp0 [a0s; path] envv.   (* [comment removed for export] *)
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid rndb regs0 mem0.

  (* [comment removed for export] *)
  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path)).
  Definition model0 : Model :=
    with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputC [a0s; path] envv fs0 stdin0)).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  Lemma model0_halted : m_halted model0 = None.
  Proof. reflexivity. Qed.
  Lemma model0_lazy : m_vm_lazy model0 = [].
  Proof. reflexivity. Qed.
  Lemma model0_fd2 : fd_lookup (m_fds model0) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. reflexivity. Qed.
  Lemma model0_fs : m_fs model0 = fs0.
  Proof. reflexivity. Qed.

  Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
  Proof.
    destruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
  Qed.
  Lemma path_len : (Z.of_nat (length path) <= 131071)%Z.
  Proof.
    destruct Hva as (_ & _ & Hl & _). inversion Hl as [|x l Hx Hl']; subst. inversion Hl'; subst. assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma path_facts :
    rdn RSEGS mem0 (p1 sp0 a0s path envv) (length path + 1) = Some (path ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (p1 sp0 a0s path envv))%Z
    /\ (bv_unsigned (p1 sp0 a0s path envv) <= bv_unsigned sp0 + 2107576)%Z
    /\ exists t8, rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned (p1 sp0 a0s path envv) + Z.of_nat (length path))) 8 = Some t8.
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct (main_str sp0 a0s path envv tid rndb regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
    cbn [nth] in Sr, Slo, Shi, Slen. unfold p1.
    split; [exact Sr|]. split; [exact Slo|]. split; [exact Shi|].
    pose proof (lay_bsb_nw RPH sp0 [a0s; path] envv a_uid a_hwcap rndb Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
    destruct (read_word_stack RPH RSEGS sp0 [a0s; path] envv 1 (length path) a_uid a_hwcap rndb ltac:(cbn; lia) ltac:(cbn; lia) Hnw)
      as (t8 & Hl8 & Hr8).
    exists t8. rewrite w_add_nat in Hr8.
    pose proof (u64_range (cat_argv_ptr sp0 [a0s; path] envv 1)).
    rewrite (main_entry_rdn_above sp0 [a0s; path] envv tid rndb regs0 mem0 ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS RPH sp0 [a0s; path] envv a_uid a_hwcap rndb) as Hw. unfold wmem in Hw.
    rewrite Hw by (rewrite u_small by lia; lia). exact Hr8.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Theorem ref_open_fail_errno : forall e vals R M,
    (1 <= e <= 4095)%Z ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 38 = errno_ret e ->
    vals_ev vals 2 = p1 sp0 a0s path envv ->
    regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 38)) R -> know_ok RSEGS (ENV vals) M knA ->
    (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1f004) M (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros e vals R M He HL P0 P38 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof path_len as HPl.
    destruct path_facts as (Sr & Slo & Shi & t8 & Ht8).
    pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr.
    pose proof (path_task sp0 a0s path envv Hva Hve Hvsp Hfit) as Hp47.
    change (cat_argv_ptr sp0 [a0s; path] envv 1) with (p1 sp0 a0s path envv) in Hp47.
    rewrite <- model0_fs.
    eapply (of_tail sp0 (blobs0 a0s path) model0 Hvsp model0_halted model0_lazy model0_fd2 path (p1 sp0 a0s path envv) t8 vals);
      try eassumption.
    - apply path_nonul.
    - rewrite P38. apply errno_ret_range. exact He.
    - lia.
    - lia.   (* [comment removed for export] *)
    - rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove. unorm. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma of_blockA : forall T,
    (forall vals R M,
       length vals = 38%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
       regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
       (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
       realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1f000) M (seg_rom RSEGS)) model0) T) ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x12ae8) mem0 (seg_rom RSEGS)) model0) T.
  Proof.
    intros T HA.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (main_regs_ok sp0 a0s path envv tid rndb regs0 mem0 Hvsp Htid ME) as HR.
    pose proof (main_know_ok sp0 a0s path envv tid rndb regs0 mem0 Hva Hve Hvsp Htid ME) as HK.
    change (E0 sp0 a0s path envv tid rndb regs0) with (ENV (vals0 sp0 a0s path envv tid rndb regs0)) in HR, HK.
    set (vals := vals0 sp0 a0s path envv tid rndb regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals0; rewrite length_app, length_skipn, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 sp0 a0s path envv) by reflexivity.
    clearbody vals.
    pose proof model0_halted as Hh.
    run_blk_keep scr0 38%nat.
    apply (HA vals); try assumption.
    intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x52000);
      [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma openat_regs : forall vals R,
    vals_ev vals 2 = p1 sp0 a0s path envv -> regs_ok (ENV vals) srA R ->
    getr R 17 = Z_to_bv 64 56 /\ getr R 10 = AT_FDCWD /\ getr R 11 = p1 sp0 a0s path envv
    /\ Z.ldiff (bv_unsigned (getr R 12)) open_ignored_flags = 0%Z.
  Proof.
    intros vals R P2 HR. repeat split.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). apply bv_eq. reflexivity.
    - regv HR (11 : reg). cbn [edenot ev ENV]. exact P2.
    - regv HR (12 : reg). vm_compute. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma after_openat_fail : forall e vals R M,
    (1 <= e <= 4095)%Z ->
    length vals = 38%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
    regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
    (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
    realizes RSEGS (mkCfg (mkst (regupd R 10 (errno_ret e)) (v_addi (Z_to_bv 64 0x1f000) 4) M (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros e vals R M He HL P0 P2 HR HK Habove.
    rewrite v_addi_pc4 by lia. change (0x1f000 + 4)%Z with 0x1f004%Z.
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
      pose proof (env_app_regs vals [errno_ret e] (blobs_ev (blobs0 a0s path)) sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
    pose proof (env_app_know RSEGS vals [errno_ret e] (blobs_ev (blobs0 a0s path)) M knA ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2.
    change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path))) with (ENV (vals ++ [errno_ret e])) in HR2, HK2.
    eapply (ref_open_fail_errno e (vals ++ [errno_ret e])); try eassumption.
    - rewrite length_app, HL. reflexivity.
    - rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
    - rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
    - rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
    - apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
      rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem ref_open_fail_toolong :
    (4096 <= length path)%nat ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x12ae8) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros Hlong. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & _).
    pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr. pose proof path_len as HPl.
    destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x1f000) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_toolong RSEGS R _ M model0 ECALLW HF is_ecall_ECALLW
              model0_halted model0_lazy A17 A10 A12 (firstn 4096 path)).
    - rewrite A11. rewrite <- (firstn_app_l 4096 path [Z_to_bv 8 0]) at 1 || idtac.
      replace (firstn 4096 path) with (firstn 4096 (path ++ [Z_to_bv 8 0]))
        by (rewrite firstn_app; replace (4096 - length path)%nat with 0%nat by lia; cbn [firstn]; apply app_nil_r).
      apply (rdn_firstn RSEGS M (length path + 1)); [| lia].
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - intros Hin. apply path_nonul. eapply In_firstn. exact Hin.
    - apply (after_openat_fail ENAMETOOLONG vals); try assumption. unfold ENAMETOOLONG. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem ref_open_fail_empty :
    path = [] ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x12ae8) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros Hnil. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & _).
    pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr.
    destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x1f000) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_empty RSEGS R _ M model0 ECALLW HF is_ecall_ECALLW
              model0_halted model0_lazy A17 A10 A12).
    - split; [cbn; lia|]. split; [intros [] |]. rewrite A11.
      replace (length path + 1)%nat with 1%nat in Sr by (rewrite Hnil; reflexivity).
      replace (path ++ [Z_to_bv 8 0]) with [Z_to_bv 8 0] in Sr by (rewrite Hnil; reflexivity).
      cbn [length Nat.add app].
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem ref_open_fail_absent :
    (length path <= 4095)%nat -> path <> [] -> path <> dot_path -> fs_lookup fs0 path = None ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x12ae8) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros Hlen Hne Hnd Hfs. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & _).
    pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr. pose proof path_len as HPl.
    destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x1f000) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_absent RSEGS R _ M model0 ECALLW HF is_ecall_ECALLW
              model0_halted model0_lazy A17 A10 A12 path).
    - split; [exact Hlen|]. split; [apply path_nonul|]. rewrite A11.
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - exact Hne.
    - exact Hnd.
    - (* [comment removed for export] *)
      destruct Hva as (_ & _ & _ & _ & VA5). cbn [tl] in VA5. apply Forall_cons_iff in VA5 as [[_ Hpdd0] _].
      intros E. rewrite E in Hpdd0. rewrite path_eqb_refl in Hpdd0. discriminate.
    - (* [comment removed for export] *)
      destruct Hva as (_ & _ & _ & _ & VA5). cbn [tl] in VA5. apply Forall_cons_iff in VA5 as [[Hpsl _] _]. exact Hpsl.
    - exact Hfs.
    - apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
  Qed.

  (* [comment removed for export] *)
  Corollary ref_open_fail_toolong_w :
    (4096 <= length path)%nat ->
    realizes RSEGS (mkCfg (mkst regs0 (0x12ae8 : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros H. replace (0x12ae8 : word) with (Z_to_bv 64 0x12ae8) by (apply bv_eq; reflexivity).
    apply ref_open_fail_toolong. exact H.
  Qed.

  Corollary ref_open_fail_empty_w :
    path = [] ->
    realizes RSEGS (mkCfg (mkst regs0 (0x12ae8 : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros H. replace (0x12ae8 : word) with (Z_to_bv 64 0x12ae8) by (apply bv_eq; reflexivity).
    apply ref_open_fail_empty. exact H.
  Qed.

  Corollary ref_open_fail_absent_w :
    (length path <= 4095)%nat -> path <> [] -> path <> dot_path -> fs_lookup fs0 path = None ->
    realizes RSEGS (mkCfg (mkst regs0 (0x12ae8 : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
  Proof.
    intros H1 H2 H3 H4. replace (0x12ae8 : word) with (Z_to_bv 64 0x12ae8) by (apply bv_eq; reflexivity).
    apply ref_open_fail_absent; assumption.
  Qed.

End OpenFail.

(* [comment removed for export] *)
Corollary ref_toolong_h : forall (AMB : Amb) (sp : word) (a0s path : list byte) (envp : list (list byte)) (tid : word) (rndb : EntryDraw)
    (regs : bvmap 5 word) (mem : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream),
  valid_argv [a0s; path] -> valid_envp envp -> valid_sp sp -> (0 < bv_unsigned tid < 2 ^ 22)%Z -> entry_stack_fits sp [a0s; path] envp ->
  main_entry sp [a0s; path] envp tid rndb regs mem -> (4096 <= length path)%nat ->
  realizes RSEGS (mkCfg (mkst regs (0x12ae8 : word) mem (seg_rom RSEGS))
                        (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp target_alloc_limit (mkProcInputC [a0s; path] envp fs0 stdin0))))
           (t_die (msg_cannot_open path) fs0).
Proof.
  intros AMB sp a0s path envp tid rndb regs mem brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hfit ME H.
  exact (ref_open_fail_toolong_w sp a0s path envp tid rndb regs mem brk mbase fs0 stdin0 target_alloc_limit Hva Hve Hvsp Htid Hfit ME H).
Qed.

Corollary ref_empty_h : forall (AMB : Amb) (sp : word) (a0s path : list byte) (envp : list (list byte)) (tid : word) (rndb : EntryDraw)
    (regs : bvmap 5 word) (mem : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream),
  valid_argv [a0s; path] -> valid_envp envp -> valid_sp sp -> (0 < bv_unsigned tid < 2 ^ 22)%Z -> entry_stack_fits sp [a0s; path] envp ->
  main_entry sp [a0s; path] envp tid rndb regs mem -> path = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x12ae8 : word) mem (seg_rom RSEGS))
                        (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp target_alloc_limit (mkProcInputC [a0s; path] envp fs0 stdin0))))
           (t_die (msg_cannot_open path) fs0).
Proof.
  intros AMB sp a0s path envp tid rndb regs mem brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hfit ME H.
  exact (ref_open_fail_empty_w sp a0s path envp tid rndb regs mem brk mbase fs0 stdin0 target_alloc_limit Hva Hve Hvsp Htid Hfit ME H).
Qed.

Corollary ref_absent_h : forall (AMB : Amb) (sp : word) (a0s path : list byte) (envp : list (list byte)) (tid : word) (rndb : EntryDraw)
    (regs : bvmap 5 word) (mem : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream),
  valid_argv [a0s; path] -> valid_envp envp -> valid_sp sp -> (0 < bv_unsigned tid < 2 ^ 22)%Z -> entry_stack_fits sp [a0s; path] envp ->
  main_entry sp [a0s; path] envp tid rndb regs mem ->
  (length path <= 4095)%nat -> path <> [] -> path <> dot_path -> fs_lookup fs0 path = None ->
  realizes RSEGS (mkCfg (mkst regs (0x12ae8 : word) mem (seg_rom RSEGS))
                        (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp target_alloc_limit (mkProcInputC [a0s; path] envp fs0 stdin0))))
           (t_die (msg_cannot_open path) fs0).
Proof.
  intros AMB sp a0s path envp tid rndb regs mem brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hfit ME H1 H2 H3 H4.
  exact (ref_open_fail_absent_w sp a0s path envp tid rndb regs mem brk mbase fs0 stdin0 target_alloc_limit Hva Hve Hvsp Htid Hfit ME H1 H2 H3 H4).
Qed.
End WithFP1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End UbOpenFail.

Module UbOpenFailBranch.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbStartup OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMainEntry OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbUsage.UbOpenFail_defs UbOpenFail OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbPilotOOM.UbPilotOOM_defs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbPilotOOM.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Section WithFP1. Context {FP : PropExec.FPState}.
Section Branch.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rndb : EntryDraw.   (* [comment removed for export] *)
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hfit : entry_stack_fits sp0 [a0s; path] envv.   (* [comment removed for export] *)
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid rndb regs0 mem0.

  Theorem open_err_branch_cannot_open :
    UbPilotOOM.open_err_branch sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 (t_die (msg_cannot_open path) fs0).
  Proof.
    intros e vals R M He HL P0 P38 P1 P2 P5 HR HK Habove.
    apply (UbOpenFail.ref_open_fail_errno sp0 a0s path envv tid rndb regs0 mem0 brk mbase fs0 stdin0 LIM Hva Hve Hvsp Hfit ME
             e vals R M (openat_errnos_range e He) HL P0 P38 P2 HR HK Habove).
  Qed.
End Branch.

(* [comment removed for export] *)
Corollary cannot_open_branch {AMB : Amb} : forall (sp0 : word) (a0s : list byte) (envv : list (list byte)) (tid : word)
    (rndb : EntryDraw) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream),
  valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 -> entry_stack_fits sp0 [a0s; dot_path] envv ->
  main_entry sp0 [a0s; dot_path] envv tid rndb regs0 mem0 ->
  open_err_branch sp0 a0s dot_path envv tid mem0 brk mbase fs0 stdin0 (t_die (msg_cannot_open dot_path) fs0).
Proof.
  intros sp0 a0s envv tid rndb regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Hfit ME.
  exact (open_err_branch_cannot_open sp0 a0s dot_path envv tid rndb regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Hfit ME).
Qed.

(* [comment removed for export] *)
Corollary ref_cannot_open_h : forall (AMB : Amb) (sp : word) (a0s path : list byte) (envp : list (list byte)) (tid : word) (rndb : EntryDraw)
    (regs : bvmap 5 word) (mem : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream),
  valid_argv [a0s; path] -> valid_envp envp -> valid_sp sp -> entry_stack_fits sp [a0s; path] envp ->
  main_entry sp [a0s; path] envp tid rndb regs mem -> (length path <= 4095)%nat ->
  open_err_branch sp a0s path envp tid mem brk mbase fs0 stdin0 (t_die (msg_cannot_open path) fs0).
Proof.
  intros AMB sp a0s path envp tid rndb regs mem brk mbase fs0 stdin0 Hva Hve Hvsp Hfit ME _.
  exact (open_err_branch_cannot_open sp a0s path envp tid rndb regs mem brk mbase fs0 stdin0 Hva Hve Hvsp Hfit ME).
Qed.
End WithFP1.

End UbOpenFailBranch.

Module UbReadErr_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMainEntry OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveH4 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbLibStdioCall.
Unset Lia Cache.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section WithFP1. Context {FP : PropExec.FPState}.
Definition STOPS : list Z := [0x1e6dc; 0x1eae0; 0x1ebd8; 0x1ec1c; 0x12f88; 0x18e44; 0x1755c; 0x19ae4]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition KEPT_MC : list nat := map ridx callee_kept.     (* [comment removed for export] *)
Definition KEPT_CS : list nat := map ridx callee_saved.    (* [comment removed for export] *)
Definition IHI : Z := 0x52000.
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

(* [comment removed for export] *)
Definition srRE_base : list expr :=
  [ELit 0; ELit 0; spx (-128); ELit 0x10800; ELit 0x314d8; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; EVar 2; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0].
Definition KEPT_RE : list nat := [2; 3; 4; 18]%nat.
Definition srRE0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RE 6.

(* [comment removed for export] *)
Definition knRE0 : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) 8388608;
   KRange (EVar 2) 0x7fff80000000 0x800000400000;
   KWr (SA (ELit 0) 0x21000) 0x31000;
   KImg 0x10000 0x21380; KImg 0x21381 0x213c9; KImg 0x313c9 0x31408; KImg 0x514e0 0x51500;
   KWord (SA (ELit 0) 0x31410) 8 (ELit 0x31410);
   KWord (SA (ELit 0) 0x31430) 4 (EVar 5);
   KImg 0x3143c 0x31488; KImg 0x31490 0x314a8; KImg 0x314b0 0x314c8;
   KImg 0x314d8 0x314e8; KImg 0x314f0 0x514e0; KImg 0x51518 0x51744;
   KWord (SA (ELit 0) 0x51748) 8 (EVar 38);
   KImg 0x51750 0x51758; KImg 0x51769 0x51770; KImg 0x51778 0x51780; KImg 0x51790 0x51798;
   KWord (SA (ELit 0) 0x51798) 8 (ELit 4096);
   KImg 0x517a0 0x517d0; KImg 0x517d8 0x517e0;
   KImg 0x51830 0x51990; KImg 0x51998 0x51b10; KImg 0x51b18 0x51b70; KImg 0x51b71 0x51b78;
   KImg 0x51b88 0x52000;
   KRange (EVar 5) 1 4194303].

(* [comment removed for export] *)
Definition ssB0 : sym_state := SS 0x12d14 srRE0 [] knRE0 39.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.
(* [comment removed for export] *)
Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-542)) 1 (ELit 32);
   SE (SA (EVar 0) (-544)) 2 (ELit 28271);
   SE (SA (EVar 0) (-552)) 8 (ELit 2338053693894893668);
   SE (SA (EVar 0) (-560)) 8 (ELit 7018141077071293539)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : sym_state := SS 0x19794 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0x19794 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0x1a4e4 srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0x19794 srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0x19794 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS 0x19794 srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scRE : stdio_res := Eval vm_compute in
  match stdio_call 231 srH knH with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srI0 : list expr := Eval vm_compute in sc_sr scRE.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scRE.

(* [comment removed for export] *)
Definition ssI0 : sym_state := SS (sc_ret scRE) srI0 [] knI0 263.
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

Lemma itinerary_re :
  (s_pc (fst (fst rB)), snd (fst rB)) = (0x1e6dc%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x1e6dc%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x1ebd8%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0x1e6dc%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0x1e6dc%Z, [SCBr true BC_GEU (ELit 61) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0x1e6dc%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 61)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0x19ae4%Z, [])
  /\ stdio_call 231 srH knH = Some scRE
  /\ (sc_ret scRE, sc_f scRE, sc_fd scRE) = (0x19e44%Z, 0x21198%Z, 2%Z)
  /\ (sc_wb scRE, sc_wp scRE, sc_l scRE) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-540)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0x1755c%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.
End WithFP1.


End UbReadErr_defs.

Module UbReadErr_tail.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeLaws OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SpecConsts OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveH4 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWritev OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExitBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbStdioDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbLibStdioCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMemcpyBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMemcpy OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMemchr OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbUsage.UbStrnlen OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbStartup OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMainEntry OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTail.
Import UbReadErr_defs.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

Section WithFP1. Context {FP : PropExec.FPState}.
Section Tail.
  Variable sp0 : word.
  Variable BL : list (list byte).          (* [comment removed for export] *)
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev BL).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma re_segI : forall vals R M,
    length vals = 263%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) srI0 R -> know_ok RSEGS (ENV vals) M knI0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x19e44) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 263%nat.
    (* [comment removed for export] *)
    apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model)))).
    2:{ cbn [W map].
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity).
        apply t_eq_sym. apply t_emit_nil_exit. }
    apply ref_exit_Z.
    pose proof (know_nth RSEGS _ _ knI ltac:(let i := kidx knI (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid.
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x314d8), (bv_unsigned (vals_ev vals 5)),
           (Z_to_bv 64 0), (Z_to_bv 64 0).
    split; [|split; [exact Hh|split; [exact Hlazy|]]].
    + constructor.
      * regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
        rewrite P0. f_equal; lia.
      * regv HR (4 : reg). reflexivity.
      * regv HR (10 : reg). reflexivity.
      * rewrite u_small by lia. lia.
      * rewrite u_small by lia. lia.
      * rewrite u_small by lia.
        pose proof (kwr_store_ok RSEGS (ENV vals) _ knI ltac:(let i := kidx knI (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                      _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia. exact Hst.
      * lit_u. lia.
      * lit_u. lia.
      * lia.
      * lit_u. change (201944 - 168)%Z with 0x31430%Z.
        krd HK 0x31430%Z 4%nat Htc. rewrite Htc. cbn [ev ENV].
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia).
        rewrite Z_to_bv_bv_unsigned. reflexivity.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * repeat split; krd_solve HK.
      * repeat split; krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * left. unfold ax_empty. krd_solve HK.
    + left. split; [reflexivity|].
      exists (Z_to_bv 64 0), (Z_to_bv 64 0). repeat split; krd_solve HK.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition PRE19 : list byte := s2b "cli: read error on "%string.

  Lemma PRE19_words :
    word_to_le_bytes 8 (Z_to_bv 64 7018141077071293539)
    ++ word_to_le_bytes 8 (Z_to_bv 64 2338053693894893668)
    ++ word_to_le_bytes 2 (Z_to_bv 64 28271)
    ++ word_to_le_bytes 1 (Z_to_bv 64 32) = PRE19.
  Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.

  Lemma re_segH : forall (path : list byte) (P : Z) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 60)%Z ->
    length vals = 231%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
    regs_ok (ENV vals) srH0 R -> know_ok RSEGS (ENV vals) M knH0 ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 541 + P)) 1%nat = Some [Z_to_bv 8 10] ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x19794) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_read_error path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path P vals R M HP HPr HL P0 P113 HR HK SBp SBn.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scr0 231%nat.
    (* [comment removed for export] *)
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    assert (SBn' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 541 + P)) 1 = Some [Z_to_bv 8 10]).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBn | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; cbn; lia]. }
    clear EQM SBp SBn. rename M0 into M'. 
    (* [comment removed for export] *)
    krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-552)%Z 8%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-544)%Z 2%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-542)%Z 1%nat Hw3. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0, Hw1, Hw2, Hw3. cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2, Hw3.
    rewrite P0 in Hw0, Hw1, Hw2, Hw3.
    assert (H17 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) 19 = Some PRE19).
    { rewrite <- PRE19_words. change 19%nat with (8 + (8 + (2 + 1)))%nat.
      apply rdn_app_Z; [exact Hw0 | | lia | lia].
      apply rdn_app_Z; [ | | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -552)%Z by lia. exact Hw1.
      + apply rdn_app_Z; [ | | lia | lia].
        * replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -544)%Z by lia. exact Hw2.
        * replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 2)%Z with (bv_unsigned sp0 + -542)%Z by lia.
          exact Hw3. }
    assert (MSG : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (19 + (length path + 1))
                  = Some (msg_read_error path)).
    { unfold msg_read_error. change (s2b _) with PRE19.
      apply rdn_app_Z; [exact H17 | | lia | lia].
      apply rdn_app_Z; [| | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 19)%Z with (bv_unsigned sp0 - 541)%Z by lia. exact SBp'.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 19 + Z.of_nat (length path))%Z
          with (bv_unsigned sp0 - 541 + P)%Z by lia. exact SBn'. }
    (* [comment removed for export] *)
    assert (LEN : length (msg_read_error path) = (19 + (length path + 1))%nat)
      by (unfold msg_read_error; rewrite !length_app; reflexivity).
    replace (W 2 (msg_read_error path)) with (map (WriteEv (Z_to_bv 64 2)) (msg_read_error path ++ []))
      by (unfold W; rewrite app_nil_r; reflexivity).
    pose proof itinerary_re as (_ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srH knH Rc Mc model scRE (msg_read_error path) []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH knH) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scRE]; rewrite ?LEN end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - cbn [edenot length]. reflexivity.
    - pose proof rw_bytes_max_ge17. cbn [length Z.of_nat]. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - left. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z in MSG by lia. exact MSG.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (re_segI (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma re_nl_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x10388) 1 = Some [Z_to_bv 8 10].
  Proof. vm_compute. reflexivity. Qed.

  Lemma re_segG : forall (path : list byte) (P : Z) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 60)%Z ->
    length vals = 199%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
    regs_ok (ENV vals) srG0 R -> know_ok RSEGS (ENV vals) M knG0 ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x19794) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_read_error path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path P vals R M HP HPr HL P0 P113 HR HK SBp.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scrG 199%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113).
      replace (-1 * P + 61)%Z with (61 - P)%Z by lia.
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    clear EQM SBp. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541 + P)).
    assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x10388) 1 = Some [Z_to_bv 8 10]).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kimg_cov 0x10388 1) in exact i)
                 _ _ 0x10388 1 HK eq_refl) by (cbn; lia). apply re_nl_img. }
    assert (Hdst : store_ok RSEGS M' dst 1 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kwr_cov (EVar 0) (-541) 64) in exact i)
                    _ _ _ (-541 + P) 1 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 541 + P)%Z with (bv_unsigned sp0 + (-541 + P))%Z by lia. exact Hst. }
    assert (MC : mcH M' dst (Z_to_bv 64 0x10388) 1 [Z_to_bv 8 10]).
    { constructor; cbn [length Z.to_nat Z.of_nat Pos.to_nat]; subst dst; rewrite ?u_small by lia; try lia.
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x19794 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x10388) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 1) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M' dst (Z_to_bv 64 0x10388) 1 _ (seg_rom RSEGS) MC Rc (0x19794 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 124636) with (0x1e6dc : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x19794 : word) with (Z_to_bv 64 0x19794) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst [Z_to_bv 8 10]) 0 (-541) BUF_HI IHI knG
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst [Z_to_bv 8 10] (ENV vals) 0 (-541) BUF_HI);
                        cbn [ev ENV length]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-541) BUF_HI IHI knG) with knH0 in HK2.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) _ knH0 ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 231%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P113).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    eapply (re_segH path P vals1); try eassumption.
    - (* [comment removed for export] *)
      rewrite rdn_wbytes_out; [exact SBp' | | |]; cbn [length]; subst dst; rewrite ?u_small by lia; lia.
    - (* [comment removed for export] *)
      subst dst. pose proof (rdn_wbytes_hit RSEGS [Z_to_bv 8 10] M' (Z_to_bv 64 (bv_unsigned sp0 - 541 + P))) as Hn.
      cbn [length] in Hn. apply Hn. rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition reG0 (path : list byte) (P : Z) (T : TSet) : Prop :=
    forall vals R M,
      length vals = 199%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
      regs_ok (ENV vals) srG0 R -> know_ok RSEGS (ENV vals) M knG0 ->
      rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x19794) M (seg_rom RSEGS)) model) T.

  (* [comment removed for export] *)
  Lemma re_segF_gen : forall (path : list byte) (pp : word) (P : Z) (T : TSet) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 61)%Z ->
    length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    reG0 path P T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x19794) M (seg_rom RSEGS)) model) T.
  Proof.
    intros path pp P T vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 HR HK Hstr HG0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (Psmall : (bv_unsigned (edenot (ENV vals) PX) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV PX]. rewrite P113, u_small by lia. lia. }
    unfold PX in Psmall.
    (* [comment removed for export] *)
    run_blk_keep scrF 167%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P113).
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken].
      rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia
        | cbn [ev ENV]; rewrite P0; lia]. }
    clear EQM Hstr. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541)).
    assert (Hsrc : rdn RSEGS M' pp (length path) = Some path).
    { rewrite <- (firstn_app_l _ path [Z_to_bv 8 0]) at 2 || idtac.
      replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
    assert (Hdst : store_ok RSEGS M' dst (length path) = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knF ltac:(let i := kidx knF (is_kwr_cov (EVar 0) (-541) 63) in exact i)
                    _ _ _ (-541) (length path) HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 541)%Z with (bv_unsigned sp0 + -541)%Z by lia. exact Hst. }
    assert (MC : mcH M' dst pp P path).
    { constructor; subst dst; rewrite ?u_small by lia; try lia.
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x19794 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = pp) by (regv HR (11 : reg); cbn [edenot ev ENV]; exact P2);
      assert (A12 : getr Rc 12 = Z_to_bv 64 P) by (regv HR (12 : reg); cbn [edenot ev ENV]; exact P113);
      destruct (ref_memcpy M' dst pp P _ (seg_rom RSEGS) MC Rc (0x19794 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 124636) with (0x1e6dc : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x19794 : word) with (Z_to_bv 64 0x19794) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst path) 0 (-541) BUF_HI IHI knF
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst path (ENV vals) 0 (-541) BUF_HI);
                        cbn [ev ENV]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-541) BUF_HI IHI knF) with knG0 in HK2.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) _ knG0 ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 199%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P113).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    eapply (HG0 vals1); try eassumption.
    (* [comment removed for export] *)
    subst dst. rewrite <- HP at 1 || idtac.
    pose proof (rdn_wbytes_hit RSEGS path M' (Z_to_bv 64 (bv_unsigned sp0 - 541))) as Hc.
    apply Hc. rewrite u_small by lia. lia.
  Qed.

  Lemma re_segF : forall (path : list byte) (pp : word) (P : Z) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 60)%Z ->
    length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x19794) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_read_error path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path pp P vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 HR HK Hstr.
    eapply (re_segF_gen path pp P _ vals); try eassumption; [lia|].
    intros vals' R' M' HL' Q0 Q113 HR' HK' SB. eapply (re_segG path P vals'); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition reF0 (path : list byte) (pp : word) (P : Z) (T : TSet) : Prop :=
    forall vals R M,
      length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
      regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
      rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x19794) M (seg_rom RSEGS)) model) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma re_segDE : forall (path : list byte) (pp : word) (P : Z) (T : TSet) (t8 : list byte) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 131071)%Z -> ~ In (Z_to_bv 8 0) path ->
    length vals = 103%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srD0 R -> know_ok RSEGS (ENV vals) M knC ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8 ->
    reF0 path pp P T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x19794) M (seg_rom RSEGS)) model) T.
  Proof.
    intros path pp P T t8 vals R M HP HPr Hnonul HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8 HF0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    (* [comment removed for export] *)
    run_blk_keep scr0 103%nat.
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
        | cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
    clear EQM Hstr Ht8. rename M0 into M'.
    (* [comment removed for export] *)
    set (spS := Z_to_bv 64 (bv_unsigned sp0 - 1120)).
    assert (Hbuf : rdn RSEGS M' pp (length (path ++ t8)) = Some (path ++ t8)).
    { rewrite length_app. rewrite (word_Z pp). apply rdn_app_Z; [ | | lia | lia].
      - rewrite <- (word_Z pp). replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
          by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
        eapply rdn_firstn; [exact Hstr' | lia].
      - pose proof (rdn_length _ _ _ _ _ Ht8') as L8. rewrite L8, HP. exact Ht8'. }
    assert (Hz : nth (length path) (path ++ t8) (Z_to_bv 8 0) = Z_to_bv 8 0).
    { pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
      rewrite app_nth2, Nat.sub_diag by lia.
      pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp) (length path + 1) _ (length path)
                    ltac:(rewrite <- (word_Z pp); exact Hstr') ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
      pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp + P) 8 t8 0 Ht8' ltac:(lia) ltac:(lia) ltac:(lia)) as B2.
      replace (bv_unsigned pp + Z.of_nat (length path))%Z with (bv_unsigned pp + P)%Z in B1 by lia.
      replace (bv_unsigned pp + P + Z.of_nat 0)%Z with (bv_unsigned pp + P)%Z in B2 by lia.
      rewrite B1 in B2. injection B2 as E. rewrite <- E. rewrite app_nth2, Nat.sub_diag by lia. reflexivity. }
    assert (MC : mchrH M' pp (path ++ t8) P 0x7fffffff).
    { pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
      constructor.
      - exact Hbuf.
      - rewrite length_app, L8.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      - rewrite length_app, L8. lia.
      - lia.
      - rewrite <- HP, Nat2Z.id, Hz. reflexivity.
      - intros j Hj. rewrite <- HP, Nat2Z.id in Hj. rewrite nth_app_l by exact Hj.
        intros E. apply (In_nth_neq path (Z_to_bv 8 0) (Z_to_bv 8 0) j Hnonul Hj). apply bv_eq. exact E.
      - lia.
      - lia.
      - intros i Hi.
        pose proof (know_nth RSEGS _ _ knD ltac:(let k := kidx knD (is_kimg_cov 0x106f0 24) in exact k) _ HK eq_refl)
          as (_ & _ & Hnone). apply Hnone. lia. }
    assert (Hstk : store_ok RSEGS M' (Z_to_bv 64 (bv_unsigned spS - 32)) 32 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knD ltac:(let i := kidx knD (is_kwr_cov (EVar 0) (-1152) 32) in exact i)
                    _ _ _ (-1152) 32 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst spS. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 1120 - 32)%Z with (bv_unsigned sp0 + -1152)%Z by lia. exact Hst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x1a4e4 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A2 : getr Rc 2 = spS)
        by (regv HR (2 : reg); subst spS; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A10 : getr Rc 10 = pp) by (regv HR (10 : reg); cbn [edenot ev ENV]; exact P2);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x7fffffff) by (regv HR (11 : reg); reflexivity);
      destruct (ref_strnlen M' pp spS (path ++ t8) P 0x7fffffff (seg_rom RSEGS) Rc (0x1a4e4 : word) MC
                  ltac:(lia) Hstk ltac:(subst spS; rewrite u_small by lia; lia)
                  ltac:(right; subst spS; rewrite u_small by lia; lia)
                  ltac:(apply ret_ok_even; reflexivity) A1 A2 A10 A11) as (R2 & M2 & Hms & Hkeep & HresP & Hfr);
      clear A1 A2 A10 A11
    end.
    replace (Z_to_bv 64 125912) with (0x1ebd8 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x1a4e4 : word) with (Z_to_bv 64 0x1a4e4) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_saved
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_saved_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    destruct Hfr as [Hagree Hgrow].
    pose proof (know_cut_sound RSEGS (ENV vals) M' M2 0 (-1152) (-1120) IHI knD
                  ltac:(unfold win_ok, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(intros x Hx; apply Hagree; cbn [outside]; split; [|exact I];
                        unfold in_rng; subst spS; unorm;
                        cbn [ev ENV] in Hx; rewrite P0 in Hx; lia)
                  Hgrow HK) as HK2.
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) M2 (kn_cut 0 (-1152) (-1120) IHI knD)
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 135%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals1 2 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P).
    { subst vals1. change 113%nat with (103 + 10)%nat. rewrite <- HL. rewrite vals_ev_junk by lia. exact HresP. }
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK3.
    assert (HK : know_ok RSEGS (ENV vals1) M2 knE0).
    { unfold knE0. apply know_ok_cons; [|exact HK3].
      apply krange_intro. cbn [edenot ev ENV PX]. rewrite Q113, u_small by lia. lia. }
    clear HK3.
    (* [comment removed for export] *)
    assert (Hstr2 : rdn RSEGS M2 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite (frame_mod_rdn RSEGS M' M2 _ _ pp (conj Hagree Hgrow)); [exact Hstr' | | lia].
      intros i Hi. cbn [outside]. split; [|exact I]. unfold in_rng. subst spS. unorm. lia. }
    clear Hstr' Ht8' Hbuf Hz MC Hstk Hagree Hgrow HresP.
    assert (Psmall : (bv_unsigned (edenot (ENV vals1) (EVar 113)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite Q113, u_small by lia. lia. }
    (* [comment removed for export] *)
    run_blk_keep scrE 135%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. rewrite (edenot_addw0_r _ _ Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    { (* [comment removed for export] *)
      unfold sc_denot. exists [Z_to_bv 8 0]. split.
      - unfold adenot, v_addi. cbn [a_base a_off]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
        ed_lin ltac:(cbn [ev ENV]; rewrite ?Q2, ?Q113). rewrite <- HP.
        pose proof (rdn_byte_Z RSEGS M2 (bv_unsigned pp) (length path + 1) _ (length path)
                      ltac:(rewrite <- (word_Z pp); exact Hstr2) ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
        rewrite app_nth2, Nat.sub_diag in B1 by lia. cbn [nth] in B1. exact B1.
      - reflexivity. }
    assert (Hstr3 : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M2 _ 0 0 4194304 IHI);
        [exact Hstr2 | vm_compute; reflexivity | unfold win_ok, IHI; cbn [ev ENV]; rewrite Q0; lia
        | cbn [ev ENV]; rewrite Q0; lia | cbn [ev ENV]; rewrite Q0; lia]. }
    clear EQM Hstr2. rename M0 into M3.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541)).
    assert (MC : mcH M3 dst (Z_to_bv 64 0x10298) 0 []).
    { constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x19794 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x10298) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M3 dst (Z_to_bv 64 0x10298) 0 _ (seg_rom RSEGS) MC Rc (0x19794 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 124636) with (0x1e6dc : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    change (wbytes M3 dst []) with M3.
    replace (0x19794 : word) with (Z_to_bv 64 0x19794) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R4 callee_kept
                    ltac:(rewrite HL1; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL1 in HR2. clear HR Hkeep. rename HR2 into HR.
    pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev BL) M3 knE ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    set (vals2 := vals1 ++ junk_vals R4) in *.
    assert (HL2 : length vals2 = 167%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
    assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
    assert (W2 : vals_ev vals2 2 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q2).
    assert (W113 : vals_ev vals2 113 = Z_to_bv 64 P) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q113).
    clearbody vals2.
    change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
    eapply (HF0 vals2); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma pre19_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x10373) 19 = Some PRE19.
  Proof. vm_compute. reflexivity. Qed.

  Lemma PRE19_len : length PRE19 = 19%nat.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma re_memcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV vals) M logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 560)) PRE19.
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- PRE19_words. cbn [mem_denot logM1]. rewrite !wbytes_app.
    unfold adenot, v_addi, at_. cbn [a_base a_off edenot ev ENV length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite P0.
    rewrite !length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unorm.
    repeat (f_equal; try (f_equal; lia)).
  Qed.

  Lemma re_segBC : forall (path : list byte) (pp : word) (P : Z) (T : TSet) (t8 : list byte) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 131071)%Z -> ~ In (Z_to_bv 8 0) path ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srRE0 R -> know_ok RSEGS (ENV vals) M knRE0 ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8 ->
    reF0 path pp P T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12d14) M (seg_rom RSEGS)) model) T.
  Proof.
    intros path pp P T t8 vals R M HP HPr Hnonul HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8 HF0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    (* [comment removed for export] *)
    run_blk_keep scr0 39%nat.
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
        | cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
    clear EQM Hstr Ht8. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
    assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x10373) 19 = Some PRE19).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kimg_cov 0x10373 19) in exact i)
                 _ _ 0x10373 19 HK eq_refl) by (cbn; lia). apply pre19_img. }
    assert (Hdst : store_ok RSEGS M' dst 19 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-560) 19) in exact i)
                    _ _ _ (-560) 19 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
    assert (MC : mcH M' dst (Z_to_bv 64 0x10373) 19 PRE19).
    { constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x19794 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x10373) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 19) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M' dst (Z_to_bv 64 0x10373) 19 _ (seg_rom RSEGS) MC Rc (0x19794 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 124636) with (0x1e6dc : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x19794 : word) with (Z_to_bv 64 0x19794) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    assert (HK2 : know_ok RSEGS (ENV vals) (wbytes M' dst PRE19) knC0).
    { subst dst. rewrite <- (re_memcpy1_denot vals M' P0).
      eapply (carry_after RSEGS (ENV vals) M' logM1 knB [] knC0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat logM1].
      repeat match goal with
             | |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
             | |- (_ <= _)%nat => lia
             | |- True => exact I
             | |- _ /\ _ => split
             end. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M' dst PRE19) knC0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 71%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals1 2 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    (* [comment removed for export] *)
    assert (Hstr2 : rdn RSEGS (wbytes M' dst PRE19) pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite rdn_wbytes_out; [exact Hstr' | | |]; subst dst; rewrite ?PRE19_len; unorm; lia. }
    assert (Ht82 : rdn RSEGS (wbytes M' dst PRE19) (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite rdn_wbytes_out; [exact Ht8' | | |]; subst dst; rewrite ?PRE19_len; unorm; lia. }
    clear Hstr' Ht8' Hsrc Hdst MC. clearbody dst.
    set (M1 := wbytes M' dst PRE19) in *. clearbody M1. clear M' dst.
    assert (WOKS1 : win_ok (ENV vals1) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite Q0. lia. }
    (* [comment removed for export] *)
    run_blk_keep scr0 71%nat.
    assert (Hstr3 : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M1 _ 0 0 4194304 IHI);
        [exact Hstr2 | vm_compute; reflexivity | exact WOKS1 | cbn [ev ENV]; rewrite Q0; lia | cbn [ev ENV]; rewrite Q0; lia]. }
    assert (Ht83 : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M1 _ 0 0 4194304 IHI);
        [exact Ht82 | vm_compute; reflexivity | exact WOKS1 | cbn [ev ENV]; rewrite Q0, u_small by lia; lia
        | cbn [ev ENV]; rewrite Q0, u_small by lia; lia]. }
    clear EQM Hstr2 Ht82. rename M0 into M3.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541)).
    assert (MC : mcH M3 dst (Z_to_bv 64 0x10386) 0 []).
    { constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x19794 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x10386) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M3 dst (Z_to_bv 64 0x10386) 0 _ (seg_rom RSEGS) MC Rc (0x19794 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 124636) with (0x1e6dc : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    change (wbytes M3 dst []) with M3.
    replace (0x19794 : word) with (Z_to_bv 64 0x19794) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R4 callee_kept
                    ltac:(rewrite HL1; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL1 in HR2. clear HR Hkeep. rename HR2 into HR.
    pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev BL) M3 knC ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    set (vals2 := vals1 ++ junk_vals R4) in *.
    assert (HL2 : length vals2 = 103%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
    assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
    assert (W2 : vals_ev vals2 2 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q2).
    clearbody vals2.
    change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
    eapply (re_segDE path pp P T t8 vals2); eassumption.
  Qed.

End Tail.
End WithFP1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End UbReadErr_tail.

Module UbReadErr.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveH4 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExitBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMainEntry OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTail OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbWorld.
Import UbReadErr_defs UbReadErr_tail.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
Definition re_ivs : list (Z * Z) :=
  [(0x10000,0x21380); (0x21381,0x213c9); (0x313c9,0x31408); (0x514e0,0x51500); (0x3143c,0x31488); (0x31490,0x314a8);
   (0x314b0,0x314c8); (0x314d8,0x314e8); (0x314f0,0x514e0); (0x51518,0x51744); (0x51750,0x51758); (0x51769,0x51770);
   (0x51778,0x51780); (0x51790,0x51798); (0x517a0,0x517d0); (0x517d8,0x517e0);
   (0x51830,0x51990); (0x51998,0x51b10); (0x51b18,0x51b70); (0x51b71,0x51b78); (0x51b88,0x52000)]%Z.

Lemma re_ivs_incl : incl re_ivs img_clear_ivs.
Proof using . unfold re_ivs, img_clear_ivs. intros x Hx. cbn in Hx |- *. tauto. Qed.

Lemma re_ivs_of_world : forall M,
  Forall (fun iv => img_clear M (fst iv) (snd iv)) img_clear_ivs ->
  Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
Proof using . intros M H. eapply incl_Forall; [apply re_ivs_incl | exact H]. Qed.

Section ReadErr.
  Variable sp0 : word.
  Variable BL : list (list byte).
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  (* [comment removed for export] *)
  Theorem re_tail : forall (path : list byte) (pp : word) (t8 : list byte) vals R M,
    ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) <= 60)%Z ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z ->
    (bv_unsigned pp + Z.of_nat (length path) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV BL vals) srRE0 R -> know_ok RSEGS (ENV BL vals) M knRE0 ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length path))) 8 = Some t8 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12d14) M (seg_rom RSEGS)) model)
               (t_die (msg_read_error path) (m_fs model)).
  Proof using Hfd2 Hh Hlazy Hvsp.
    intros path pp t8 vals R M Hnonul HPl HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8.
    unfold t_die.
    eapply (re_segBC sp0 BL model Hvsp Hh Hlazy path pp (Z.of_nat (length path)) _ t8 vals);
      try eassumption; try lia.
    intros vals' R' M' HL' Q0 Q2 Q113 HR' HK' Hstr'.
    eapply (re_segF sp0 BL model Hvsp Hh Hlazy Hfd2 path pp _ vals'); try eassumption; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variables (pp : word) (tid cnr : Z) (R : bvmap 5 word) (M : word -> option byte).
  (* [comment removed for export] *)
  Hypothesis Rsp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
  Hypothesis Rgp : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis Rtp : getr R 4 = Z_to_bv 64 0x314d8.
  Hypothesis Rs2 : getr R 18 = pp.
  (* [comment removed for export] *)
  Hypothesis Mstack : stack_writable M sp0.
  Hypothesis Mimg : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
  Hypothesis Mtid : cell M 0x31430 4 tid.
  Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
  Hypothesis Mself : cell M 0x31410 8 0x31410.
  Hypothesis Mcanary : cell M 0x51748 8 cnr.
  Hypothesis Mpagesz : cell M 0x51798 8 4096.
  (* [comment removed for export] *)
  Hypothesis Hpp1 : (bv_unsigned sp0 <= bv_unsigned pp)%Z.

  Definition valsRE : list word :=
    [sp0; pp; pp; pp; pp; Z_to_bv 64 tid] ++ junk_vals R ++ [Z_to_bv 64 cnr].
  Let E : env := ENV BL valsRE.

  Lemma valsRE_len : length valsRE = 39%nat.
  Proof using . unfold valsRE. rewrite !length_app, junk_vals_length. reflexivity. Qed.

  Lemma evRE_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof using BL cnr pp sp0 tid.
    intros i Hi. unfold E, ENV. cbn [ev]. unfold valsRE.
    change (6 + i)%nat with (length [sp0; pp; pp; pp; pp; Z_to_bv 64 tid] + i)%nat.
    unfold vals_ev. rewrite app_nth2_plus, app_nth1 by (rewrite junk_vals_length; exact Hi).
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma spxRE_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof using BL R cnr pp tid. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

  Ltac reg_caseRE :=
    cbn [nth srRE0 all_regs];
    first [ rewrite spxRE_val
          | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot E (EVar n)) with (ev E n);
              first [ rewrite (evRE_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact Rgp | exact Rtp | exact Rs2
          | rewrite Rsp, alu_add; change (ev E 0) with sp0; unfold v_add; apply bv_eq;
            rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia
          | idtac ].

  Lemma regs_okRE : regs_ok E srRE0 R.
  Proof using BL Rgp Rs2 Rsp Rtp SPhi SPlo cnr tid.
    pose proof SPlo. pose proof SPhi.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseRE.
  Qed.

  Lemma img_clear_of : forall lo hi, In (lo, hi) re_ivs -> img_clear M lo hi.
  Proof using Mimg. intros lo hi Hin. exact (proj1 (Forall_forall _ _) Mimg (lo, hi) Hin). Qed.

  Ltac kimg := split; [lia|]; split; [lia|]; apply img_clear_of; clear; cbn; tauto.
  Ltac kcell H := split; [lia|]; split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|];
                 rewrite adenot_lit0; cbn [edenot];
                 first [exact H | rewrite H; reflexivity | idtac].

  Lemma know_okRE : (bv_unsigned pp + 8 <= bv_unsigned sp0 + 4194304)%Z -> know_ok RSEGS E M knRE0.
  Proof using BL Hpp1 Htid Mcanary Mimg Mpagesz Mself Mstack Mtid R SPal SPhi SPlo.
    intros Hpp2. pose proof SPlo. pose proof SPhi. pose proof SPal.
    unfold know_ok, knRE0.
    repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok].
    - (* [comment removed for export] *) split; [lia|]. change (edenot E (EVar 0)) with sp0. exact SPal.
    - change (edenot E (EVar 0)) with sp0. lia.
    - (* [comment removed for export] *) split; [apply flat_intro; cbn; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off]. change (edenot E (EVar 0)) with sp0.
      replace (bv_unsigned sp0 + -8388608 + d)%Z with (bv_unsigned sp0 - 8388608 + d)%Z by lia.
      apply Mstack; lia.
    - change (edenot E (EVar 2)) with pp. lia.
    - (* [comment removed for export] *) split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia.
      apply store_ok_data; rewrite u_small by lia; lia.
    - kimg. - kimg. - kimg. - kimg.
    - kcell Mself.
    - kcell Mtid.
    - kimg. - kimg. - kimg. - kimg. - kimg. - kimg.
    - kcell Mcanary.
    - kimg. - kimg. - kimg. - kimg.
    - kcell Mpagesz.
    - kimg.
    - kimg. - kimg. - kimg. - kimg. - kimg. - kimg.
    - change (edenot E (EVar 5)) with (Z_to_bv 64 tid : word). rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem ref_read_error : forall (path : list byte) (t8 : list byte),
    ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) <= 60)%Z ->
    (bv_unsigned pp + Z.of_nat (length path) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length path))) 8 = Some t8 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12d14) M (seg_rom RSEGS)) model)
               (t_die (msg_read_error path) (m_fs model)).
  Proof using E Hfd2 Hh Hlazy Hpp1 Htid Mcanary Mimg Mpagesz Mself Mstack Mtid Rgp Rs2 Rsp Rtp SPal SPhi SPlo.
    intros path t8 Hnonul HPl Hpp2 Hstr Ht8.
    eapply (re_tail path pp t8 valsRE R M); try eassumption.
    - apply valsRE_len.
    - reflexivity.
    - reflexivity.
    - apply regs_okRE.
    - apply know_okRE. lia.
  Qed.

  Corollary ref_read_error_dot : forall (t8 : list byte),
    (bv_unsigned pp + 9 <= bv_unsigned sp0 + 4194304)%Z ->
    rdn RSEGS M pp 2 = Some [Z_to_bv 8 46; Z_to_bv 8 0] ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + 1)) 8 = Some t8 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12d14) M (seg_rom RSEGS)) model)
               (t_die (msg_read_error dot_path) (m_fs model)).
  Proof using E Hfd2 Hh Hlazy Hpp1 Htid Mcanary Mimg Mpagesz Mself Mstack Mtid Rgp Rs2 Rsp Rtp SPal SPhi SPlo.
    intros t8 Hpp2 Hstr Ht8.
    apply (ref_read_error dot_path t8).
    - cbn. intros [E0|[]]. apply (f_equal bv_unsigned) in E0. vm_compute in E0. lia.
    - cbn. lia.
    - cbn [length dot_path Z.of_nat Pos.of_succ_nat]. lia.
    - exact Hstr.
    - exact Ht8.
  Qed.
End ReadErr.
End WithFP1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End UbReadErr.

Module UbDirTail.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbStartup OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMainEntry OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbUsage.UbMainEntryN OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbWorld OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbDirMid UbReadErr.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section WithFP1. Context {FP : PropExec.FPState}.
Theorem dir_tail : forall (AMB : Amb) (sp0 : word) (a0s : list byte) (envv : list (list byte)) (tid : word)
    (rndb : EntryDraw) (regs0 : bvmap 5 word) (mem0 : word -> option byte),
  valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
  main_entry sp0 [a0s; dot_path] envv tid rndb regs0 mem0 ->
  forall (cnr : Z) (R : bvmap 5 word) (M : word -> option byte) (model : Model),
    m_halted model = None -> m_vm_lazy model = [] ->
    fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    dir_tail_pre sp0 (p1 sp0 a0s dot_path envv) (bv_unsigned tid) cnr mem0 R M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12d14) M (seg_rom RSEGS)) model)
               (t_die (msg_read_error dot_path) (m_fs model)).
Proof.
  intros AMB sp0 a0s envv tid rndb regs0 mem0 Hva Hve Hvsp Htid ME cnr R M model Hh Hlazy Hfd2 P.
  destruct P as [Rsp Rgp Rtp Rs2 Mstack Mimg Mtid Htidr Mself Mcanary Mpagesz Habove].
  pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
  unfold sp_window_lo, sp_window_hi in SPlo, SPhi.
  edestruct (@main_strN AMB sp0 [a0s; dot_path] envv tid rndb regs0 mem0 Hva Hve Hvsp ME 1%nat) as (Sr & Slo & Shi & Slen & t8 & Ht8);
    [cbn; lia|].
  cbn [nth length Nat.add dot_path app] in Sr, Slo, Shi, Ht8.
  set (pp := p1 sp0 a0s dot_path envv) in *.
  change (cat_argv_ptr sp0 [a0s; dot_path] envv 1) with pp in Sr, Slo, Shi, Ht8.
  change (Z.of_nat 1) with 1%Z in Ht8.
  pose proof (u64_range pp) as Hppr.
  assert (Hstr : rdn RSEGS M pp 2 = Some [Z_to_bv 8 46; Z_to_bv 8 0]).
  { rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia. }
  assert (Ht8' : rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + 1)) 8 = Some t8).
  { rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove.
    rewrite (u_small (bv_unsigned pp + 1)) by lia. rewrite u_small by lia. lia. }
  exact (ref_read_error_dot sp0 [] model Hvsp Hh Hlazy Hfd2 pp (bv_unsigned tid) cnr R M
           Rsp Rgp Rtp Rs2 Mstack Mimg Mtid Htidr Mself Mcanary
           Mpagesz Slo t8 ltac:(lia) Hstr Ht8').
Qed.
End WithFP1.
End UbDirTail.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import Amb PropExec CatExec CatSim SeqExec StoreOk ShapeAlg ShapeLaws SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Spec UbStartup UbMainEntry UbReadDefs UbReadBase UbReadStage UbWorld UbWorldK UbTargetPre UbTargetPreK UbSymPlanSoundA. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require UbPilotOOM. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbPilotOOM.UbPilotOOM_defs. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import UbPilotOOM. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require UbDirMid. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbDirMid.UbW65x. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require UbReadBig. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbReadBig.UbRead0. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import UbReadBig. Import UbLeafHeader. Import UbHeaderK. Import UbRefused. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import UbDirMid. Import UbLeafDir. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import UbMain UbUsage. Import UbOpenFail. Import UbOpenFailBranch. Import UbDirTail.
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
#[local] Existing Instance PropExec.fp0.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition target_phase_stmt : Prop :=
  forall (sp0 gm area brkv mas tid sec cnr : Z) (content : list byte)
         (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (model : Model),
    target_pre sp0 gm area brkv mas tid sec cnr content R M -> target_vm sp0 gm area VM -> SPSA.std_model VM model ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12db8) M (seg_rom RSEGS)) model) (t_target content (m_fs model)).

Definition target_phase_k_stmt : Prop :=
  forall k : Z, (1 <= k <= 10)%Z ->
  forall (sp0 B area brkv mas tid sec cnr : Z) (content : list byte)
         (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (model : Model),
    target_pre_k k sp0 B area brkv mas tid sec cnr content R M -> target_vm_k k sp0 B area VM -> SPSA.std_model VM model ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12db8) M (seg_rom RSEGS)) model) (t_target content (m_fs model)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ref_list_byte_eqb_eq : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
  induction p as [|a p IH]; destruct q as [|b q]; cbn; try (split; congruence).
  rewrite Bool.andb_true_iff, IH. unfold bv_eqb. rewrite Z.eqb_eq.
  split.
  - intros [H1 ->]. f_equal. apply bv_eq. exact H1.
  - intros H. injection H. intros -> ->. auto.
Qed.

(* [comment removed for export] *)
Lemma t_body_big : forall (data : list byte) (fs0 : Fs),
  (65536 <= Z.of_nat (length data))%Z ->
  t_eq (if (Z.of_nat (length data) <? 67108864)%Z then t_body data fs0 else t_die msg_refused fs0) (t_body data fs0).
Proof.
  intros data fs0 H. destruct (Z.ltb_spec (Z.of_nat (length data)) 67108864) as [Hlt|Hge].
  - apply t_eq_refl.
  - unfold t_body. rewrite (proj2 (Z.leb_le MAX_INPUT (Z.of_nat (length data)))) by (unfold MAX_INPUT; lia).
    apply t_eq_refl.
Qed.

Lemma target_vm_of_small : forall (VM : VmMaps) (sp0 mb gm : word) (area : Z),
  area = (bv_unsigned mb + 4096)%Z -> vm_pre VM sp0 mb gm -> vm_small VM gm ->
  target_vm (bv_unsigned sp0) (bv_unsigned gm) area VM.
Proof.
  intros VM sp0 mb gm area Harea (Pr & Pl & Psp & Ph & Pf & Pn & Plive & (p & Pin & Pne & Plo & Phi) & Pseps)
         (Vr & Vl & Vn & Vin & Vf & Vs).
  constructor.
  - exact Vr.
  - rewrite Z_to_bv_bv_unsigned. exact Psp.
  - rewrite Z_to_bv_bv_unsigned. exact Vin.
  - exists (fst p), (snd p). destruct p as [lo sz]. cbn [fst snd] in *. split; [exact Pin|]. lia.
  - exact Vn.
  - exact Vf.
  - exact Vs.
  - exact Vl.
Qed.

Section Driver.
  Context {AMB : Amb}.
  Hypothesis TPH : target_phase_stmt.
  Hypothesis TPKH : target_phase_k_stmt.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section FileExists.
    Variable sp0 : word.
    Variables a0s path : list byte.
    Variable envv : list (list byte).
    Variable tid : word.
    Variable rndb : EntryDraw.
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
    Hypothesis ME : main_entry sp0 [a0s; path] envv tid rndb regs0 mem0.
    Hypothesis Hbrk : valid_brk RSEGS brk.
    Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
    Hypothesis Hpne : path <> [].
    Hypothesis Hpnd : path <> dot_path.
    Hypothesis Hplen : (length path <= 4095)%nat.
    Hypothesis Hpdd : path <> dotdot_path.
    Hypothesis Hpsl : path_has_slash path = false.

    Lemma after_malloc_main : after_malloc sp0 a0s path envv tid fs0 stdin0 (t_opened fdata fs0).
    Proof using Hfile Hplen Hvsp TPH TPKH.
      unfold after_malloc. intros R M VM mb gm sec cnr area brkv mas Harea RP W MF VP VS.
      pose proof Hvsp as Hvsp'. destruct Hvsp' as (SPlo & SPhi & SPal).
      unfold sp_window_lo, sp_window_hi in SPlo, SPhi.
      pose proof (rp_gm _ _ _ _ _ _ _ _ RP) as Hgm.
      unfold t_opened.
      destruct (Z.ltb_spec0 (Z.of_nat (length fdata)) 65536) as [Hlt|Hge].
      - (* [comment removed for export] *)
        apply (read_k0 sp0 (p1 sp0 a0s path envv) mb gm sec cnr path fdata VM stdin0 fs0 tid Hfile R M _ RP Hlt).
        intros R' M' RQ.
        pose proof VS as VS'. destruct VS' as (VSr & VSl & VSn & VSin & VSsm & VSsep).
        apply (header_phase sp0 (p1 sp0 a0s path envv) gm tid sec cnr area brkv mas fdata VM stdin0 fs0 R M R' M'
                 Hvsp RQ W MF ltac:(lia) Hlt VSin).
        intros R'' M'' TP.
        exact (TPH (bv_unsigned sp0) (bv_unsigned gm) area brkv mas (bv_unsigned tid) (bv_unsigned sec) (bv_unsigned cnr)
                   fdata R'' M'' VM (model_post VM stdin0 fs0 tid) TP
                   (target_vm_of_small VM sp0 mb gm area Harea VP VS)
                   ltac:(constructor; reflexivity)).
      - (* [comment removed for export] *)
        assert (Hpage0 : forall i, (0 <= i < 0x1000)%Z -> M (Z_to_bv 64 i) = None).
        { intros i Hi. pose proof (w_img _ _ _ _ _ _ _ _ W) as Hw. unfold img_clear_ivs in Hw.
          apply Forall_cons_iff in Hw as [H0 _]. exact (H0 i Hi). }
        eapply rz_conseq; [ | apply (t_body_big fdata fs0); lia ].
        change (model_pre path VM stdin0 fs0 tid) with (modelG path stdin0 fs0 tid 0 VM).
        apply (read_big sp0 (p1 sp0 a0s path envv) mb gm sec cnr path fdata stdin0 fs0 tid Hfile R M VM
                 (t_body fdata fs0) (t_die msg_refused fs0) RP VP Hpage0 ltac:(lia)).
        + intros R' M' off V' RL.
          exact (refused_leaf_ok sp0 path stdin0 fs0 gm tid sec cnr area brkv mas M Hvsp W R' M' off V' RL).
        + intros k Hk HLk. unfold post_cont. intros R' M' V B e RPk.
          apply (header_phase_k k sp0 (p1 sp0 a0s path envv) mb gm B e tid sec cnr area brkv mas fdata M R' M' V stdin0 fs0
                   Hk Hvsp RPk W MF).
          * unfold capk. exact HLk.
          * intros R'' M'' TPk TVk.
            exact (TPKH k Hk (bv_unsigned sp0) (bv_unsigned B) area brkv mas (bv_unsigned tid) (bv_unsigned sec) (bv_unsigned cnr)
                        fdata R'' M'' V (model_post V stdin0 fs0 tid) TPk TVk ltac:(constructor; reflexivity)).
    Qed.

    Theorem ref_file_exists :
      open_err_branch sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 (t_die (msg_cannot_open path) fs0) ->
      realizes RSEGS (mkCfg (mkst regs0 (0x12ae8 : word) mem0 (seg_rom RSEGS))
                            (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputC [a0s; path] envv fs0 stdin0))))
               (t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened fdata fs0)).
    Proof using Hbrk Hfile Hpdd Hplen Hpnd Hpne Hpsl Htid Hva Hve Hvsp ME TPH TPKH.
      intros HCO.
      replace (0x12ae8 : word) with (Z_to_bv 64 0x12ae8) by (apply bv_eq; reflexivity).
      apply (oom_pilot sp0 a0s path envv tid rndb regs0 mem0 brk mbase fs0 stdin0 fdata
               Hva Hve Hvsp Htid ME Hbrk Hfile Hpne Hpnd Hplen Hpdd Hpsl).
      - exact HCO.
      - apply (brk_ok_sem sp0 a0s path envv tid rndb mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk Hplen).
        apply after_malloc_main.
    Qed.
  End FileExists.
End Driver.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Top.
  Hypothesis TPH : target_phase_stmt.
  Hypothesis TPKH : target_phase_k_stmt.

  (* [comment removed for export] *)
  Hypothesis H_usage : forall (AMB : Amb) (sp : word) (argv envp : list (list byte)) (tid : word) (rndb : EntryDraw)
      (regs : bvmap 5 word) (mem : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream),
    valid_argv argv -> valid_envp envp -> valid_sp sp -> (0 < bv_unsigned tid < 2 ^ 22)%Z -> entry_stack_fits sp argv envp ->
    main_entry sp argv envp tid rndb regs mem -> length argv <> 2%nat ->
    realizes RSEGS (mkCfg (mkst regs (0x12ae8 : word) mem (seg_rom RSEGS))
                          (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp LIM (mkProcInputC argv envp fs0 stdin0))))
             (t_die (msg_usage (hd [] argv)) fs0).
  (* [comment removed for export] *)
  Hypothesis H_toolong : forall (AMB : Amb) (sp : word) (a0s path : list byte) (envp : list (list byte)) (tid : word) (rndb : EntryDraw)
      (regs : bvmap 5 word) (mem : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream),
    valid_argv [a0s; path] -> valid_envp envp -> valid_sp sp -> (0 < bv_unsigned tid < 2 ^ 22)%Z -> entry_stack_fits sp [a0s; path] envp ->
    main_entry sp [a0s; path] envp tid rndb regs mem -> (4096 <= length path)%nat ->
    realizes RSEGS (mkCfg (mkst regs (0x12ae8 : word) mem (seg_rom RSEGS))
                          (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp LIM (mkProcInputC [a0s; path] envp fs0 stdin0))))
             (t_die (msg_cannot_open path) fs0).
  Hypothesis H_empty : forall (AMB : Amb) (sp : word) (a0s path : list byte) (envp : list (list byte)) (tid : word) (rndb : EntryDraw)
      (regs : bvmap 5 word) (mem : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream),
    valid_argv [a0s; path] -> valid_envp envp -> valid_sp sp -> (0 < bv_unsigned tid < 2 ^ 22)%Z -> entry_stack_fits sp [a0s; path] envp ->
    main_entry sp [a0s; path] envp tid rndb regs mem -> path = [] ->
    realizes RSEGS (mkCfg (mkst regs (0x12ae8 : word) mem (seg_rom RSEGS))
                          (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp LIM (mkProcInputC [a0s; path] envp fs0 stdin0))))
             (t_die (msg_cannot_open path) fs0).
  Hypothesis H_absent : forall (AMB : Amb) (sp : word) (a0s path : list byte) (envp : list (list byte)) (tid : word) (rndb : EntryDraw)
      (regs : bvmap 5 word) (mem : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream),
    valid_argv [a0s; path] -> valid_envp envp -> valid_sp sp -> (0 < bv_unsigned tid < 2 ^ 22)%Z -> entry_stack_fits sp [a0s; path] envp ->
    main_entry sp [a0s; path] envp tid rndb regs mem ->
    (length path <= 4095)%nat -> path <> [] -> path <> dot_path -> fs_lookup fs0 path = None ->
    realizes RSEGS (mkCfg (mkst regs (0x12ae8 : word) mem (seg_rom RSEGS))
                          (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp LIM (mkProcInputC [a0s; path] envp fs0 stdin0))))
             (t_die (msg_cannot_open path) fs0).
  (* [comment removed for export] *)
  Hypothesis H_cannot_open : forall (AMB : Amb) (sp : word) (a0s path : list byte) (envp : list (list byte)) (tid : word) (rndb : EntryDraw)
      (regs : bvmap 5 word) (mem : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream),
    valid_argv [a0s; path] -> valid_envp envp -> valid_sp sp -> entry_stack_fits sp [a0s; path] envp ->
    main_entry sp [a0s; path] envp tid rndb regs mem -> (length path <= 4095)%nat ->
    open_err_branch sp a0s path envp tid mem brk mbase fs0 stdin0 (t_die (msg_cannot_open path) fs0).
  (* [comment removed for export] *)
  Hypothesis H_dir_tail : forall (AMB : Amb) (sp0 : word) (a0s : list byte) (envv : list (list byte)) (tid : word)
      (rndb : EntryDraw) (regs0 : bvmap 5 word) (mem0 : word -> option byte),
    valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
    main_entry sp0 [a0s; dot_path] envv tid rndb regs0 mem0 ->
    forall (cnr : Z) (R : bvmap 5 word) (M : word -> option byte) (model : Model),
      m_halted model = None -> m_vm_lazy model = [] ->
      fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
      dir_tail_pre sp0 (p1 sp0 a0s dot_path envv) (bv_unsigned tid) cnr mem0 R M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12d14) M (seg_rom RSEGS)) model)
                 (t_die (msg_read_error dot_path) (m_fs model)).

  Theorem ref_main_phase_h : main_phase_stmt.
  Proof using H_absent H_cannot_open H_dir_tail H_empty H_toolong H_usage TPH TPKH.
    intros AMB sp brk mbase rnd argv envp fs0 stdin0 tid regs mem Hsp Hbrk Hfit Hva Hve Hfs Htid ME.
    change rsegs with RSEGS. change target_alloc_limit with LIM.
    destruct argv as [|a0s [|path [|x l]]].
    - apply (H_usage AMB sp [] envp tid rnd regs mem brk mbase fs0 stdin0 Hva Hve Hsp Htid Hfit ME). cbn; lia.
    - apply (H_usage AMB sp [a0s] envp tid rnd regs mem brk mbase fs0 stdin0 Hva Hve Hsp Htid Hfit ME). cbn; lia.
    - cbn [spec].
      destruct (Nat.leb_spec0 4096 (length path)) as [Hlong|Hshort].
      + apply (H_toolong AMB sp a0s path envp tid rnd regs mem brk mbase fs0 stdin0 Hva Hve Hsp Htid Hfit ME Hlong).
      + destruct (list_byte_eqb path []) eqn:Hemp.
        * apply ref_list_byte_eqb_eq in Hemp.
          apply (H_empty AMB sp a0s path envp tid rnd regs mem brk mbase fs0 stdin0 Hva Hve Hsp Htid Hfit ME Hemp).
        * assert (Hne : path <> []) by (intros E; apply ref_list_byte_eqb_eq in E; rewrite E in Hemp; discriminate).
          destruct (list_byte_eqb path dot_path) eqn:Hdot.
          -- apply ref_list_byte_eqb_eq in Hdot. rewrite Hdot in *.
             apply (ref_dir_path
                      (fun sp0 a0s envv tid rndb regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Hfit ME =>
                         H_cannot_open AMB sp0 a0s dot_path envv tid rndb regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Hfit ME ltac:(cbn; lia))
                      (H_dir_tail AMB)
                      sp a0s envp tid rnd regs mem brk mbase fs0 stdin0 Hva Hve Hsp Htid Hfit ME Hbrk).
          -- assert (Hnd : path <> dot_path)
               by (intros E; apply ref_list_byte_eqb_eq in E; rewrite E in Hdot; discriminate).
             destruct Hva as (VA1 & VA2 & VA3 & VA4 & VA5). pose proof VA5 as VA5'.
             cbn [tl] in VA5'. apply Forall_cons_iff in VA5' as [[Hpsl Hpdd0] _].
             assert (Hpdd : path <> dotdot_path)
               by (intros E; rewrite E in Hpdd0; rewrite path_eqb_refl in Hpdd0; discriminate).
             assert (Hva : valid_argv [a0s; path]) by exact (conj VA1 (conj VA2 (conj VA3 (conj VA4 VA5)))).
             destruct (fs_lookup fs0 path) as [data|] eqn:Hlk.
             ++ apply (ref_file_exists TPH TPKH sp a0s path envp tid rnd regs mem brk mbase fs0 stdin0 data
                         Hva Hve Hsp Htid ME Hbrk Hlk Hne Hnd ltac:(lia) Hpdd Hpsl).
                apply (H_cannot_open AMB sp a0s path envp tid rnd regs mem brk mbase fs0 stdin0 Hva Hve Hsp Hfit ME ltac:(lia)).
             ++ apply (H_absent AMB sp a0s path envp tid rnd regs mem brk mbase fs0 stdin0 Hva Hve Hsp Htid Hfit ME
                         ltac:(lia) Hne Hnd Hlk).
    - apply (H_usage AMB sp (a0s :: path :: x :: l) envp tid rnd regs mem brk mbase fs0 stdin0 Hva Hve Hsp Htid Hfit ME). cbn; lia.
  Qed.
End Top.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ref_main_phase : target_phase_stmt -> target_phase_k_stmt -> main_phase_stmt.
Proof.
  intros TPH TPKH.
  exact (ref_main_phase_h TPH TPKH
           (fun AMB sp argv envp tid rndb regs mem brk mbase fs0 stdin0 Hva Hve Hsp Htid Hfit ME Hargc =>
              @ref_usage_w _ AMB sp argv envp tid rndb regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Htid Hfit ME Hargc)
           ref_toolong_h ref_empty_h ref_absent_h ref_cannot_open_h dir_tail).
Qed.
