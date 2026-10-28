(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg
  MmapSim AllocSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX ExistsRun PhaseG
  Spec MallocDefs HUEnframeBase HUReadBase HUReadStage
  HUWorld HUTargetPre HUWorldK HUHeader_defs.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require HULeafHeader.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import ConeCfg.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sr_HK : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x331ae8; J 5; J 6; J 7;
   ELit 2; EVar 2; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 1; EVar 3; ELit 3; EVar 4; ELit 0x31ef09; ELit 0;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].

Definition kn_HK : list kentry :=
  [KRange (EVar 2) 0x354000 0x7fffff800000; KRange (EVar 3) 65536 67108863;
   KWord (SA (EVar 2) 0) 1 (EVar 6); KWord (SA (EVar 2) 1) 1 (EVar 7);
   KRange (EVar 6) 0 255; KRange (EVar 7) 0 255].

Definition hkK := Eval vm_compute in runh scr_fall (SS 0xe1aa0 sr_HK [] kn_HK NXh).

Lemma hdrk_itinerary_ok :
  s_pc (fst (fst hkK)) = 0xe1c8c%Z /\ s_log (fst (fst hkK)) = [] /\ s_next (fst (fst hkK)) = 47%nat
  /\ nth 11 (s_regs (fst (fst hkK))) (ELit 0) = cfglen_x.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition off_image (x : Z) : Prop := (x + 1 <= 0x10000 \/ 0x354000 <= x)%Z.

Lemma find_segment_skip : forall seg rest a n,
  (0 < n)%Z ->
  (a < Z.of_N (seg_base seg) \/ Z.of_N (seg_base seg) + Z.of_N (seg_size seg) < a + n)%Z ->
  find_segment (seg :: rest) a n = find_segment rest a n.
Proof.
  intros seg rest a n Hn H. cbn [find_segment].
  destruct (Z.leb_spec (Z.of_N (seg_base seg)) a); destruct (Z.leb_spec (a + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)));
    cbn [andb]; try reflexivity. lia.
Qed.

Lemma find_segment_off : forall a n, (0 < n)%Z -> (a + n <= 0x10000 \/ 0x354000 <= a)%Z ->
  find_segment RSEGS a n = None.
Proof.
  intros a n Hn H. unfold M.loaded_segments, Ubsan_loaded_segments.
  rewrite 4 find_segment_skip; [reflexivity | exact Hn | | exact Hn | | exact Hn | | exact Hn |];
    cbn [seg_base seg_size Ubsan_segment_000 Ubsan_segment_001 Ubsan_segment_002 Ubsan_segment_003]; lia.
Qed.

Lemma seg_rom_off : forall x : word, off_image (bv_unsigned x) -> seg_rom RSEGS x = None.
Proof.
  intros x Hx. unfold seg_rom, memory_read. rewrite find_segment_off; [reflexivity | cbn; lia | unfold off_image in Hx; cbn; lia].
Qed.

Lemma store_ok1_off : forall M (x : word), off_image (bv_unsigned x) ->
  store_ok RSEGS M x 1 = true -> M x <> None.
Proof.
  intros M x Hx H. cbn [store_ok] in H. unfold wview in H.
  destruct (M x); [discriminate|]. rewrite find_segment_off in H; [discriminate | lia | unfold off_image in Hx; lia].
Qed.

(* [comment removed for export] *)
Lemma byte_of_cell : forall M a v,
  (0 <= a < 2 ^ 64)%Z -> off_image a -> (0 <= v < 256)%Z ->
  cell M a 1 v -> M (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Proof.
  intros M a v Ha Hoff Hv C. unfold cell in C. cbn [rdn] in C.
  rewrite (seg_rom_off (Z_to_bv 64 a)) in C by (rewrite u64_lit by lia; exact Hoff).
  destruct (M (Z_to_bv 64 a)) as [b|]; [|discriminate].
  unfold word_to_le_bytes in C. cbn [Z_to_le_bytes] in C. rewrite u64_lit in C by lia.
  injection C as ->. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma defined_of_wr : forall M (base n : Z),
  (0 <= base)%Z -> (base + n <= 2 ^ 64)%Z -> (base + n <= 0x10000 \/ 0x354000 <= base)%Z ->
  (forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= n)%Z -> store_ok RSEGS M (Z_to_bv 64 (base + d)) m = true) ->
  forall i, (0 <= i < n)%Z -> M (Z_to_bv 64 (base + i)) <> None.
Proof.
  intros M base n Hb Hn Hoff W i Hi. apply store_ok1_off.
  - rewrite u64_lit by lia. unfold off_image. lia.
  - apply (W i 1%nat); cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cell_ofw : forall M A n (w : word) A' V',
  rdn RSEGS M (Z_to_bv 64 A) n = Some (word_to_le_bytes n w) ->
  A = A' -> w = Z_to_bv 64 V' -> cell M A' n V'.
Proof. intros M A n w A' V' H <- ->. exact H. Qed.

Lemma w2le_8_inj : forall (v w : word), word_to_le_bytes 8 v = word_to_le_bytes 8 w -> v = w.
Proof.
  intros v w H. apply bv_eq. rewrite <- (bytes_le_to_Z_8 v), <- (bytes_le_to_Z_8 w). rewrite H. reflexivity.
Qed.

Lemma w2le_4_mod : forall (e : word),
  word_to_le_bytes 4 e = word_to_le_bytes 4 (Z_to_bv 64 (bv_unsigned e mod 2 ^ 32)).
Proof.
  intros e. unfold word_to_le_bytes. pose proof (Z.mod_pos_bound (bv_unsigned e) (2 ^ 32) ltac:(lia)).
  rewrite (u64_lit (bv_unsigned e mod 2 ^ 32)) by lia.
  symmetry. exact (Z_to_le_bytes_mod 4 (bv_unsigned e)).
Qed.

Lemma w2le1_byte_k : forall (x : byte), word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned x)) = [x].
Proof.
  intros x. pose proof (bv_unsigned_in_range _ x) as Hx. change (bv_modulus 8) with 256%Z in Hx.
  unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal.
  rewrite u_small by lia. apply Z_to_bv_bv_unsigned.
Qed.

Lemma live_bytes_cons : forall (a n : word) r, live_bytes ((a, n) :: r) = (bv_unsigned n + live_bytes r)%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pres_cell : forall M0 M sp0 a n v,
  pres M0 M sp0 -> (0x10000 <= a)%Z -> (a + Z.of_nat n <= 0x354000)%Z ->
  (forall i, (a <= i < a + Z.of_nat n)%Z -> ~ rd_cell i) ->
  cell M0 a n v -> cell M a n v.
Proof.
  intros M0 M sp0 a n v P Ha Hn Hrd C. unfold cell in *. rewrite <- C.
  apply rdn_agree. intros j Hj. rewrite (u_small a) by lia. apply P. left. rewrite u_small by lia.
  split; [lia|]. apply Hrd. lia.
Qed.

Lemma pres_img_clear : forall M0 M sp0 lo hi,
  pres M0 M sp0 -> (0x10000 <= lo)%Z -> (hi <= 0x354000)%Z ->
  (forall i, (lo <= i < hi)%Z -> ~ rd_cell i) ->
  img_clear M0 lo hi -> img_clear M lo hi.
Proof.
  intros M0 M sp0 lo hi P Hlo Hhi Hrd C i Hi. rewrite (P (Z_to_bv 64 i)); [apply C; exact Hi|].
  left. rewrite u_small by lia. split; [lia|]. apply Hrd. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma curslot_eq : forall k, (0 <= k)%Z -> (curslot k = 4120 + 40 * (k mod 2))%Z.
Proof.
  intros k Hk. unfold curslot. rewrite Zodd_mod. pose proof (Z.mod_pos_bound k 2 ltac:(lia)).
  destruct (Z.eq_dec (k mod 2) 1) as [E|E]; [rewrite E; reflexivity|].
  replace (k mod 2)%Z with 0%Z by lia. reflexivity.
Qed.

Lemma freeslot_eq : forall k, (0 <= k)%Z -> (freeslot k = 4160 - 40 * (k mod 2))%Z.
Proof.
  intros k Hk. unfold freeslot. rewrite Zodd_mod. pose proof (Z.mod_pos_bound k 2 ltac:(lia)).
  destruct (Z.eq_dec (k mod 2) 1) as [E|E]; [rewrite E; reflexivity|].
  replace (k mod 2)%Z with 0%Z by lia. reflexivity.
Qed.

Section KnowFacts.
  Variables (E : env) (M : word -> option byte) (kn : list kentry).
  Hypothesis HK : know_ok RSEGS E M kn.

  Lemma kf_word : forall b o n v, In (KWord (SA b o) n v) kn ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned (edenot E b) + o)) n = Some (word_to_le_bytes n (edenot E v)).
  Proof.
    intros b o n v Hin. pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X.
    destruct X as (_ & _ & X). exact X.
  Qed.

  Lemma kf_zero : forall b o len, In (KZero (SA b o) len) kn ->
    zero_bytes M (bv_unsigned (edenot E b) + o) (bv_unsigned (edenot E len)).
  Proof.
    intros b o len Hin. pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X.
    destruct X as (_ & X). unfold estart, elenZ in X. cbn [a_base a_off] in X. exact X.
  Qed.

  Lemma kf_img : forall lo hi, In (KImg lo hi) kn -> img_clear M lo hi.
  Proof.
    intros lo hi Hin. pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X.
    destruct X as (_ & _ & X). exact X.
  Qed.

  Lemma kf_range : forall x lo hi, In (KRange x lo hi) kn -> (lo <= bv_unsigned (edenot E x) <= hi)%Z.
  Proof.
    intros x lo hi Hin. pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X. lia.
  Qed.

  Lemma kf_align : forall x m, In (KAlign x m) kn -> (bv_unsigned (edenot E x) mod m = 0)%Z.
  Proof.
    intros x m Hin. pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X. lia.
  Qed.

  Lemma kf_wr : forall b o n, In (KWr (SA b o) n) kn ->
    forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= n)%Z ->
      store_ok RSEGS M (Z_to_bv 64 (bv_unsigned (edenot E b) + o + d)) m = true.
  Proof.
    intros b o n Hin. pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X.
    destruct X as (_ & X). unfold estart in X. cbn [a_base a_off] in X. exact X.
  Qed.

  Lemma kf_disj : forall b1 o1 n1 b2 o2 n2, In (KDisj (SA b1 o1) n1 (SA b2 o2) n2) kn ->
    (bv_unsigned (edenot E b1) + o1 + n1 <= bv_unsigned (edenot E b2) + o2
     \/ bv_unsigned (edenot E b2) + o2 + n2 <= bv_unsigned (edenot E b1) + o1)%Z.
  Proof.
    intros b1 o1 n1 b2 o2 n2 Hin. pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X.
    unfold estart in X. cbn [a_base a_off] in X. exact X.
  Qed.
End KnowFacts.

(* [comment removed for export] *)
Ltac kin :=
  unfold kn_POST, kn_static, kn_ctx, kn_meta; cbn [app In];
  repeat (first [ left; reflexivity | right ]);
  lazymatch goal with |- False => fail "kin: entry not found" | |- _ => idtac end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition t_hdr := HULeafHeader.H0Header.t_hdr.

Section HeaderK.
  Variables (k : Z) (sp0 p1 mb bw gm B e can sec tid : word) (area brkv mas : Z) (content : list byte).
  Variables (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps).
  Variables (stdin0 : AmbIn) (fs0 : Fs).
  Hypothesis Hk : (1 <= k <= 10)%Z.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis RP : read_post k sp0 p1 mb bw gm B e can sec content M0 R M VM.
  Hypothesis W0 : world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas (bv_unsigned tid)
                         (bv_unsigned can) (bv_unsigned sec) M0.
  Hypothesis HL : (capk (k - 1) <= Z.of_nat (length content) < capk k)%Z.
  Hypothesis MF : main_frame (bv_unsigned sp0) M0.   (* [comment removed for export] *)

  Let L : Z := Z.of_nat (length content).

  (* [comment removed for export] *)
  Definition EK (extra : list word) : env := ENV_RD sp0 p1 mb bw gm L B e can sec extra content.

  Lemma ek0 : forall extra, ev (EK extra) 0 = sp0. Proof. reflexivity. Qed.
  Lemma ek2 : forall extra, ev (EK extra) 2 = mb. Proof. reflexivity. Qed.
  Lemma ek5 : forall extra, ev (EK extra) 5 = B. Proof. reflexivity. Qed.
  Lemma ek6 : forall extra, ev (EK extra) 6 = e. Proof. reflexivity. Qed.
  Lemma ek7 : forall extra, ev (EK extra) 7 = can. Proof. reflexivity. Qed.
  Lemma ek8 : forall extra, ev (EK extra) 8 = sec. Proof. reflexivity. Qed.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac get_know extra Hlen HK :=
    destruct (rk_know _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as (extra & Hlen & HK);
    change (ENV_RD sp0 p1 mb bw gm (Z.of_nat (length content)) B e can sec extra content) with (EK extra) in HK.

  Ltac kclean X :=
    unfold LA, BA, mbx in X; rewrite ?edenot_add_lit in X; unfold adenot, v_addi in X; cbn [a_base a_off edenot] in X;
    rewrite ?ek0, ?ek2, ?ek5, ?ek6, ?ek7, ?ek8 in X;
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in X; rewrite ?Z.add_0_l in X.

  Lemma capk_split : capk k = (capk (k - 1) + capk (k - 1))%Z.
  Proof.
    unfold capk. replace k with (k - 1 + 1)%Z at 1 by lia. rewrite Z.pow_add_r by lia. lia.
  Qed.

  Lemma hk_nums : (65536 <= capk (k - 1))%Z /\ (capk k <= 67108864)%Z /\ (65536 <= L < 67108864)%Z
                  /\ nb_of k = nbk k /\ cap_of k = capk k /\ off_of k = offk k /\ res_of k = resk k.
  Proof.
    pose proof (capk_pos (k - 1) ltac:(lia)). pose proof (capk_le k ltac:(lia)). unfold L. repeat split; try lia; reflexivity.
  Qed.

  Lemma sp0_facts : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z /\ (bv_unsigned sp0 mod 16 = 0)%Z.
  Proof. destruct Hvsp as (A & B_ & C). unfold sp_window_lo, sp_window_hi in *. lia. Qed.

  (* [comment removed for export] *)
  Lemma buf_facts : (bv_unsigned B mod 4096 = 0)%Z /\ (0x354000 <= bv_unsigned B)%Z
                    /\ (bv_unsigned B + nbk k <= bv_unsigned sp0 - 8388608)%Z.
  Proof.
    get_know extra Hlen HK. pose proof hk_nums as (Hc1 & Hc2 & HLr & Enb & Ecap & Eoff & _). pose proof sp0_facts as [SP _].
    pose proof (kf_align _ _ _ HK (EVar 5) 4096 ltac:(kin)) as AL. cbn [edenot] in AL. rewrite ek5 in AL.
    pose proof (kf_range _ _ _ HK (EVar 5) 0x354000 (CEIL - nb_of k) ltac:(kin)) as RB. cbn [edenot] in RB. rewrite ek5 in RB.
    pose proof (kf_disj _ _ _ HK (EVar 0) (-8388608) HUGE (EVar 5) 0 (nb_of k) ltac:(kin)) as DJ. cbn [edenot] in DJ.
    rewrite ek0, ek5 in DJ. unfold HUGE in DJ. pose proof (u64_range B). rewrite Enb in *. lia.
  Qed.

  Lemma stack_k : stack_writable M sp0.
  Proof.
    get_know extra Hlen HK.
    pose proof (kf_wr _ _ _ HK (EVar 0) (-8388608) 8388608 ltac:(kin)) as W. kclean W.
    intros d m Hd Hm. replace (bv_unsigned sp0 - 8388608 + d)%Z with (bv_unsigned sp0 + -8388608 + d)%Z by lia.
    apply W; assumption.
  Qed.

  Lemma canary_k : cell M 0x351b28 8 (bv_unsigned can).
  Proof.
    get_know extra Hlen HK.
    pose proof (kf_word _ _ _ HK (ELit 0) 0x351b28 8 (EVar 7) ltac:(kin)) as W. kclean W.
    unfold cell. rewrite Z_to_bv_bv_unsigned. exact W.
  Qed.

  (* [comment removed for export] *)
  Lemma img_low_k : forall i, (0x10000 <= i < 0x31eec0)%Z -> M (Z_to_bv 64 i) = None.
  Proof.
    intros i Hi. pose proof (rk_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as P.
    (* [comment removed for export] *)
    pose proof (proj1 (Forall_forall _ _) (w_img _ _ _ _ _ _ _ _ _ W0) (0x10000, 0x31eec0)%Z ltac:(cbn; tauto)) as C.
    rewrite (P (Z_to_bv 64 i)); [apply C; cbn; lia|].
    left. rewrite u_small by lia. split; [lia|]. unfold rd_cell. lia.
  Qed.

  Lemma init0_k : M (Z_to_bv 64 0x32ef10) = None.
  Proof.
    pose proof (rk_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as P.
    pose proof (proj1 (Forall_forall _ _) (w_img _ _ _ _ _ _ _ _ _ W0) (0x32ef09, 0x331a18)%Z ltac:(cbn; tauto)) as C.   (* [comment removed for export] *)
    rewrite (P (Z_to_bv 64 0x32ef10)); [apply C; cbn; lia|].
    left. rewrite u_small by lia. split; [lia|]. unfold rd_cell. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma area_eq : area = (bv_unsigned mb + 4096)%Z.
  Proof.
    get_know extra Hlen HK.
    pose proof (rk_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as P.
    pose proof (kf_word _ _ _ HK (ELit 0) 0x351e28 8 (mbx 4096) ltac:(kin)) as X. kclean X.
    pose proof (kf_range _ _ _ HK (EVar 2) 0x1000 (CEIL - 8192) ltac:(kin)) as Rmb. cbn [edenot] in Rmb. rewrite ek2 in Rmb.
    unfold CEIL in Rmb.
    pose proof (w_mah _ _ _ _ _ _ _ _ _ W0) as C0. unfold ctx_meta_area_head, CTX in C0.
    pose proof (w_area_rng _ _ _ _ _ _ _ _ _ W0) as Ar. pose proof (w_sp0 _ _ _ _ _ _ _ _ _ W0) as Wsp.
    assert (C : cell M (0x351df0 + 56) 8 area).
    { eapply pres_cell; [exact P | lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact C0]. }
    unfold cell in C. replace (0x351df0 + 56)%Z with 0x351e28%Z in C by reflexivity. rewrite X in C.
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

  Lemma world_k_intro :
    world_k (bv_unsigned sp0) k area (bv_unsigned B) brkv mas (bv_unsigned tid) (bv_unsigned can) (bv_unsigned sec) M.
  Proof.
    get_know extra Hlen HK. pose proof (rk_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as P. pose proof area_eq as AE.
    pose proof hk_nums as (Hc1 & Hc2 & HLr & _). pose proof sp0_facts as [SPF _]. pose proof buf_facts as (BF1 & BF2 & BF3).
    pose proof (u64_range mb) as Umb. pose proof (u64_range B) as UB. pose proof (u64_range e) as Ue.
    pose proof (u64_range can) as Ucan. pose proof (u64_range sec) as Usec.
    destruct W0 as [Wsec Winit Wctr Wfmh Wam Wamc Wamac Wmas Wmah Wmat Wamas Wactive44 Wusage44 Wseq Wbrk
                    Wachk Wanext Wans Wsprev Wsnext Wsmem Wsmsk WsW Warest Wadef Wgmeta Wgaidx Wgpad Wenf Wgtail Wgdef
                    Waal Wgmal Wsp0 Warng Waimg Wgmrng Wdisj Wbrkv Wmasv Wtid Wtidr Werrno Wself Wcanary Wpagesz Wimg Wworld].
    (* [comment removed for export] *)
    pose proof (kf_range _ _ _ HK (EVar 2) 0x1000 (CEIL - 8192) ltac:(kin)) as Rmb. cbn [edenot] in Rmb. rewrite ek2 in Rmb.
    pose proof (kf_align _ _ _ HK (EVar 2) 4096 ltac:(kin)) as Amb. cbn [edenot] in Amb. rewrite ek2 in Amb.
    pose proof (kf_disj _ _ _ HK (EVar 5) 0 (nb_of k) (EVar 2) 4096 4096 ltac:(kin)) as DB. kclean DB.
    pose proof (kf_wr _ _ _ HK (EVar 2) 4096 4096 ltac:(kin)) as Wmb. kclean Wmb.
    pose proof (kf_wr _ _ _ HK (EVar 5) 0 (nb_of k) ltac:(kin)) as WB. kclean WB.
    pose proof (kf_zero _ _ _ HK (EVar 2) 4200 (ELit 3992) ltac:(kin)) as Zarea. kclean Zarea.
    pose proof (kf_zero _ _ _ HK (EVar 5) 8 (ELit 5) ltac:(kin)) as Zhdr. kclean Zhdr.
    pose proof (kf_zero _ _ _ HK (EVar 5) (nb_of k - 4) (ELit 4) ltac:(kin)) as Ztail. kclean Ztail.
    change (bv_unsigned (Z_to_bv 64 3992)) with 3992%Z in Zarea.
    change (bv_unsigned (Z_to_bv 64 5)) with 5%Z in Zhdr.
    change (bv_unsigned (Z_to_bv 64 4)) with 4%Z in Ztail.
    unfold CEIL, nb_of, cap_of in *. unfold nbk, capk in BF3, Hc2.
    constructor.
    all: unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta, ctx_avail_meta_count,
      ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta_areas,
      ctx_active, ctx_usage, ctx_seq, ctx_brk, CTX in *.
    all: unfold slotC, slotF, nbk, capk, offk, Wk, resk.
    - exact Hk.
    - kcell HK (ELit 0) 0x351df0%Z 8%nat (EVar 8).
    - kcell HK (ELit 0) 0x351df8%Z 4%nat (ELit 1).
    - kcell HK (ELit 0) 0x351dfc%Z 4%nat (ELit (1 + k)).
    - kcell HK (ELit 0) 0x351e00%Z 8%nat (mbx (freeslot k)).
    - kcell HK (ELit 0) 0x351e08%Z 8%nat (mbx 4200).
    - kcell HK (ELit 0) 0x351e10%Z 8%nat (ELit 99).
    - kcell HK (ELit 0) 0x351e18%Z 8%nat (ELit 0).
    - (* [comment removed for export] *)
      eapply pres_cell; [exact P | lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact Wmas].
    - kcell HK (ELit 0) 0x351e28%Z 8%nat (mbx 4096).
    - kcell HK (ELit 0) 0x351e30%Z 8%nat (mbx 4096).
    - kcell HK (ELit 0) 0x351e38%Z 8%nat (mbx 8192).
    - kcell HK (ELit 0) 0x351fa0%Z 8%nat (ELit 0).
    - kcell HK (ELit 0) 0x352120%Z 8%nat (ELit 0).
    - kcell HK (ELit 0) 0x352180%Z 1%nat (ELit (1 + 2 * k)).
    - eapply pres_cell; [exact P | lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact Wbrk].
    - kcell HK (EVar 2) 4096%Z 8%nat (EVar 8).
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
    - exact BF1.
    - exact SPF.
    - exact Warng.
    - exact Waimg.
    - unfold nbk, capk in BF3. lia.
    - lia.
    - exact Wbrkv.
    - exact Wmasv.
    - eapply pres_cell; [exact P | lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact Wtid].
    - exact Wtidr.
    - pose proof (kf_word _ _ _ HK (ELit 0) 0x331a44%Z 4%nat (EVar 6) ltac:(kin)) as X. kclean X.
      pose proof (Z.mod_pos_bound (bv_unsigned e) (2 ^ 32) ltac:(lia)).
      exists (bv_unsigned e mod 2 ^ 32)%Z. split; [lia|]. unfold cell. rewrite X. f_equal. apply w2le_4_mod.
    - eapply pres_cell; [exact P | lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact Wself].
    - exact canary_k.
    - eapply pres_cell; [exact P | lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact Wpagesz].
    - (* [comment removed for export] *)
      unfold img_clear_ivs in *. apply Forall_cons_iff in Wimg as [_ Wimg].
      apply Forall_cons; [exact (kf_img _ _ _ HK 0 0x1000 ltac:(kin))|].
      repeat (apply Forall_cons_iff in Wimg as [?C Wimg]).
      repeat (apply Forall_cons; [eapply pres_img_clear; [exact P | cbn; lia | cbn; lia | unfold rd_cell; cbn; intros; lia | assumption] |]).
      apply Forall_nil.
    - exact Wworld.
  Qed.

  Lemma main_frame_k : main_frame (bv_unsigned sp0) M.
  Proof.
    pose proof (rk_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as P. pose proof sp0_facts as [SP _].
    eapply main_frame_frame; [lia | lia | | | | exact MF].
    - intros i Hi. apply P. right. rewrite u_small by lia. lia.
    - (* [comment removed for export] *) apply P. left. rewrite u_small by lia. split; [lia | unfold rd_cell; lia].
    - (* [comment removed for export] *) intros i Hi. apply P. right. rewrite u_small by lia. lia.
  Qed.

  Definition modelk : Model := model_post VM stdin0 fs0 tid.

  Definition valsk : list word :=
    [sp0; p1; Z_to_bv 64 (bv_unsigned B + offk k); Z_to_bv 64 L; Z_to_bv 64 (capk k); tid;
     Z_to_bv 64 (hdr_b0 content); Z_to_bv 64 (hdr_b1 content); Z_to_bv 64 0; can; sec] ++ junk_vals R.

  Lemma content_byte_k : forall j, (j < length content)%nat ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned B + offk k + Z.of_nat j)) 1%nat
    = Some (word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned (nth j content (Z_to_bv 8 0))))).
  Proof.
    intros j Hj. pose proof (rk_content _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as Hcont.
    pose proof hk_nums as (Hc1 & Hc2 & HLr & Enb & Ecap & Eoff & _). rewrite Eoff in Hcont.
    pose proof buf_facts as (_ & RB & RB2). pose proof sp0_facts as [SP _]. unfold nbk, offk in *.
    pose proof (rdn_nth RSEGS M (length content) _ content j Hcont Hj) as H.
    rewrite w_add_nat in H. rewrite u_small in H by lia. rewrite w2le1_byte_k. exact H.
  Qed.

  Lemma hdrk_sym : regs_ok (ENVh content valsk) sr_HK R /\ know_ok RSEGS (ENVh content valsk) M kn_HK.
  Proof.
    pose proof hk_nums as (Hc1 & Hc2 & HLr & Enb & Ecap & Eoff & _).
    pose proof buf_facts as (_ & RB & RB2). pose proof sp0_facts as [SP _].
    destruct RP as [Rsp Rgp Rtp Rs0 Rs1 Rs2 Rs3 Rs4 Rs5 Rs6 Rs7 Hcont P HKx Hvm].
    set (E := ENVh content valsk).
    assert (E0 : ev E 0 = sp0) by reflexivity.
    assert (E1 : ev E 1 = p1) by reflexivity.
    assert (E2 : ev E 2 = Z_to_bv 64 (bv_unsigned B + offk k)) by reflexivity.
    assert (E3 : ev E 3 = Z_to_bv 64 L) by reflexivity.
    assert (E4 : ev E 4 = Z_to_bv 64 (capk k)) by reflexivity.
    assert (E6 : ev E 6 = Z_to_bv 64 (hdr_b0 content)) by reflexivity.
    assert (E7 : ev E 7 = Z_to_bv 64 (hdr_b1 content)) by reflexivity.
    assert (EJ : forall i, (i < 32)%nat -> ev E (11 + i) = getr R (Z_to_bv 5 (Z.of_nat i))).
    { intros i Hi. unfold E, ENVh, valsk. cbn [ev]. unfold vals_ev.
      change (11 + i)%nat with (length [sp0; p1; Z_to_bv 64 (bv_unsigned B + offk k); Z_to_bv 64 L; Z_to_bv 64 (capk k); tid;
                                        Z_to_bv 64 (hdr_b0 content); Z_to_bv 64 (hdr_b1 content); Z_to_bv 64 0; can; sec] + i)%nat.
      rewrite app_nth2_plus. unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi.
      reflexivity. }
    split.
    - apply HUReadBase.regs_ok_by_index. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
        cbn [nth sr_HK HUReadBase.all_regs].
      all: try (lazymatch goal with |- _ = edenot _ (J ?n) =>
                  unfold J; change (edenot E (EVar (11 + n))) with (ev E (11 + n)%nat); rewrite EJ by lia; reflexivity end).
      all: try (lazymatch goal with |- _ = edenot _ (spx ?z) =>
                  unfold spx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot]; rewrite E0;
                  rewrite Rsp; f_equal; lia end).
      all: try (change (edenot E (EVar 1)) with (ev E 1); rewrite E1; assumption).
      all: try (change (edenot E (EVar 2)) with (ev E 2); rewrite E2; rewrite <- Eoff; assumption).
      all: try (change (edenot E (EVar 3)) with (ev E 3); rewrite E3; assumption).
      all: try (change (edenot E (EVar 4)) with (ev E 4); rewrite E4; rewrite <- Ecap; assumption).
      all: cbn [edenot]; first [assumption | apply getr_zero | reflexivity].
    - pose proof (bv_unsigned_in_range _ (nth 0 content (Z_to_bv 8 0))) as B0.
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

  Theorem header_ok_k : forall (mode : bool) (Q : config -> Prop) K,
    (* [comment removed for export] *)
    (forall R', tgt_entry (bv_unsigned sp0) (bv_unsigned B + offk k) (bv_unsigned can) content R' M ->
       GG RSEGS mode Q K (mkCfg (mkst R' (Z_to_bv 64 0xe1c8c) M (seg_rom RSEGS)) modelk)) ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1aa0) M (seg_rom RSEGS)) modelk).
  Proof.
    intros mode Q K HK_T. destruct hdrk_sym as [HR HK].
    pose proof (hdr_cfglen_range content) as CR.
    pose proof hk_nums as (Hc1 & Hc2 & HLr & Enb & Ecap & Eoff & _).
    pose proof sp0_facts as [SP SPA].
    pose proof (u64_range B) as UB. pose proof (u64_range can) as UC.
    pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1. change (bv_modulus 8) with 256%Z in B1.
    pose proof buf_facts as (BAL & RB1 & RB). unfold nbk in RB.
    pose proof capk_split as CS. unfold L in HLr.
    set (cb := fun i : nat => Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (hdr_cfglen content) + 2 + i) content (Z_to_bv 8 0)))).
    assert (HL0 : length valsk = 43%nat) by (unfold valsk; rewrite length_app, junk_vals_length; reflexivity).
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
    assert (PB41 : vals_ev vals 43 = cb 1%nat).
    { unfold vals. replace 43%nat with (length valsk + 0)%nat by (rewrite HL0; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (PB42 : vals_ev vals 44 = cb 0%nat).
    { unfold vals. replace 44%nat with (length valsk + 1)%nat by (rewrite HL0; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (PB43 : vals_ev vals 45 = cb 2%nat).
    { unfold vals. replace 45%nat with (length valsk + 2)%nat by (rewrite HL0; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (PB44 : vals_ev vals 46 = cb 3%nat).
    { unfold vals. replace 46%nat with (length valsk + 3)%nat by (rewrite HL0; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    clearbody vals.
    pose proof (cfglen_val content vals P6 P7) as CV.
    unfold offk in P2.
    assert (CB : forall i, (i < 4)%nat ->
      rdn RSEGS M (Z_to_bv 64 (bv_unsigned B + 16 * (k + 2) + hdr_cfglen content + 2 + Z.of_nat i)) 1%nat
      = Some [nth (Z.to_nat (hdr_cfglen content) + 2 + i) content (Z_to_bv 8 0)]).
    { intros i Hi.
      replace (bv_unsigned B + 16 * (k + 2) + hdr_cfglen content + 2 + Z.of_nat i)%Z
        with (bv_unsigned B + offk k + Z.of_nat (Z.to_nat (hdr_cfglen content) + 2 + i))%Z by (unfold offk; lia).
      rewrite content_byte_k by lia. rewrite w2le1_byte_k. reflexivity. }
    (* [comment removed for export] *)
    gg_block_gen FUELh STOPSh scr_fall 43%nat true.
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
    lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst _ _ ?Mx _) _) =>
      lazymatch goal with EQ : Mx = _ |- _ => cbn [mem_denot] in EQ; subst Mx end end.
    apply HK_T.
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
    - unfold L in *. lia.
    - unfold offk. split; [|split]; [ | lia | unfold L in *; lia].
      apply (proj1 (Z.mod_divide (bv_unsigned B) 4096 ltac:(lia))) in BAL. destruct BAL as [q Hq]. rewrite Hq.
      replace (q * 4096 + 16 * (k + 2))%Z with ((q * 256 + (k + 2)) * 16)%Z by lia. apply Z_mod_mult.
    - lia.
    - pose proof stack_k as ST. intros d m Hd Hm. apply ST; assumption.
    - exact img_low_k.
    - exact init0_k.
    - exact canary_k.
    - pose proof (rk_content _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as Hcont. rewrite Eoff in Hcont. exact Hcont.
  Qed.

  (* [comment removed for export] *)
  Theorem header_phase_k_sec : forall (mode : bool) (Q : config -> Prop) K,
    (* [comment removed for export] *)
    (forall R', tgt_entry (bv_unsigned sp0) (bv_unsigned B + offk k) (bv_unsigned can) content R' M ->
       GG RSEGS mode Q K (mkCfg (mkst R' (Z_to_bv 64 0xe1c8c) M (seg_rom RSEGS)) modelk)) ->
    GG RSEGS mode Q (t_hdr content fs0 K) (mkCfg (mkst R (Z_to_bv 64 0xe1aa0) M (seg_rom RSEGS)) modelk).
  Proof.
    intros mode Q K HT. pose proof hk_nums as (Hc1 & Hc2 & HLr & _). pose proof (hdr_cfglen_range content) as CR.
    unfold t_hdr, HULeafHeader.H0Header.t_hdr. rewrite HULeafHeader.H0Header.config_len_hdr. unfold HDR_MIN, MAX_INPUT.
    replace (67108864 <=? Z.of_nat (length content))%Z with false by (symmetry; apply Z.leb_gt; unfold L in *; lia).
    replace (length content <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; unfold L in *; lia).
    replace (length content <? 6 + Z.to_nat (hdr_cfglen content))%nat with false by (symmetry; apply Nat.ltb_ge; unfold L in *; lia).
    apply header_ok_k. exact HT.
  Qed.
End HeaderK.

Theorem header_phase_k : forall (mode : bool) (Q : config -> Prop) (k : Z) (sp0 p1 mb bw gm B e can sec tid : word)
    (area brkv mas : Z) (content : list byte)
    (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (stdin0 : AmbIn) (fs0 : Fs) K,
  (1 <= k <= 10)%Z -> valid_sp sp0 ->
  read_post k sp0 p1 mb bw gm B e can sec content M0 R M VM ->
  world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned can) (bv_unsigned sec) M0 ->
  (capk (k - 1) <= Z.of_nat (length content) < capk k)%Z ->
  (forall R', tgt_entry (bv_unsigned sp0) (bv_unsigned B + offk k) (bv_unsigned can) content R' M ->
     GG RSEGS mode Q K (mkCfg (mkst R' (Z_to_bv 64 0xe1c8c) M (seg_rom RSEGS)) (model_post VM stdin0 fs0 tid))) ->
  GG RSEGS mode Q (t_hdr content fs0 K) (mkCfg (mkst R (Z_to_bv 64 0xe1aa0) M (seg_rom RSEGS)) (model_post VM stdin0 fs0 tid)).
Proof.
  intros. eapply header_phase_k_sec; eassumption.
Qed.
