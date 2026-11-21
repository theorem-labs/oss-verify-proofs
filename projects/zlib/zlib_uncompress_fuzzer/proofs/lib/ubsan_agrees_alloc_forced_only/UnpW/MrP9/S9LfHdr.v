(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import WsegFast PropExec CatExec CatSim SeqExec StoreOk Frame StreamSim ShapeAlg Nodes AgentLib SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux RefMemcpyLib RefNodes Hoare. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import S9ExitBase S9StdioDefs S9StdioWrite S9LibStdioCall S9ReadBase S9TargetPre S9Header_defs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Spec.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MrP9 Require Import S9SoDefs S9PrintfFirst.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hd_regions (sp0 : Z) : list (word * Z) :=
  [(Z_to_bv 64 (sp0 - 512), 384); (Z_to_bv 64 0x22c70, 232)].

(* [comment removed for export] *)
Definition hd_kept : list reg := [2; 3; 4; 8; 9]%bv.

Record hd_pre {RCa1 : RunCtx}  (sp0 buf : Z) (content : list byte) (can : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop := HD_PRE {
  hd_sp    : getr R 2 = Z_to_bv 64 (sp0 - 128);
  hd_s1    : getr R 9 = Z_to_bv 64 buf;
  hd_s3    : getr R 19 = Z_to_bv 64 (Z.of_nat (length content));
  hd_sp0   : 0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0;
  hd_buf   : 0x94000 <= buf /\ buf + Z.of_nat (length content) <= 0x7fffff800000;
  hd_L     : Z.of_nat (length content) < 2 ^ 26;
  hd_stack : stack_writableZ M sp0;
  (* [comment removed for export] *)
  hd_img   : forall i, 0x10000 <= i < 0x21c30 \/ 0x21c38 <= i < 0x22e60 -> M (Z_to_bv 64 i) = None;
  hd_got   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 0x21c30) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x93218));
  hd_can   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 0x93218) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
  hd_can64 : 0 <= can < 2 ^ 64;
  hd_cont  : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 buf) (length content) = Some content
}.
Arguments HD_PRE {RCa1}.  (* a worker (A1) tool *)

Definition hdr_diag_stmt {RCa1 : RunCtx}  (P : list byte -> Prop) (msg : list byte) : Prop :=
  forall (sp0 buf : Z) (content : list byte) (can : Z) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet),
    hd_pre sp0 buf content can R M -> P content ->
    fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader model = true ->   (* a worker port727 *)
    m_halted model = None -> m_vm_lazy model = [] ->
    K [] ->
    (forall R' M',
       (forall r : reg, In r hd_kept -> getr R' r = getr R r) ->
       frame_mod M M' (hd_regions sp0) ->
       (exists wp rp : word, file_clean M' 0x22c70 wp rp) ->
       realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R' (Z_to_bv 64 0x14ac0) M' (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model) K) ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R (Z_to_bv 64 0x149c8) M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model) (t_emit (Spec.W 2 msg) K).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sr_HD : list expr :=
  [ELit 0; J 1; spx (-128); J 3; J 4; J 5; J 6; J 7;
   J 8; EVar 2; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; J 18; EVar 3; J 20; J 21; J 22; J 23;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].

Definition kn_HD0 : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-6144513)) 6144513;
   KWr (SA (ELit 0) 0x22000) 0x72000;
   KImg 0x10000 0x21c30;
   KWord (SA (ELit 0) 0x21c30) 8 (ELit 0x93218);           (* [comment removed for export] *)
   KImg 0x21c38 0x22e60;
   KWord (SA (ELit 0) 0x93218) 8 (EVar 9);                 (* [comment removed for export] *)
   KRange (EVar 2) 0x94000 0x7fffff800000].
(* [comment removed for export] *)
Definition kn_HDs : list kentry := kn_HD0 ++ [KRange (EVar 3) 0 5].
(* [comment removed for export] *)
Definition kn_HDl : list kentry :=
  kn_HD0 ++ [KRange (EVar 3) 6 67108863;
             KWord (SA (EVar 2) 0) 1 (EVar 6); KWord (SA (EVar 2) 1) 1 (EVar 7);
             KRange (EVar 6) 0 255; KRange (EVar 7) 0 255].

Definition HD_FUEL : nat := 5000.
(* [comment removed for export] *)
Definition HD_STOPS : list Z := [0x1b5b8; 0x14ac0].

Definition hd_sregions : list sregion := [(SA (EVar 0) (-512), 384); (SA (ELit 0) 0x22c70, 232)].

Lemma hd_itinerary {RCa1 : RunCtx}  :
  let a := sym_exec (run_segments RSEGS rc_inp rc_sp rc_mb) HD_FUEL true HD_STOPS scr0 (SS 0x149c8 sr_HD [] kn_HDs 43) [] in
  let b := sym_exec (run_segments RSEGS rc_inp rc_sp rc_mb) HD_FUEL true HD_STOPS scr_taken (SS 0x149c8 sr_HD [] kn_HDl 43) [] in
  (s_pc (fst (fst a)), snd (fst a)) = (0x1b5b8, [])
  /\ (s_pc (fst (fst b)), snd (fst b)) = (0x1b5b8, [SCBr true BC_LTU (EVar 3) (EAlu ALU_ADD cfglen_x (ELit 6))]).
Proof. vm_compute. split; reflexivity. Qed.

Lemma w2le1_byte : forall (x : byte), word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned x)) = [x].
Proof.
  intros x. pose proof (bv_unsigned_in_range _ x) as Hx. change (bv_modulus 8) with 256%Z in Hx.
  unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal.
  rewrite u_small by lia. apply Z_to_bv_bv_unsigned.
Qed.

Section Entry.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
  Variables (sp0 buf : Z) (content : list byte) (can : Z) (R : bvmap 5 word) (M : word -> option byte).
  Hypothesis HP : hd_pre sp0 buf content can R M.
  Let L : Z := Z.of_nat (length content).

  Definition hd_vals : list word :=
    [Z_to_bv 64 sp0; Z_to_bv 64 0; Z_to_bv 64 buf; Z_to_bv 64 L; Z_to_bv 64 0; Z_to_bv 64 0;
     Z_to_bv 64 (hdr_b0 content); Z_to_bv 64 (hdr_b1 content); Z_to_bv 64 0; Z_to_bv 64 can; Z_to_bv 64 0] ++ junk_vals R.

  Let E : env := ENVh content hd_vals.

  Lemma hd_vals_length : length hd_vals = 43%nat.
  Proof. unfold hd_vals. rewrite length_app, junk_vals_length. reflexivity. Qed.

  Lemma hd_EJ : forall i, (i < 32)%nat -> ev E (11 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold E, ENVh, hd_vals. cbn [ev]. unfold vals_ev.
    change (11 + i)%nat with (length [Z_to_bv 64 sp0; Z_to_bv 64 0; Z_to_bv 64 buf; Z_to_bv 64 L; Z_to_bv 64 0; Z_to_bv 64 0;
                                      Z_to_bv 64 (hdr_b0 content); Z_to_bv 64 (hdr_b1 content); Z_to_bv 64 0; Z_to_bv 64 can; Z_to_bv 64 0] + i)%nat.
    rewrite app_nth2_plus. unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi.
    reflexivity.
  Qed.

  Lemma hd_regs_ok : regs_ok E sr_HD R.
  Proof.
    destruct HP as [R2 R9 R19 [SP0 _] _ _ _ _ _ _ _ _].
    assert (E0 : ev E 0 = Z_to_bv 64 sp0) by reflexivity.
    assert (E2 : ev E 2 = Z_to_bv 64 buf) by reflexivity.
    assert (E3 : ev E 3 = Z_to_bv 64 L) by reflexivity.
    apply S9ReadBase.regs_ok_by_index. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sr_HD S9ReadBase.all_regs].
    all: try (lazymatch goal with |- _ = edenot _ (J ?n) =>
                unfold J; change (edenot E (EVar (11 + n))) with (ev E (11 + n)%nat); rewrite hd_EJ by lia; reflexivity end).
    all: try (lazymatch goal with |- _ = edenot _ (spx ?z) =>
                unfold spx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot]; rewrite E0;
                rewrite R2; rewrite u_small by lia; f_equal; lia end).
    all: try (change (edenot E (EVar 2)) with (ev E 2); rewrite E2; assumption).
    all: try (change (edenot E (EVar 3)) with (ev E 3); rewrite E3; assumption).
    all: cbn [edenot]; first [assumption | apply getr_zero | reflexivity].
  Qed.

  Lemma hd_know0 : know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E M kn_HD0.
  Proof.
    destruct HP as [_ _ _ [SP0 SP16] [HB HBL] HL HST IMG GOT CANC CAN64 _].
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    assert (E0 : ev E 0 = Z_to_bv 64 sp0) by reflexivity.
    unfold kn_HD0. repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. cbn [edenot]. rewrite E0, u_small by lia. exact SP16.
    - apply krange_intro. cbn [edenot]. rewrite E0, u_small by lia. lia.
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite E0, u_small by lia.
      split; [lia|]. intros d m Hd Hm.
      replace (sp0 + -6144513 + d) with (sp0 - 6144513 + d) by lia. apply HST; lia.
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z0.
      split; [lia|]. intros d m Hd Hm. apply store_ok_data; rewrite u64_lit by lia; lia.
    - apply kimg_intro; [lia | lia | intros i Hi; apply IMG; lia].
    - eapply (kword_intro (run_segments RSEGS rc_inp rc_sp rc_mb) E M (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact GOT].
    - apply kimg_intro; [lia | lia | intros i Hi; apply IMG; lia].
    - eapply (kword_intro (run_segments RSEGS rc_inp rc_sp rc_mb) E M (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact CANC].
    - apply krange_intro. change (edenot E (EVar 2)) with (Z_to_bv 64 buf). rewrite u_small by lia. lia.
  Qed.

  Lemma hd_know_short : (length content < 6)%nat -> know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E M kn_HDs.
  Proof.
    intros Hlt. unfold kn_HDs. apply Forall_app. split; [exact hd_know0|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply krange_intro. change (edenot E (EVar 3)) with (Z_to_bv 64 L). unfold L. rewrite u_small by lia. lia.
  Qed.

  Lemma hd_content_byte : forall j, (j < length content)%nat ->
    rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (buf + Z.of_nat j)) 1%nat
    = Some (word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned (nth j content (Z_to_bv 8 0))))).
  Proof.
    destruct HP as [_ _ _ _ [HB HBL] _ _ _ _ _ _ CONT].
    intros j Hj. pose proof (rdn_nth (run_segments RSEGS rc_inp rc_sp rc_mb) M (length content) _ content j CONT Hj) as H.
    rewrite w_add_nat in H. rewrite u_small in H by lia. rewrite w2le1_byte. exact H.
  Qed.

  Lemma hd_know_long : (6 <= length content)%nat -> know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E M kn_HDl.
  Proof.
    intros Hge. pose proof HP as [_ _ _ _ [HB HBL] HL _ _ _ _ _ _].
    pose proof (bv_unsigned_in_range _ (nth 0 content (Z_to_bv 8 0))) as B0.
    pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1.
    change (bv_modulus 8) with 256%Z in B0, B1.
    assert (E2 : ev E 2 = Z_to_bv 64 buf) by reflexivity.
    unfold kn_HDl. apply Forall_app. split; [exact hd_know0|].
    repeat apply Forall_cons; try apply Forall_nil.
    - apply krange_intro. change (edenot E (EVar 3)) with (Z_to_bv 64 L). unfold L in *. rewrite u_small by lia. lia.
    - cbn [kentry_ok]. split; [lia|]. split; [apply flat_intro; change (edenot E (EVar 2)) with (ev E 2); rewrite ?E2; rewrite ?u_small by lia; lia|].
      unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev E 2) with (Z_to_bv 64 buf).
      change (ev E 6) with (Z_to_bv 64 (hdr_b0 content)). unfold hdr_b0. rewrite u_small by lia.
      replace (buf + 0)%Z with (buf + Z.of_nat 0)%Z by lia.
      apply hd_content_byte. lia.
    - cbn [kentry_ok]. split; [lia|]. split; [apply flat_intro; change (edenot E (EVar 2)) with (ev E 2); rewrite ?E2; rewrite ?u_small by lia; lia|].
      unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev E 2) with (Z_to_bv 64 buf).
      change (ev E 7) with (Z_to_bv 64 (hdr_b1 content)). unfold hdr_b1. rewrite u_small by lia.
      replace (buf + 1)%Z with (buf + Z.of_nat 1)%Z by lia.
      apply hd_content_byte. lia.
    - apply krange_intro. change (edenot E (EVar 6)) with (Z_to_bv 64 (hdr_b0 content)). unfold hdr_b0. rewrite u_small by lia. lia.
    - apply krange_intro. change (edenot E (EVar 7)) with (Z_to_bv 64 (hdr_b1 content)). unfold hdr_b1. rewrite u_small by lia. lia.
  Qed.
End Entry.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma hd_regions_denot : forall (E : env) (sp0 : Z),
  0x7fff80000000 <= sp0 <= 0x800000000000 -> ev E 0 = Z_to_bv 64 sp0 -> map (rdenot E) hd_sregions = hd_regions sp0.
Proof.
  intros E sp0 SP0 H. unfold hd_sregions, hd_regions, rdenot, estart. cbn [map fst snd a_base a_off edenot]. rewrite H.
  change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite u_small by lia.
  replace (sp0 + -512) with (sp0 - 512) by lia. reflexivity.
Qed.

Lemma hd_regions_flat : forall (E : env) (sp0 : Z),
  0x7fff80000000 <= sp0 <= 0x800000000000 -> ev E 0 = Z_to_bv 64 sp0 -> regions_flat E hd_sregions.
Proof.
  intros E sp0 SP0 H r Hr. unfold hd_sregions in Hr. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[]]]; unfold flat, estart; cbn [fst snd a_base a_off edenot]; rewrite ?H;
    change (bv_unsigned (Z_to_bv 64 0)) with 0; rewrite ?u_small by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma hd_block_frame : forall (E : env) (sp0 : Z) base log,
  0x7fff80000000 <= sp0 <= 0x800000000000 -> ev E 0 = Z_to_bv 64 sp0 ->
  log_covered hd_sregions log = true -> log_flat E log ->
  frame_mod base (mem_denot E base log) (hd_regions sp0).
Proof.
  intros E sp0 base log SP0 H Hc Hlf. rewrite <- (hd_regions_denot E sp0 SP0 H).
  apply log_covered_frame; [exact Hc | apply (hd_regions_flat E sp0 SP0 H) | exact Hlf].
Qed.

(* [comment removed for export] *)
Lemma hd_sw_frame {RCa1 : RunCtx}  : forall (sp0 : Z) M M' bufp bufsz,
  0x7fff80000000 <= sp0 <= 0x800000000000 ->
  sw_post M (sp0 - 192) 0x22c70 bufp bufsz M' -> frame_mod M M' (hd_regions sp0).
Proof.
  intros sp0 M M' bufp bufsz SP0 [Pagree Pgrows _ _ _].
  split; [|exact Pgrows]. intros a Ho. unfold hd_regions in Ho. cbn [outside] in Ho. unfold in_rng in Ho.
  rewrite !u64_lit in Ho by lia. apply Pagree; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma msg_short_img {RCa1 : RunCtx}  : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 0x10502) 31 = Some Spec.msg_short.
Proof. vm_compute. reflexivity. Qed.
Lemma msg_overrun_img {RCa1 : RunCtx}  : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 0x10368) 31 = Some Spec.msg_overrun.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Ltac hd_stdio_then_join vals content sp0 msg msg_img msg_addr HL P0 SP0 HR0 FMa Hfd Hrdr Hh Hl HKnil HCONT HR HK :=
  lazymatch type of HR with regs_ok _ ?sr ?Rb => lazymatch type of HK with know_ok _ _ ?Mb ?kn =>
    let sc := eval vm_compute in (stdio_call 43 sr kn) in
    lazymatch sc with
    | Some ?res =>
        let SC := fresh "SC" in
        assert (SC : stdio_call (length vals) sr kn = Some res) by (rewrite HL; vm_cast_no_check (@eq_refl _ (Some res)));
        lazymatch goal with |- realizes _ (mkCfg _ ?model) (t_emit _ ?K) =>
          apply (stdio_call_sound_post vals (blobs_ev [content]) sr kn Rb Mb model res [] msg K HR HK SC) end;
        cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn]
    end end end;
  [ cbn [edenot]; lia
  | cbn [edenot length Z.of_nat]; lia
  | cbn [edenot]; rewrite u64_lit by lia; reflexivity
  | change (@length byte msg) with 31%nat; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia
  | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVh]; rewrite P0;
    rewrite (u64_lit sp0) by lia; rewrite !u64_lit by lia; lia
  | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVh]; rewrite P0;
    rewrite (u64_lit sp0) by lia; rewrite !u64_lit by lia; lia
  | cbn [edenot]; rewrite !u64_lit by lia; lia
  | cbn [edenot]; rewrite !u64_lit by lia; unfold TASK_SIZE; lia
  | cbn [edenot]; rewrite !u64_lit by lia; unfold TASK_SIZE; lia
  | reflexivity
  | cbn [edenot]; change (@length byte msg) with 31%nat;
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      rewrite (kimg_rdn (run_segments RSEGS rc_inp rc_sp rc_mb) (ENVh content vals) _ kn ltac:(let i := kidx kn (is_kimg_cov msg_addr 31) in exact i)
                 _ _ msg_addr 31 HK eq_refl) by (cbn; lia) end;
    apply msg_img
  | exact Hfd
  | exact Hrdr
  | exact Hh
  | exact Hl
  | exact HKnil
  | ].

Theorem hdr_diag_short {RCa1 : RunCtx}  : hdr_diag_stmt (fun content => (length content < 6)%nat) Spec.msg_short.
Proof.
  intros sp0 buf content can R M model K HP Hlt Hfd Hrdr Hh Hl HKnil HCONT.
  pose proof HP as [_ _ _ [SP0 _] _ _ _ _ _ _ _ _].
  pose proof (hd_regs_ok sp0 buf content can R M HP) as HR.
  pose proof (hd_know_short sp0 buf content can R M HP Hlt) as HK.
  set (vals := hd_vals sp0 buf content can R) in *.
  assert (HL : length vals = 43%nat) by apply hd_vals_length.
  assert (P0 : vals_ev vals 0 = Z_to_bv 64 sp0) by reflexivity.
  pose proof HR as HR0.
  (* [comment removed for export] *)
  run_block_lf HR HK HD_FUEL HD_STOPS scr0 43%nat.
  clear HR HK. intros Ra Ma HR HK EQa LFa. cbn [s_pc s_regs s_log] in HR, EQa, LFa |- *.
  assert (FMa : frame_mod M Ma (hd_regions sp0)).
  { rewrite EQa. apply hd_block_frame; [exact SP0 | exact P0 | vm_compute; reflexivity | exact LFa]. }
  clear EQa LFa.
  (* [comment removed for export] *)
  hd_stdio_then_join vals content sp0 Spec.msg_short msg_short_img 0x10502 HL P0 SP0 HR0 FMa Hfd Hrdr Hh Hl HKnil HCONT HR HK.
  (* [comment removed for export] *)
  clear HR HK. intros Rc Mc HR HK POST.
  assert (FMc : frame_mod Ma Mc (hd_regions sp0)).
  { eapply hd_sw_frame; [exact SP0|].
    rewrite edenot_add_lit in POST. unfold adenot, v_addi in POST. cbn [a_base a_off edenot ev ENVh] in POST.
    rewrite P0 in POST. rewrite (u64_lit sp0) in POST by lia. rewrite !u64_lit in POST by lia.
    replace (sp0 - 192) with (sp0 + -192) by lia. exact POST. }
  clear POST.
  set (vals' := vals ++ junk_vals Rc) in *.
  assert (P0' : vals_ev vals' 0 = Z_to_bv 64 sp0) by reflexivity.
  run_block_lf HR HK HD_FUEL HD_STOPS scr0 75%nat.
  clear HR HK. intros Rd Md HR HK EQd LFd. cbn [s_pc s_regs s_log] in HR, EQd, LFd |- *.
  assert (FMd : frame_mod Mc Md (hd_regions sp0)).
  { rewrite EQd. apply hd_block_frame; [exact SP0 | exact P0' | vm_compute; reflexivity | exact LFd]. }
  clear EQd LFd.
  apply HCONT.
  - (* [comment removed for export] *)
    eapply (same_regs_sound _ sr_HD _ R Rd hd_kept); [ | | exact HR].
    + vm_compute. reflexivity.
    + subst vals'. apply env_app_regs; [rewrite HL; vm_compute; reflexivity | exact HR0].
  - (* [comment removed for export] *)
    eapply frame_mod_trans_same; [|exact FMd]. eapply frame_mod_trans_same; [exact FMa | exact FMc].
  - (* [comment removed for export] *)
    exists (Z_to_bv 64 0x93678), (Z_to_bv 64 0). repeat split; krd_solve HK.
Qed.

Theorem hdr_diag_overrun {RCa1 : RunCtx}  :
  hdr_diag_stmt (fun content => (6 <= length content)%nat /\ Z.of_nat (length content) < 6 + hdr_cfglen content) Spec.msg_overrun.
Proof.
  intros sp0 buf content can R M model K HP [Hge Hov] Hfd Hrdr Hh Hl HKnil HCONT.
  pose proof HP as [_ _ _ [SP0 _] _ HLL _ _ _ _ _ _].
  pose proof (hd_regs_ok sp0 buf content can R M HP) as HR.
  pose proof (hd_know_long sp0 buf content can R M HP Hge) as HK.
  pose proof (hdr_cfglen_range content) as CR.
  set (vals := hd_vals sp0 buf content can R) in *.
  assert (HL : length vals = 43%nat) by apply hd_vals_length.
  assert (P0 : vals_ev vals 0 = Z_to_bv 64 sp0) by reflexivity.
  assert (P3 : vals_ev vals 3 = Z_to_bv 64 (Z.of_nat (length content))) by reflexivity.
  assert (P6 : vals_ev vals 6 = Z_to_bv 64 (hdr_b0 content)) by reflexivity.
  assert (P7 : vals_ev vals 7 = Z_to_bv 64 (hdr_b1 content)) by reflexivity.
  pose proof HR as HR0.
  (* [comment removed for export] *)
  run_block_lf HR HK HD_FUEL HD_STOPS scr_taken 43%nat.
  { (* [comment removed for export] *)
    unfold sc_denot. fold cfglen_x. cbn [edenot].
    rewrite (cfglen_val content vals P6 P7). change (ev (ENVh content vals) 3) with (vals_ev vals 3). rewrite P3.
    rewrite alu_add. unfold v_add. cbn [branch_taken]. unfold bv_ltu.
    rewrite (u_small (hdr_cfglen content)) by lia. change (bv_unsigned (Z_to_bv 64 6)) with 6%Z.
    rewrite !u_small by lia. apply Z.ltb_lt. lia. }
  clear HR HK. intros Ra Ma HR HK EQa LFa. cbn [s_pc s_regs s_log] in HR, EQa, LFa |- *.
  assert (FMa : frame_mod M Ma (hd_regions sp0)).
  { rewrite EQa. apply hd_block_frame; [exact SP0 | exact P0 | vm_compute; reflexivity | exact LFa]. }
  clear EQa LFa.
  (* [comment removed for export] *)
  hd_stdio_then_join vals content sp0 Spec.msg_overrun msg_overrun_img 0x10368 HL P0 SP0 HR0 FMa Hfd Hrdr Hh Hl HKnil HCONT HR HK.
  (* [comment removed for export] *)
  clear HR HK. intros Rc Mc HR HK POST.
  assert (FMc : frame_mod Ma Mc (hd_regions sp0)).
  { eapply hd_sw_frame; [exact SP0|].
    rewrite edenot_add_lit in POST. unfold adenot, v_addi in POST. cbn [a_base a_off edenot ev ENVh] in POST.
    rewrite P0 in POST. rewrite (u64_lit sp0) in POST by lia. rewrite !u64_lit in POST by lia.
    replace (sp0 - 192) with (sp0 + -192) by lia. exact POST. }
  clear POST.
  set (vals' := vals ++ junk_vals Rc) in *.
  assert (P0' : vals_ev vals' 0 = Z_to_bv 64 sp0) by reflexivity.
  run_block_lf HR HK HD_FUEL HD_STOPS scr0 75%nat.
  clear HR HK. intros Rd Md HR HK EQd LFd. cbn [s_pc s_regs s_log] in HR, EQd, LFd |- *.
  assert (FMd : frame_mod Mc Md (hd_regions sp0)).
  { rewrite EQd. apply hd_block_frame; [exact SP0 | exact P0' | vm_compute; reflexivity | exact LFd]. }
  clear EQd LFd.
  apply HCONT.
  - (* [comment removed for export] *)
    eapply (same_regs_sound _ sr_HD _ R Rd hd_kept); [ | | exact HR].
    + vm_compute. reflexivity.
    + subst vals'. apply env_app_regs; [rewrite HL; vm_compute; reflexivity | exact HR0].
  - (* [comment removed for export] *)
    eapply frame_mod_trans_same; [|exact FMd]. eapply frame_mod_trans_same; [exact FMa | exact FMc].
  - (* [comment removed for export] *)
    exists (Z_to_bv 64 0x93678), (Z_to_bv 64 0). repeat split; krd_solve HK.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
