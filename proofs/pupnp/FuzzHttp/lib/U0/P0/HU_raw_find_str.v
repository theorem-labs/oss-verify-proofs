From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_syscalls F_ctype F_twoway_A F_twoway_C HU_list_kit.
Import ListNotations.
Open Scope Z_scope.

Definition rfs_entry := 0x155d4%Z.

Ltac rfs_sstep := step; fix_lit_store.
Ltac rfs_lit_branch :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    first [ replace (if c then a else b) with a by (vm_compute; reflexivity)
          | replace (if c then a else b) with b by (vm_compute; reflexivity) ] end.
Ltac rfs_b2z :=
  repeat match goal with |- context [Z.b2z (?a <? ?b)] =>
    first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) ] end;
  cbn [Z.b2z]; change (Z.lxor 1 0) with 1; change (Z.lxor 0 1) with 1; change (Z.lxor 1 1) with 0; change (Z.lxor 0 0) with 0.
Ltac rfs_post_callq segs m :=
  let ms' := fresh "ms'" in let PO := fresh "PC" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  try (lazymatch goal with QSP : bv_unsigned (Z_to_bv 64 _) = _ |- _ => try rewrite !QSP in MUc; try rewrite !QSP in PO end);
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).
Tactic Notation "rfs_callq" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | rfs_post_callq segs m ]
  end.

Lemma rfs_le1_small : forall z, (0 <= z < 256)%Z -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z Hz. apply le1_of_mod8. rewrite unsigned_lit by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256%Z. change (2^8)%Z with 256%Z. reflexivity.
Qed.

Lemma rfs_to_lower_nz : forall c, 0 < c < 256 -> 0 < to_lower c < 256.
Proof. intros c Hc. unfold to_lower, is_upper. destruct (_ && _)%bool eqn:E; [apply andb_true_iff in E; destruct E as [E1 E2]; apply Z.leb_le in E1; apply Z.ltb_lt in E2|]; lia. Qed.

Lemma rfs_upd_nth_same : forall (l : list byte) i x, nth_error l i = Some x -> upd l i x = l.
Proof.
  intros l i x H. apply nth_error_ext. intros j. destruct (Nat.eq_dec j i) as [->|NE].
  - rewrite nth_error_upd_same; [symmetry; exact H| exact (nth_error_lt _ _ _ H)].
  - rewrite nth_error_upd_other by lia. reflexivity.
Qed.

Lemma rfs_first_nul : forall (vbs : list byte) (k : nat), nth_error vbs k = Some (Z_to_bv 8 0) ->
  exists str rest, vbs = str ++ Z_to_bv 8 0 :: rest /\ ~ In (Z_to_bv 8 0) str /\ (length str <= k)%nat.
Proof.
  induction vbs as [|a l IH]; intros k H; [destruct k; discriminate|].
  destruct (Z.eq_dec (bv_unsigned a) 0) as [E|NE].
  - exists [], l. assert (a = Z_to_bv 8 0) as -> by (apply bv_eq; rewrite E; reflexivity).
    split; [reflexivity|]. split; [intros []| cbn; lia].
  - destruct k as [|k].
    + cbn in H. injection H as ->. exfalso. apply NE. reflexivity.
    + destruct (IH k H) as (s & r & E & NI & L). exists (a :: s), r. cbn. rewrite E. split; [reflexivity|]. split; [| lia].
      intros [H1|H1]; [| exact (NI H1)]. apply NE. subst a. reflexivity.
Qed.

Lemma rfs_nad_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m NAD chunked_bytes.
Proof.
  intros m MI. pose proof (ro_cells_image rsegs m NAD chunked_bytes MI ltac:(vm_compute; reflexivity) ltac:(unfold NAD; lia) ltac:(unfold NAD; cbn; lia)) as RO.
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Lemma rfs_strstr_call : forall (qq lo0 Hh : Z) (hay slack : list byte) (canary0 : word)
    (ra0 gp0 tp0 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (F0 : bvmap 5 word) (fc0 : bv 32) (m : mem),
  bytes_at rsegs m Hh (hay ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) hay ->
  ((- (Hh + Z.of_nat (length hay) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary0] ->
  stk rsegs m lo0 qq -> (lo0 <= qq - 2240)%Z -> (0 <= qq < 2^64)%Z -> (0 < Hh)%Z ->
  (Hh + Z.of_nat (length hay) + 1 + Z.of_nat (length slack) <= lo0)%Z ->
  (got_ssp + 8 <= lo0)%Z -> (ssp_guard + 8 <= lo0)%Z -> (NAD + 8 <= lo0)%Z ->
  mem_inv rsegs m -> a0 = Z_to_bv 64 Hh -> a1 = Z_to_bv 64 NAD ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (r : Z),
      ms' = MS (mkR ra0 (Z_to_bv 64 qq) gp0 tp0 t0' t1' t2' x8 x9 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
               F0 (ret_pc ra0) fc0 None m' (seg_rom rsegs)
      /\ munch [(qq - 2240, qq)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo0 qq
      /\ bytes_at rsegs m' Hh (hay ++ Z_to_bv 8 0 :: slack)
      /\ rw_cells rsegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m' ssp_guard [C8 canary0]
      /\ (r = 0 \/ Hh <= r <= Hh + Z.of_nat (length hay))%Z)
    (MS (mkR ra0 (Z_to_bv 64 qq) gp0 tp0 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F0 (Z_to_bv 64 strstr_entry) fc0 None m (seg_rom rsegs)).
Proof.
  intros until m. intros HAY NONUL PAD GOT CAN ST LO QQ H0 SEPH SG1 SG2 SG3 MI -> ->.
  assert (E0 : bv_unsigned (Z_to_bv 64 qq) = qq) by (apply unsigned_lit; lia).
  pose proof ST as ST'. destruct ST' as (L0 & _ & _).
  assert (E1 : bv_unsigned (Z_to_bv 64 Hh) = Hh) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (strstr_chunked_spec ra0 (Z_to_bv 64 qq) gp0 tp0 t0 t1 t2 x8 x9 (Z_to_bv 64 Hh) (Z_to_bv 64 NAD) a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F0 fc0 m hay slack canary0 lo0);
      rewrite ?E0, ?E1; eauto; try lia. apply rfs_nad_bytes. exact MI. }
  intros ms' Q. unfold twoway_post in Q. rewrite !E0, !E1 in Q. exact Q.
Qed.

Section RFS.
  Variables (qq lo0 MP B n L : Z) (vbs sl : list byte) (canary0 : word).
  Variables (ra0 gp0 tp0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (F0 : bvmap 5 word) (fc0 : bv 32) (m0 : mem).
  Hypothesis VN : nth_error vbs (Z.to_nat L) = Some (Z_to_bv 8 0).
  Hypothesis LR : 0 <= L < n.
  Hypothesis SLP : (- (B + n)) mod 8 <= Z.of_nat (length sl).
  Hypothesis LOD : lo0 <= qq - 2288.
  Hypothesis MPQ : qq <= MP.
  Hypothesis MPH : MP + 16 <= 2^64.
  Hypothesis MPA : MP mod 8 = 0.
  Hypothesis BP : 0 < B.
  Hypothesis NB : L < 2^31.
  Hypothesis SEP : B + n + Z.of_nat (length sl) <= lo0.
  Hypothesis SG1 : got_ssp + 8 <= lo0.
  Hypothesis SG2 : ssp_guard + 8 <= lo0.
  Hypothesis SG3 : NAD + 8 <= lo0.
  Hypothesis SGD1 : B + n + Z.of_nat (length sl) <= got_ssp \/ got_ssp + 8 <= B.
  Hypothesis SGD2 : B + n + Z.of_nat (length sl) <= ssp_guard \/ ssp_guard + 8 <= B.
  Hypothesis L00 : 0 <= lo0.
  Hypothesis QH0 : qq <= 2^64.
  Hypothesis LVB0 : length vbs = Z.to_nat n.

  Notation W := [(qq - 2288, qq); (B, B + n)]%Z.
  Notation FRM m := (rw_cells rsegs m (qq + -48) [C8 x20; C8 x19; C8 x18; C8 x9; C8 x8; C8 ra0]).

  Definition RPOST : machine_state -> Prop :=
    fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' vbs',
      ms' = MS (mkR ra0 (Z_to_bv 64 qq) gp0 tp0 t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
               F0 (ret_pc ra0) fc0 None m' (seg_rom rsegs)
      /\ munch W m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo0 qq
      /\ rw_cells rsegs m' B [CB (Z.to_nat n) vbs']
      /\ (forall j, nth_error vbs j = Some (Z_to_bv 8 0) -> nth_error vbs' j = Some (Z_to_bv 8 0)).

  Definition rlinv (vbs' : list byte) (i : nat) : Prop :=
    length vbs' = length vbs /\ (forall j, (i <= j)%nat -> nth_error vbs' j = nth_error vbs j)
    /\ (forall j b, (j < i)%nat -> nth_error vbs' j = Some b -> bv_unsigned b <> 0)
    /\ (forall j, nth_error vbs j = Some (Z_to_bv 8 0) -> nth_error vbs' j = Some (Z_to_bv 8 0)).

  #[using="All"] Lemma rfs_facts : 0 <= lo0 /\ qq <= 2^64 /\ length vbs = Z.to_nat n /\ bv_unsigned (Z_to_bv 64 qq) = qq.
  Proof.
    split; [lia|]. split; [lia|]. split; [lia|]. apply unsigned_lit. lia.
  Qed.

  #[using="All"] Lemma rfs_ret : forall (vbs' : list byte) (m : mem) x1 x5 x6 x7 y8 y9 x10 x11 x12 x13 x14 x15 x16 x17 y18 y19 y20 x28 x29 x30 x31,
    munch W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
    FRM m -> stk rsegs m lo0 (qq + -48) ->
    rw_cells rsegs m B [CB (Z.to_nat n) vbs'] -> (forall j, nth_error vbs j = Some (Z_to_bv 8 0) -> nth_error vbs' j = Some (Z_to_bv 8 0)) ->
    evt rsegs RPOST (MS (mkR x1 (Z_to_bv 64 (qq + -48)) gp0 tp0 x5 x6 x7 y8 y9 x10 x11 x12 x13 x14 x15 x16 x17 y18 y19 y20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F0 (Z_to_bv 64 0x156e4) fc0 None m (seg_rom rsegs)).
  Proof.
    intros until x31. intros MU WM MI FR ST VB LZ.
    destruct rfs_facts as (L0 & QH & LVB & QQ).
    do 8 step.
    release_frame FR ST qq.
    apply evt_done. unfold RPOST. do 15 eexists. exists m, vbs'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact VB| exact LZ].
  Qed.

  #[using="All"] Lemma rfs_exit : forall (str rest vbs' : list byte) (m : mem) x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 y18 y20 x28 x29 x30 x31,
    vbs = str ++ Z_to_bv 8 0 :: rest -> ~ In (Z_to_bv 8 0) str -> (length str <= Z.to_nat L)%nat ->
    munch W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
    FRM m -> stk rsegs m lo0 (qq + -48) -> rw_cells rsegs m MP [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 L)] -> bytes_at rsegs m (B + n) sl ->
    rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary0] ->
    u8arr rsegs m B vbs' -> rlinv vbs' (length str) ->
    evt rsegs RPOST (MS (mkR x1 (Z_to_bv 64 (qq + -48)) gp0 tp0 x5 x6 x7 (Z_to_bv 64 MP) (Z_to_bv 64 NAD) x10 (Z_to_bv 64 B) x12 x13 x14 x15 x16 x17
                            y18 (Z_to_bv 64 0) y20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F0 (Z_to_bv 64 0x15688) fc0 None m (seg_rom rsegs)).
  Proof.
    intros until x31. intros EV NI LS MU WM MI FR ST MPC SLB GOT CAN WB LI.
    destruct rfs_facts as (L0 & QH & LVB & QQ).
    destruct LI as (LL & LGE & LLT & LZ).
    set (f := length str) in *.
    assert (FZ : nth_error vbs f = Some (Z_to_bv 8 0)). { rewrite EV. rewrite nth_error_app2 by lia. subst f. rewrite Nat.sub_diag. reflexivity. }
    assert (VNL : nth_error vbs' (Z.to_nat L) = Some (Z_to_bv 8 0)) by (apply LZ; exact VN).
    zstep. zstep. step. ubr.
    zstep.
    pose proof (u8arr_store_ok rsegs _ _ _ L (Z_to_bv 64 (B + L)) WB ltac:(rewrite LL, LVB; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep. change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 ?e) ?x) _) => change (write_to_mem mm (Z_to_bv 64 e) x) with (write_to_mem mm (wa e) x) end.
    pose proof (u8arr_write rsegs _ _ _ L (Z_to_bv 8 0) WB ltac:(rewrite LL, LVB; lia)) as WB2. clear WB. store_done.
    rewrite (rfs_upd_nth_same vbs' (Z.to_nat L) (Z_to_bv 8 0) VNL) in WB2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2 end.
    destruct (nth_error_split vbs' f (Z_to_bv 8 0)) as (hay & l2 & E1 & L1). { rewrite (LGE f) by lia. exact FZ. }
    pose proof WB2 as WB2b. destruct WB2b as [HB _].
    assert (HAYB : bytes_at rsegs m2 B (hay ++ Z_to_bv 8 0 :: l2 ++ sl)).
    { replace (hay ++ Z_to_bv 8 0 :: l2 ++ sl) with (vbs' ++ sl) by (rewrite E1, <- app_assoc; reflexivity).
      apply bytes_at_app. split; [exact HB|]. rewrite LL, LVB. replace (B + Z.of_nat (Z.to_nat n)) with (B + n) by lia. exact SLB. }
    assert (NONUL : ~ In (Z_to_bv 8 0) hay).
    { intros HIN. apply In_nth_error in HIN. destruct HIN as [j Hj]. pose proof (nth_error_lt _ _ _ Hj) as JL.
      apply (LLT j (Z_to_bv 8 0)); [lia| | reflexivity]. rewrite E1. rewrite nth_error_app1 by lia. exact Hj. }
    assert (LSK : Z.of_nat (length (l2 ++ sl)) = n - Z.of_nat f - 1 + Z.of_nat (length sl)).
    { rewrite length_app. apply (f_equal (@length byte)) in E1. rewrite length_app in E1. cbn [length] in E1. lia. }
    assert (PAD : (- (B + Z.of_nat (length hay) + 1)) mod 8 <= Z.of_nat (length (l2 ++ sl))).
    { rewrite LSK, L1. clear - SLP LS LR LVB. Z.div_mod_to_equations. lia. }
    zstep. zstep. zstep. zstep.
    rfs_callq (rfs_strstr_call (qq + -48) lo0 B hay (l2 ++ sl) canary0).
    all: side (first [exact HAYB | exact NONUL | exact PAD | exact ST | assumption | reflexivity
                     | (rewrite ?L1, ?LSK; lia) ]).
    zstep. zstep. step. ubr.
    zstep. zstep. zstep. rfs_b2z. step. rfs_lit_branch.
    step. ubr.
    pose proof (u8arr_store_ok rsegs _ _ _ L (Z_to_bv 64 (B + L)) WB2 ltac:(rewrite LL, LVB; lia) ltac:(unfold wa; f_equal; lia)) as SOK2.
    zstep. change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 ?e) ?x) _) => change (write_to_mem mm (Z_to_bv 64 e) x) with (write_to_mem mm (wa e) x) end.
    pose proof (u8arr_write rsegs _ _ _ L (Z_to_bv 8 0) WB2 ltac:(rewrite LL, LVB; lia)) as WB3. clear WB2. store_done.
    rewrite (rfs_upd_nth_same vbs' (Z.to_nat L) (Z_to_bv 8 0) VNL) in WB3.
    pose proof (rw_cells_of_u8arr _ _ _ _ WB3) as VB3. rewrite LL, LVB in VB3.
    step. if_cases K0; zify_cond K0.
    - zstep. eapply (rfs_ret vbs'); try eassumption.
    - zstep. zstep. zstep. eapply (rfs_ret vbs'); try eassumption.
  Qed.

  #[using="All"] Lemma rfs_loop : forall (str rest : list byte) (k i : nat) (vbs' : list byte) (m : mem) (p ii : Z) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    vbs = str ++ Z_to_bv 8 0 :: rest -> ~ In (Z_to_bv 8 0) str -> (length str <= Z.to_nat L)%nat ->
    (length str - i < k)%nat -> (i <= length str)%nat -> p = B + Z.of_nat i -> ii = Z.of_nat i ->
    munch W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
    FRM m -> stk rsegs m lo0 (qq + -48) -> rw_cells rsegs m MP [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 L)] -> bytes_at rsegs m (B + n) sl ->
    rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary0] ->
    u8arr rsegs m B vbs' -> rlinv vbs' i ->
    evt rsegs RPOST (MS (mkR x1 (Z_to_bv 64 (qq + -48)) gp0 tp0 x5 x6 x7 (Z_to_bv 64 MP) (Z_to_bv 64 NAD) (Z_to_bv 64 1) (Z_to_bv 64 B) x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 p) (Z_to_bv 64 0) (Z_to_bv 64 ii) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F0 (Z_to_bv 64 0x15638) fc0 None m (seg_rom rsegs)).
  Proof.
    intros str rest k. induction k as [|k IH]; intros until x31; intros EV NI LS HK HI EP EI MU WM MI FR ST MPC SLB GOT CAN WB LI; [lia|]. subst p ii.
    destruct rfs_facts as (L0 & QH & LVB & QQ).
    pose proof LI as LI0. destruct LI as (LL & LGE & LLT & LZ).
    set (f := length str) in *.
    assert (FZ : nth_error vbs f = Some (Z_to_bv 8 0)). { rewrite EV. rewrite nth_error_app2 by lia. subst f. rewrite Nat.sub_diag. reflexivity. }
    destruct (nth_error vbs i) as [bc|] eqn:Hbc. 2:{ exfalso. apply nth_error_None in Hbc. rewrite EV, length_app in Hbc. cbn in Hbc. lia. }
    pose proof (byte_lt256 bc) as BR.
    assert (Hbc' : nth_error vbs' i = Some bc) by (rewrite (LGE i) by lia; exact Hbc).
    pose proof (u8arr_read rsegs _ _ vbs' (Z.of_nat i) bc (Z_to_bv 64 (B + Z.of_nat i)) WB ltac:(rewrite Nat2Z.id; exact Hbc') ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. step. rfs_lit_branch.
    zstep.
    step. if_cases K0; zify_cond K0.
    -
      assert (EF : i = f).
      { destruct (Nat.eq_dec i f) as [E|NE]; [exact E|]. exfalso. assert (i < f)%nat as LT by lia.
        rewrite EV, nth_error_app1 in Hbc by lia. apply NI. assert (bc = Z_to_bv 8 0) as <- by (apply bv_eq; rewrite K0; reflexivity). eapply nth_error_In. exact Hbc. }
      subst i. eapply (rfs_exit str rest vbs'); try eassumption.
    - assert (ILT : (i < f)%nat).
      { destruct (Nat.lt_ge_cases i f) as [LT|GE]; [exact LT|]. exfalso. assert (i = f) as -> by lia. rewrite FZ in Hbc. injection Hbc as <-. apply K0. reflexivity. }
      pose proof (rfs_to_lower_nz (bv_unsigned bc) ltac:(lia)) as TL.
      zstep. call tolower_spec. all: side (rewrite ?unsigned_lit by lia; first [assumption | lia]).
      rewrite unsigned_lit by lia.
      zstep. rewrite (swrap32_id (Z.of_nat i + 1)) by lia.
      pose proof (u8arr_store_ok rsegs _ _ _ (Z.of_nat i) (Z_to_bv 64 (B + Z.of_nat i)) WB ltac:(rewrite LL, LVB; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
      zstep.
      rewrite (rfs_le1_small (to_lower (bv_unsigned bc))) by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 ?e) ?x) _) =>
        replace (write_to_mem mm (Z_to_bv 64 e) x) with (write_to_mem mm (wa (B + Z.of_nat i)) x) by (unfold wa; f_equal; f_equal; lia) end.
      pose proof (u8arr_write rsegs _ _ _ (Z.of_nat i) (Z_to_bv 8 (to_lower (bv_unsigned bc))) WB ltac:(rewrite LL, LVB; lia)) as WB2. clear WB RD. store_done.
      rewrite Nat2Z.id in WB2. set (vbs2 := upd vbs' i (Z_to_bv 8 (to_lower (bv_unsigned bc)))) in WB2.
      assert (LI2 : rlinv vbs2 (S i)).
      { subst vbs2. split; [| split; [| split]].
        - rewrite upd_length. exact LL.
        - intros j Hj. rewrite nth_error_upd_other by lia. apply LGE. lia.
        - intros j b Hj Hb. destruct (Nat.eq_dec j i) as [->|NE].
          + rewrite nth_error_upd_same in Hb by (rewrite LL, LVB; lia). injection Hb as <-. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256%Z. rewrite Z.mod_small by lia. lia.
          + rewrite nth_error_upd_other in Hb by lia. exact (LLT j b ltac:(lia) Hb).
        - intros j Hj. destruct (Nat.eq_dec j i) as [->|NE]; [rewrite Hbc in Hj; injection Hj as E0; exfalso; apply K0; rewrite E0; reflexivity|].
          rewrite nth_error_upd_other by lia. apply LZ. exact Hj. }
      clearbody vbs2. clear LI0 LL LGE LLT LZ.
      step. ubr_by ltac:(rewrite ?signed_lit in KU by lia; lia).
      zstep. zstep. zstep. zstep. rfs_b2z. step. rfs_lit_branch.
      zstep. zstep. zstep. zstep.
      assert (SLT : forall zz, 0 <= zz < 2^63 -> (Z.lxor zz 9223372036854775808 <? 9223372036854775808) = false)
        by (intros zz Hzz; change 9223372036854775808 with (2^63); rewrite zb_lxor_pow2_small by lia; apply Z.ltb_ge; lia).
      rewrite ?SLT by lia. clear SLT. rfs_b2z. cbn [Z.b2z]. change (Z.lxor (Z.lxor 0 0) 1) with 1.
      step.
      step. rfs_lit_branch.
      eapply (IH (S i) vbs2); try eassumption; try lia.
  Qed.

  #[using="All"] Lemma rfs_body : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    rw_cells rsegs m0 MP [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 L)] -> rw_cells rsegs m0 B [CB (Z.to_nat n) vbs] -> bytes_at rsegs m0 (B + n) sl ->
    rw_cells rsegs m0 got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m0 ssp_guard [C8 canary0] -> stk rsegs m0 lo0 qq -> mem_inv rsegs m0 ->
    evt rsegs RPOST (MS (mkR ra0 (Z_to_bv 64 qq) gp0 tp0 t0 t1 t2 x8 x9 (Z_to_bv 64 MP) (Z_to_bv 64 NAD) a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                        F0 (Z_to_bv 64 rfs_entry) fc0 None m0 (seg_rom rsegs)).
  Proof.
    intros until t6. intros MPC VB0 SLB GOT CAN ST MI. unfold rfs_entry.
    destruct rfs_facts as (L0 & QH & LVB & QQ).
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ VB0) as WB. clear VB0.
    carve_frame 48%nat ST.
    zstep. do 6 rfs_sstep.
    step. ubr.
    zstep.
    ub_align.
    zstep. zstep. zstep. step. ubr.
    zstep. zstep. zstep. zstep. rfs_b2z. step. rfs_lit_branch.
    step. ubr.
    zstep.
    pose proof (u8arr_read rsegs _ _ vbs L (Z_to_bv 8 0) (Z_to_bv 64 (B + L)) WB VN ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDL.
    zstep. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
    zstep. zstep.
    destruct (rfs_first_nul vbs (Z.to_nat L) VN) as (str & rest & EV & NI & LS).
    eapply (rfs_loop str rest (S (length str)) 0%nat vbs); try eassumption; try lia.
    split; [reflexivity|]. split; [intros; reflexivity|]. split; [intros j b0' Hj; lia|]. intros j Hj; exact Hj.
  Qed.

End RFS.

Lemma rfs_call : forall (qq lo0 MP B n L : Z) (vbs sl : list byte) (canary0 : word)
    (ra0 gp0 tp0 t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (F0 : bvmap 5 word) (fc0 : bv 32) (m : mem),
  rw_cells rsegs m MP [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 L)] ->
  rw_cells rsegs m B [CB (Z.to_nat n) vbs] -> nth_error vbs (Z.to_nat L) = Some (Z_to_bv 8 0) -> 0 <= L < n ->
  bytes_at rsegs m (B + n) sl -> (- (B + n)) mod 8 <= Z.of_nat (length sl) ->
  rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary0] ->
  stk rsegs m lo0 qq -> lo0 <= qq - 2288 -> qq <= MP -> MP + 16 <= 2^64 -> MP mod 8 = 0 ->
  0 < B -> L < 2^31 -> B + n + Z.of_nat (length sl) <= lo0 ->
  got_ssp + 8 <= lo0 -> ssp_guard + 8 <= lo0 -> NAD + 8 <= lo0 ->
  (B + n + Z.of_nat (length sl) <= got_ssp \/ got_ssp + 8 <= B) ->
  (B + n + Z.of_nat (length sl) <= ssp_guard \/ ssp_guard + 8 <= B) ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' vbs',
      ms' = MS (mkR ra0 (Z_to_bv 64 qq) gp0 tp0 t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
               F0 (ret_pc ra0) fc0 None m' (seg_rom rsegs)
      /\ munch [(qq - 2288, qq); (B, B + n)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo0 qq
      /\ rw_cells rsegs m' B [CB (Z.to_nat n) vbs']
      /\ (forall j, nth_error vbs j = Some (Z_to_bv 8 0) -> nth_error vbs' j = Some (Z_to_bv 8 0)))
    (MS (mkR ra0 (Z_to_bv 64 qq) gp0 tp0 t0 t1 t2 x8 x9 (Z_to_bv 64 MP) (Z_to_bv 64 NAD) a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F0 (Z_to_bv 64 rfs_entry) fc0 None m (seg_rom rsegs)).
Proof.
  intros until m. intros MPC VB VN LR SLB SLP GOT CAN ST LOD MPQ MPH MPA BP NB SEP SG1 SG2 SG3 SGD1 SGD2 MI.
  pose proof ST as ST'. destruct ST' as (A1 & A2 & _). pose proof VB as V. destruct V as [[WF _] _]. cbn in WF. destruct WF as (W0 & _).
  eapply evt_mono.
  { eapply (rfs_body qq lo0 MP B n L vbs sl canary0 ra0 gp0 tp0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F0 fc0 m); eassumption || lia. }
  intros ms' H. exact H.
Qed.
