(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg ABase AKit ShadowTac ADepot_iface ADepot ADepotKit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition imemcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 : word) (D : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(D, D + Z.of_nat (length src))]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' D [CB (length src) src].

Section Memcpy.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z) (src rest junk : list byte).
  Notation D := (bv_unsigned a0).
  Notation n := (Z.of_nat (length src)).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis SRC : bytes_at bsegs m S (src ++ rest).
  Hypothesis DST : rw_cells bsegs m D [CB (length src) junk].
  Hypothesis A1 : a1 = Z_to_bv 64 S.
  Hypothesis A2 : a2 = Z_to_bv 64 n.
  Hypothesis SEP : (S + Z.of_nat (length (src ++ rest)) <= D \/ D + n <= S)%Z.
  Hypothesis DSMALL : (D + n < 2^63)%Z.
  Hypothesis SSMALL : (S + Z.of_nat (length (src ++ rest)) < 2^63)%Z.
  Hypothesis RS : rng RNG S n.
  Hypothesis RD : rng RNG D n.
  Notation POST := (imemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 D src m).

  (* [comment removed for export] *)
  #[using="rest junk SRC DST SEP DSMALL RS RD"] Lemma imemcpy_loop : forall (k : nat) (i : Z) (mc : word -> option byte) (bs : list byte) x14,
    Z.to_nat (n - i) = k -> (0 <= i < n)%Z ->
    u8arr bsegs mc D bs -> length bs = length src -> (forall j, (j < Z.to_nat i)%nat -> nth_error bs j = nth_error src j) ->
    munch [(D, D + n)]%Z m mc -> wmono bsegs m mc -> mem_inv bsegs mc ->
    evtF bsegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (S + i)) (Z_to_bv 64 (D + n)) (Z_to_bv 64 (D + i)) x14 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x6309c) fc None mc (seg_rom bsegs)).
  Proof.
    pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite length_app in SB.
    Local Ltac2 Set LiaHints.tbl := fun () => "00M0>10364520306.691129708843.72 11799361125.7413708355367.6915404439176.6915410598582.6915416934737.7016747840457.9 1849121282.72 1849121282.74 19526850107.7019526868180.7119622189599.6920506372396.7320506372396.7523153198281.733436568184.69 40649645729.764325898847.69 5120842917.81 57904774905.7257905327519.7259308548577.6759310630224.6459893199455.6967686555271.758611898281.71 8611898281.72 8931259039.69 00000A00X00f01701H01[01o02:02H02V02g03803P03e04:04K04^04_04m05>05N05f06:06K06Y06Z06m07E07]S2DB2SB2Hk2Hi3LBSS2DB2SB2Hk2Hi3LBS1K1n1HS2DB2SB2Hi3LBSS2DB2SB2Hk2Hi3LBSS2DB2SB2Hk2Hi3LBSS2DB2SB2Hk2Hi3LBS1KS2DB2SB2Hk2Hi3LBS2HjS3SEP2DB2SBS2DB2SB2Hi3LBSS2DB2SB2Hi3LBSS2DB2SB2Hk2Hi3LBSS2DB2SB2Hk2Hi3LBSS6DSMALL2DB2SB2Hk2Hi3LBSS6DSMALL2DB2SB2Hi3LBSS6DSMALL2DB2SB2Hi3LBSS2DB2SB2Hk2Hi3LBSS2DB2SB2Hk2Hi3LBS1KFS2DB2SB2Hk3LBSS2DB2SB2Hk2Hi3LBSS2DB2SB2Hk3LBS1HS2DB2SB2Hk2Hi3LBS1K2Hj1nS2DB2SB2Hk2Hi3LBS2NBS2DB2SB2Hk2Hi3LBSS2DB2SB2Hk3LBSFS2DB2SB2Hk2Hi3LBS1nS2DB2SB2Hk2Hi3LBS1K2Hj1nS6DSMALL2DB2SB2Hk2Hi3LBS".
induction k as [|k IH]; intros i mc bs x14 Hk Hi ARR LBS DONE MU WM MI1; [exfalso; lia|].
    destruct (nth_error src (Z.to_nat i)) as [b|] eqn:NB. 2:{ exfalso. apply nth_error_None in NB. lia. }
    assert (SRC1 : bytes_at bsegs mc S (src ++ rest)).
    { eapply bytes_at_transport; [exact SRC | exact MU |]. cbn [disjoint_from]. clear - SEP Hi SB DB. lia. }
    pose proof (u8ro_read bsegs mc S (src ++ rest) i b (wa (S + i)) SRC1 ltac:(rewrite nth_error_app1 by lia; exact NB) ltac:(lia) eq_refl) as RDb.
    zstep. cbv beta.
    pose proof (u8arr_store_ok bsegs mc D bs i (wa (D + i)) ARR ltac:(rewrite LBS; lia) eq_refl) as SOK.
    zstep.
    pose proof (u8arr_write bsegs mc D bs i b ARR ltac:(rewrite LBS; lia)) as ARR'.
    change (le1 (Z_to_bv 64 (bv_unsigned b))) with (le1 (zxb b)). rewrite le1_zxb.
    store_done.
    zstep. zstep. zstep. if_cases K; zify_cond K.
    - replace (D + i + 1)%Z with (D + (i + 1))%Z by lia. replace (S + i + 1)%Z with (S + (i + 1))%Z by lia.
      eapply (IH (i + 1)%Z); [lia | lia | exact ARR' | rewrite Arr.upd_length; exact LBS | | assumption | assumption | assumption].
      + intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)).
        * subst j. rewrite Arr.nth_error_upd_same by (rewrite LBS; lia). symmetry; exact NB.
        * rewrite Arr.nth_error_upd_other by lia. apply DONE. lia.
    - zstep.
      assert (E : upd bs (Z.to_nat i) b = src).
      { apply nth_error_ext. intros j. destruct (Nat.eq_dec j (Z.to_nat i)).
        * subst j. rewrite Arr.nth_error_upd_same by (rewrite LBS; lia). symmetry; exact NB.
        * rewrite Arr.nth_error_upd_other by lia. destruct (Nat.lt_ge_cases j (Z.to_nat i)); [apply DONE; lia|].
          rewrite (proj2 (nth_error_None _ _)) by (rewrite LBS; lia). rewrite (proj2 (nth_error_None _ _)) by lia. reflexivity. }
      rewrite E in ARR'. apply rw_cells_of_u8arr in ARR'. finish.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="S rest junk MI SRC DST A1 A2 SEP DSMALL RS RD"] Lemma imemcpy_body : (1 <= n < 2^64)%Z ->
    evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x63090) fc None m (seg_rom bsegs)).
  Proof.
    intros N1. pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite length_app in SB.
    pose proof (munch_refl [(D, D + n)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM. subst a1 a2.
    zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0080>10640767904.5216077671799.5230823899914.5253004074301.5259308646881.5 60134654234.526625077458.52 67943303862.5200000:00D00K00L00U00V00]00gS2N12DB2SBS2N12DB2SBS2DB2SBFS1K2N12DBFS2DB2SBS2N12DB2SB".
if_cases K; zify_cond K. { exfalso. revert K N1 DB. clear. intros K N1 DB. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    zstep. zstep.
    replace a0 with (Z_to_bv 64 (D + 0)) at 3 by (rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
    replace (Z_to_bv 64 S) with (Z_to_bv 64 (S + 0)) by (f_equal; lia).
    eapply (imemcpy_loop (Z.to_nat n) 0 m junk); try assumption; try lia.
    - eapply u8arr_of_rw_cells. exact DST.
    - pose proof DST as [[WF _] _]. cbn in WF. destruct WF as [WF _]. exact WF.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Memcpy.

#[using="Type"] Lemma imemcpy_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (S : Z) (src rest junk : list byte),
  mem_inv bsegs m -> bytes_at bsegs m S (src ++ rest) -> rw_cells bsegs m (bv_unsigned a0) [CB (length src) junk] ->
  (S + Z.of_nat (length (src ++ rest)) <= bv_unsigned a0 \/ bv_unsigned a0 + Z.of_nat (length src) <= S)%Z ->
  (bv_unsigned a0 + Z.of_nat (length src) < 2^63)%Z -> (S + Z.of_nat (length (src ++ rest)) < 2^63)%Z ->
  (1 <= Z.of_nat (length src) < 2^64)%Z ->
  rng RNG S (Z.of_nat (length src)) -> rng RNG (bv_unsigned a0) (Z.of_nat (length src)) ->
  evtF bsegs RNG (imemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 (bv_unsigned a0) src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length src))) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x63090) fc None m (seg_rom bsegs)).
Proof. intros. eapply imemcpy_body; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; reflexivity. Qed.

(* [comment removed for export] *)
Definition imemcpy_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (D : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(D, D + Z.of_nat (length src))]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' D [CB (length src) src].

#[using="Type"] Lemma imemcpy_specZ : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src rest junk : list byte),
  mem_inv bsegs m -> bytes_at bsegs m S (src ++ rest) -> rw_cells bsegs m D [CB (length src) junk] ->
  n = Z.of_nat (length src) ->
  (S + Z.of_nat (length (src ++ rest)) <= D \/ D + n <= S)%Z ->
  (D + n < 2^63)%Z -> (S + Z.of_nat (length (src ++ rest)) < 2^63)%Z -> (1 <= n)%Z ->
  rng RNG S n -> rng RNG D n ->
  evtF bsegs RNG (imemcpy_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 D src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x63090) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros MI SRC DST -> SEP DS SS N1 RS RD.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  Local Ltac2 Set LiaHints.tbl := fun () => "0020>50463930673.498549018784.48 00000:00DS2DS2N12DBS2DS2N12DB".
assert (U : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  eapply evtF_mono.
  { eapply (imemcpy_body RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S src rest junk);
      rewrite ?U; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try reflexivity; lia. }
  intros ms' P. unfold imemcpy_post in P. rewrite !U in P. exact P.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma amo_add_w_le4 : forall tf cnt, (0 <= tf)%Z -> (0 <= cnt)%Z -> (tf + cnt < 2^32)%Z ->
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 tf)))) (low32 (Z_to_bv 64 cnt))))
  = le4 (Z_to_bv 64 (tf + cnt)).
Proof.
  intros tf cnt H0 H1 H2. unfold le4 at 2. Local Ltac2 Set LiaHints.tbl := fun () => "0070=11597642244.811600047760.641352023633.748466830417.754259705740.655033206788.655041854608.600000:00D00N00X00\00f010S2H02H12H2S2H02H12H2S2H02H12H2S2H02H12H2S2H0S2H02H12H2S2H02H12H2".
rewrite unsigned_lit by lia. f_equal.
  cbn [amo_val]. rewrite bv_add_unsigned.
  assert (E1 : bv_unsigned (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 tf)))) = tf).
  { rewrite bv_extract_unsigned. rewrite le_bytes_to_word_le4. rewrite unsigned_lit by lia.
    rewrite Z.shiftr_0_r. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite !Z.mod_small by lia. reflexivity. }
  assert (E2 : bv_unsigned (low32 (Z_to_bv 64 cnt)) = cnt).
  { unfold low32. rewrite bv_extract_unsigned. rewrite unsigned_lit by lia. rewrite Z.shiftr_0_r.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite Z.mod_small by lia. reflexivity. }
  rewrite E1, E2. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite Z.mod_small by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
End CANSEC1.
Ltac amo_stepW4 :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply (evtF_step_acc segs RNG);
      [ reflexivity
      | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; amo_decide; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | solve_accs
      | simp_regs; vnorm_for i; rewrite amo_add_w_le4 by lia; mem_after_store_opt ]
    end end
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Section Lock.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo B v : Z).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 48)%Z.
  Hypothesis ALO : (AIMG_HI <= lo)%Z.
  Hypothesis A0 : a0 = Z_to_bv 64 B.
  Hypothesis CELL : rw_cells bsegs m B [C4 (Z_to_bv 64 v)].
  Hypothesis BV : (0 <= v < 2^31)%Z.
  Hypothesis BA : (B mod 4 = 0 /\ TAB <= B /\ B + 4 <= NUNIQ)%Z.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RB : rng RNG B 4.

  Definition lock_post : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m' lw,
      ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (B, B + 4)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' B [C4 lw].

  #[using="MI ST LO ALO A0 CELL BV BA RSTK RB"] Lemma lock_body : evtF bsegs RNG lock_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x723e8) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (B, B + 4)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold AIMG_HI, TAB, NUNIQ in *.
    Local Ltac2 Set LiaHints.tbl := fun () => "0180>13172413352.5213624457060.6613624457062.581800609155.61 1800609155.69 19042827563.6420268442745.6122387597248.6024638473347.6124638473347.6725073575915.6125073575915.6225073575915.6425073575915.6525365921608.6227147338155.6327907155492.5928072922155.6128406852928.6229431497298.6729442629968.5729442630097.5529442630230.5931378308326.5331378620384.5832164731367.6032164731367.6534440526528.6335188928243.6037452664998.5437454847525.5640460011584.6240600968423.6040600968426.6841991641667.5742630527489.5543057221392.5143988483203.5943988483203.6745299709328.5545848756903.5946462227904.6249649769127.6250036301095.5951469103432.6451711223320.585187432548.61 5187432548.66 52105090727.6153043216584.6453459164111.6553469114889.5753471300778.5654243526019.6154243526019.665576237813.64 5584011775.57 5586288476.56 59308628304.3 59308628433.2 59308628566.1 59308628695.2 60858483367.6163104122952.6563305555623.6164997134979.6264997134979.6765212743211.6365495973220.6665495973223.608603416747.63 9248820168.64 00000400500600700800<00G00K00L00M00N00O00P00Q00\00`00d00h00l01001701;01B01C01D01E01F01J01N01R01V01Z01[01\01]01a01e01f01g01k01l02002102502@02A02B02C02D02O02P02Q02R02S02T02U02V02W02^02b02f02j02k03603703803903=03>03?03C03NS2LOSSSSS2HBS2LO3ALO2BAS2HBSSSSSSS2LO3ALO2BAS2HBS2LOS2HBS2HBS2BVS2K22BVS2BVS2BV2K4SSSSS2HBS2HBS2BVS2BVS2HBSSSS2BAS2LOSSS2BASS2HBSS2HBS2LO3ALO2BASSSSS2LO3ALO2BASSSSSSSSS2BV2K1S2K2S2K3S2K4SS2LO3ALO2BASSSS2HBSSS2HBS2LO3ALO2BA".
assert (RSTK' : rng RNG (bv_unsigned sp + -48) 48) by (eapply rng_sub'; [exact RSTK| lia]).
    subst a0. carve_frame 48%nat ST.
    do 10 zstep. zstep. rewrite sx32_lit by lia.
    zstep. if_cases K1; zify_cond K1. 2:{ exfalso. clear - BV K1. lia. }
    zstep.
    assert (AMO : amo_aligned AW (Z_to_bv 64 B) = true) by (apply amo_alignedW_intro; [lia| lia]).
    amo_stepA AMO. rewrite sx32_lit by lia.
    zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. lia. }
    amo_stepA AMO.
    zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3. cbv in K3. lia. }
    zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. lia. }
    do 7 zstep.
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. unfold lock_post.
    replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z by lia.
    do 16 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. all: match goal with H : rw_cells bsegs _ B ?c |- _ => idtac c; exact H end.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Lock.

(* [comment removed for export] *)
End CANSEC2.
Ltac shr0 :=
  repeat match goal with |- context [Z.shiftr ?x ?k] =>
    replace (Z.shiftr x k) with 0%Z by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia) end.


Section CANSEC3. Context {rc : runConstT}.
Section NStoreFile.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section NStore.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (lo NDp AR T sz tf STORE : Z) (HW : word) (tb : list word) (jn jl js jh jf : list byte).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 112)%Z.
  Hypothesis ALO : (ATOP <= lo)%Z.
  Hypothesis A0 : a0 = Z_to_bv 64 NDp.
  Hypothesis A2 : a2 = Z_to_bv 64 AR.
  Hypothesis A3 : a3 = HW.
  Hypothesis ARGS : rw_cells bsegs m AR [C8 (Z_to_bv 64 T); C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 0)].
  Hypothesis ARB : (bv_unsigned sp <= AR /\ AR + 16 <= 2^47)%Z.
  Hypothesis NODE : rw_cells bsegs m NDp [CB 8 jn; CB 4 jl; CB 4 js].
  Hypothesis CTF : rw_cells bsegs m SSTF [C8 (Z_to_bv 64 tf)].
  Hypothesis CPTR : rw_cells bsegs m SSPTR [C8 (Z_to_bv 64 STORE)].
  Hypothesis CST : rw_cells bsegs m SSST [C4 (Z_to_bv 64 tf)].
  Hypothesis FRAMES : rw_cells bsegs m (STORE + 8 * tf) [CB 8 jh; CB (Z.to_nat (8 * sz)) jf].
  Hypothesis TB : u64arr bsegs m T tb.
  Hypothesis LTB : length tb = 255%nat.
  Hypothesis SZ : (1 <= sz <= 255)%Z.
  Hypothesis TF : (0 <= tf /\ tf + sz + 1 < 1048576)%Z.
  Hypothesis TBB : (bv_unsigned sp <= T /\ T + 2040 <= 2^47)%Z.
  Hypothesis NDB : (AIMG_HI <= NDp /\ NDp + 16 <= ATOP /\ NDp mod 16 = 0)%Z.
  Hypothesis STOB : (AIMG_HI <= STORE /\ STORE + 8388608 <= ATOP /\ STORE mod 4096 = 0)%Z.
  Hypothesis SEPNS : (NDp + 16 <= STORE + 8 * tf \/ STORE + 8 * (tf + sz + 1) <= NDp)%Z.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RAR : rng RNG AR 16.
  Hypothesis RND : rng RNG NDp 16.
  Hypothesis RFR : rng RNG (STORE + 8 * tf) (8 * (sz + 1)).
  Hypothesis RT : rng RNG T 2040.

  Definition nstore_post : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (NDp, NDp + 16); (SSTF, SSTF + 8); (SSST, SSST + 4); (STORE + 8 * tf, STORE + 8 * tf + 8 * (sz + 1))]%Z m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' NDp [C8 HW; CB 4 jl; C4 (Z_to_bv 64 (tf + 1))]
      /\ rw_cells bsegs m' SSTF [C8 (Z_to_bv 64 (tf + sz + 1))]
      /\ rw_cells bsegs m' SSST [C4 (Z_to_bv 64 (tf + sz + 1))]
      /\ rw_cells bsegs m' (STORE + 8 * tf) [C8 (Z_to_bv 64 sz); CB (Z.to_nat (8 * sz)) (firstn (Z.to_nat (8 * sz)) (u64s tb))]
      /\ rw_cells bsegs m' AR [C8 (Z_to_bv 64 T); C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 0)].

  #[using="rc jn js jh jf MI ST LO ALO A0 A2 A3 ARGS ARB NODE CTF CPTR CST FRAMES TB LTB SZ TF TBB NDB STOB SEPNS RI RSTK RAR RND RFR RT"] Lemma nstore_body : evtF bsegs RNG nstore_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x7196c) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp); (NDp, NDp + 16); (SSTF, SSTF + 8); (SSST, SSST + 4); (STORE + 8 * tf, STORE + 8 * tf + 8 * (sz + 1))]%Z m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold AIMG_HI, SSTF, SSPTR, SSST in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    Local Ltac2 Set LiaHints.tbl := fun () => "06>0?10095167155.11810095167155.99 10255843992.95 10411647463.95 10489398501.10211077935948.95 11362458803.97 11593749418.10511593749418.92 11688375624.11811801586693.10911801586693.1101203282236.94  12587650279.89 12587650282.11412642784408.95 12701873968.95 13098894204.10413303305455.94 13482237428.94 13520218209.87 13520218212.95 13520218213.11213520218216.11513520218219.11413620867140.10014236670872.95 1508639646.105 15092166424.97 15104381976.91 15104381976.97 15149862570.10515422468449.93 15604312956.1081560509925.100 1560509925.96  1560509931.114 16004731724.98 16007310588.10516072396420.94 17088274784.10217103458764.93 17223795648.89 17288173208.93 17288173208.95 17755953380.97 17909413921.11118045588882.94 18118171189.10918125223772.97 18239100277.94 18446219239.11018446219239.91 19042827563.90 19042827563.96 19338285270.10519338285270.91 19373511525.93 19373511528.11519589112390.10519636467608.95 19680783712.11519680783712.93 21028037403.3  21270506136.95 21309753520.91 21309753520.96 21309753520.99 21418632967.94 21484770583.10021680067508.10821764122956.11621764122956.89 21764122956.97 21848846242.10221894104544.11521894104544.89 2221946199.102 23077509607.10323077509607.99 23122445900.95 23223914816.91 23889028584.95 23993334155.10123993334155.98 24224200420.94 24499257512.1082492914022.95  2492914022.98  24983023919.10825048463044.97 25119755800.11825119755800.91 25119755800.96 25119755800.99 2525449496.118 2525449496.91  2525449496.96  2525449496.99  25464565985.96 25624113075.97 25628751800.11125826858776.91 25826858776.97 2597469155.114 26180746584.93 26180746584.95 26353760792.97 26521015384.95 26943471331.11827141788524.10927147338155.92 27147338155.94 27679091076.83 27780997068.91 2803919340.100 2803919340.104 28072922155.96 28082336400.11828119612256.11528119612256.93 28630498355.95 28980082218.10428990961846.94 29032285152.11429032285152.92 29056984305.10229090419458.10929141972172.93 29267190616.11829469427431.96 29469427431.99 29756005259.10229756005259.11429756005259.11629756005259.98 29782367974.10030024882249.10730541626225.92 305622464.92   30640719399.95 31065366849.10831065366849.11031105608828.94 31161366443.94 31259190279.97 31352001640.91 31352001640.97 31688689248.11231688689248.93 31874498834.10132907263168.94 3317750039.100 3317750039.104 33183415099.98 33203879240.11833508037984.11633508037984.91 34135153417.93 34290115814.82 34642181227.10234830683292.10034830683292.10434943365921.96 349669172.118  34985880335.10935158841676.94 35291343393.11135814319382.10435835696073.10935863348660.10836004693060.11036380065980.1083660419288.118 3660419288.91  3660419288.96  3660419288.99  36960507030.91 36986663037.10837047490023.99 37062796780.10037062796780.10437453426021.11237453426022.90 37502248088.93 37502248088.95 39545954992.97 39939243268.10340373330341.11240613224310.98 40852972392.97 41169553244.86 41178353612.93 41345759113.11141513302182.10541514416856.97 41564619544.10241809465927.85 41900557288.93 41900557288.95 42116106735.94 42957278038.94 43055432124.80 43152703000.94 43190871063.10443303441508.92 43303441512.11543407189580.10243407189580.98 44021460374.92 44085631722.91 44304791951.10944484923210.10844631688216.91 44631688216.97 44700995416.95 44708047596.93 44725753788.10044725753788.10444805171356.97 44960421824.95 44973188593.10645015350225.10545090362644.10045090362644.10445093806515.94 45236992039.10745487759923.95 45667945696.10045667945696.97 45857202116.11846235924760.11846235924760.91 46235924760.96 46235924760.99 46355298535.91 46355298538.11346722908207.10847196384886.11447334819512.11147399595340.97 47474589859.10947700500248.97 48276508316.97 48475049000.10549641221712.11850027952920.91 50027952920.97 50221560344.94 50633028432.93 50664164139.93 50977580352.93 51423379376.10551438510464.11451544965601.1115170374848.116 5170374848.89  5170374848.97  51896122520.95 52260433120.11752260433120.94 52281016680.11852281016680.91 52281016680.96 52281016680.99 52504176569.10052577538839.10052577538839.10452577538839.10852577538839.11152577538839.11852577538839.91 52577538839.93 52577538839.94 52577538839.95 52577538839.96 52577538839.97 52577538839.99 52683723224.94 53270529432.93 53270529432.95 53408145191.1045372288304.93  5372288304.95  54247636400.94 54330877797.11354330877798.87 54437333272.94 5496416704.97  55034195860.10155034195860.11255034195865.10155034195866.11455034195867.10055036293010.11655475721960.95 55756264419.11855770193284.88 5580625880.91  5580625880.97  55890146712.95 55946304394.10255955194800.91 55955194800.97 56459965173.11656815227425.11156834611108.10856980320960.95 57091798963.11857226951348.10857241388115.10557347395742.11857404317676.10057404317676.10458872313774.11459308628304.3  59308628433.1  59308628695.1  59308628820.1  59308629211.1  59314873579.5  59314873579.8  59382398767.10559586081460.11260283127279.94 60324194812.10160511600900.10460647885491.96 60647885491.99 60698737376.11860698737376.95 60853221185.98 61328998664.11461335917969.11161448802292.94 62048608059.10262048608059.98 62077860332.10062077860332.10462999281728.93 63242030569.11063332853404.97 63401989926.10063401989931.10663404087074.97 63409910945.86 63409911719.89 6341393216.93  63620716339.95 63887030421.11764233206808.97 64267814368.11764267814368.95 64426527463.91 64426527466.11364871668375.11164877476912.95 65178518140.10365212743211.11765212743211.90 65212743211.95 65212743211.98 65360148067.11665362245221.93 65501840056.11165504523926.10565510090920.11265673334344.11866077201632.11466077201632.11666077201632.11766077201632.89 66077201632.97 66487633944.11866487633944.91 66487633944.96 66487633944.99 67760998476.92 6816265519.108 6818787088.83  68460123752.94 6983718313.95  7825307013.101 7901778387.104 8079916440.95  8158244420.90  8200089752.93  8200089752.95  8232114456.94  8603416747.94  8759927523.118 8894204422.94  8897956419.105 8935173666.116 8937270820.112 9405451517.108 9559035261.109 9719060044.89  00000500:00O00T00j00o01401M01a01o02S02T02d02i03303?03Z03d04004504:04?04I04S04]05305?05@05L05X05d05e05j06:06?06D06N06V06o07@07V07[07c07o08;08T08i08n09Z0:10:K0:U0:Z0:c0:l0;60;;0;@0;J0;c0;o0<90<>0<E0<Q0<l0=G0=b0=g0=l0>10>;0>@0>E0>d0>n0?30?I0?R0?[0?`0?h0@10@60@;0@D0@^0@c0@h0A40AM0Ag0B<0BQ0Bf0C20C>0CJ0CV0C^0Cc0DB0DN0DZ0Dd0Dm0E60EB0EK0Ee0Ej0F30F<0FD0FI0FU0Fa0Fj0GH0GR0GW0G\0HH0H\0Hf0Hk0IS0I[0I`0J>0JC0JH0JM0JW0Ja0Jf0K00K50K:0KB0KG0Ko0LW0Lg0M00ME0MN0MW0Ma0Mf0N00N80N=0NB0NG0NU0N_0Nd0Ni0Nn0O30O<0OE0OJ0On0P30P80PM0PW0P\0Pa0Pi0Q90QB0QK0QT0Q]0R10RK0R_0Rk0S70SA0SF0S[0T00TK0TX0Tb0Tg0U00U80U=0U`0Ua0Uj0V40V90VB0VK0VW0V\0Vd0W00W50W:0WD0WL0WT0WY0Wm0XU0Y60YB0YN0YW0Y\0Z10ZF0ZO0ZW0Z\0[50[>0[G0[L0[]0[b0[g0[l0\X0\d0]00]<0]H0]M0]W0]c0]m0^L0^Q0^R0^^0^g0_40_]0`20`G0`S0`a0`j0a20a?0aL0b30b;0bC0bK0bW0ba0bf0bo0c80cA0cJ0cO0cT0cY0c^0d40d90d>0dC0dH0dM0dR0dW0d\0de0e10e=0ec0f>0fY0g40g>0gC0gO0gW0gk0hD0hX0i10iE0i^0ig0jD0jL0jU0j^0jj0kI0kd0l?0lG0l\0lj0m20m70mQ0m[0n?0nZ0o50o60o=0oA0oE0oI0oM0oV0ob0oo10910E10O10\10a10f11011511F11P12312812=12B12N12Z12b12c12l13413<13D13L13T13\13a13i14>14H14M14R14\14a15<15F15O15X15a15j16416916X16b16l17:17D17N17X17]17b17n18:18F18R18W18c18k19419<19U1:;1:P1:U1:a1:m1;B1;K1;e1;j1<71<P1<i1=C1=]1=bS3LTBS3LTBS2LO3ALO3LTB3NDB4STOBS3LTBS3LTB2SZ3NDB4STOB4LSRCS3LTBS3LTBS3LTB2SZ2TF3NDB4STOB4LSRCS3LTB2SZ2TF3NDB4STOBS3LTB3NDB4LSRCS2LO3ALO3EFA3LTB2SZ2TF3NDB4STOB4LSRCFS2LO3ALO3LTB3TBBS3LTBS3LTB4LSRCS2LO3ALO3LTBS2LO3ALO3LTB2SZ2TF3NDB4STOBS3LTB4LSRCS2LO3ALO3LTBS3LTBS3LTBS3LTBS3LTB4LSRCS3LTB4LSRCS3LTB4LSRCS3LTB2SZ3NDB4STOB4LSRCS2LO3ALO3LTBFS2LO3ALO3LTBS2LO3ALO3LTBS2LO3ALO3LTBFS3LTBS2LO3ALO3LTB3TBBS3LTBS3LTBS3LTB4LSRCS3LTB2HBS3LTB2SZ2TF3NDB4STOB4LSRCS3LTB2TF3NDB4STOBS3LTB2SZ3NDB4STOB4LSRCS3LTBS3LTB2HBS2LO3ALO3LTBS2LO3ALO3LTBS2LO3ALO3LTB3TBB3NDB4STOBS3EFA3LTB2TF3NDB4STOBS3LTBS3EFA3LTB2SZ2TF3NDB4STOB5SEPNS2K12K62K74LSRCS3LTB2SZ3NDB4STOB5SEPNSS3LTB2SZ2TF3NDB4STOB5SEPNSS3LTB4LSRCS3LTBS3LTB3SPRS3LTB3SPRS3LTB4LSRCS3LTBS3LTBS3LTB4LSRCS3LTB2SZ2TF3NDB4STOB4LSRCS2LO3ALO3LTBS3LTB4LSRCS3LTBS2SZ2K3S2LO3ALO3LTBS2LO3ALO3LTB2SZ2TF3NDB4STOBS2LO3ALO3LTB2SZ2TF3NDB4STOBS2LO3ALO3LTB2SZ2TF3NDB4STOBS3LTBS3LTBS3LTBS3LTB4LSRCS3LTBS3LTBS3LTB2SZ2TF3TBB3NDB4STOB4LSRC1HS3LTB4LSRCS3LTBS3LTB2SZ3NDB4STOB4LSRCS3LTB3SPRS3LTB3SPRS3LTBS3LTB2HBS3ARB3LTBS3LTBS3LTBS3LTB3NDBS3EFA3LTB2TF3NDB4STOB4LSRCS3LTBS3LTBS2LO3ALO3LTBS2LO3ALO3ARB3LTB3NDB4STOBS2LO3ALO3LTB3NDB4STOB4LSRCS2LO3ALO3LTB3NDB4STOBS2LO3ALO3LTB3NDB4STOBS2LO3ALO3LTB3NDB4STOBS2LO3ALO3LTBS2LO3ALO3LTBS2LO3ALO3LTBS2LO3ALO3LTBS3LTB2HBS3LTBS2LO3ALO3EFA3LTB2SZ2TF3NDB4STOBS2LO3ALO3LTBS2LO3ALO3LTBS3LTB4LSRCS3LTB3TBBS3LTB3TBBS2LO3ALO3LTBS3LTB3TBBS2LO3ALO3LTB3NDB4STOB4LSRCS3LTBS3LTB3SPRS3LTB3SPRS2LO3LTBS3LTBS2LO3ALO3LTBS2LO3ALO3LTBS3LTB3SPRS2LO3ALO3LTB3TBB3NDB4STOB4LSRCS3LTB4LSRCS3LTBS3LTBS3EFA3LTB2SZ2TF3NDB4STOB5SEPNS2K12K62K74LSRCS3LTB2SZ2TF3NDB4STOBS3LTB4LSRCS3LTBS2LO3ALO3EFA3LTB2SZ2TF3TBB3NDB4STOB4LSRCS3LTB2HBS3LTBS2LO3ALO3ARB3LTB3NDB4STOB4LSRCS3LTBS3LTBS3LTBS3LTB4LSRCS3LTB4LSRCS3LTBS3LTB4LSRCS3LTBS3LTBS3LTB2HBS3LTBS2LO3ALO3EFA3LTB2SZ2TF3TBB3NDB4STOB4LSRCS2LO3ALO3EFA3LTB2SZ2TF3TBB3NDB4STOB4LSRCS2LO3ALO3ARB3LTBS3LTB3SPRS2LO3ALO3LTB3NDB4STOBS3ARB3LTBS3ARB3LTBS3LTB4LSRCS3LTBS3LTB4LSRCS3LTB2HBS3LTBS3LTBS3LTBS3LTB3NDB4LSRCS3LTB4LSRCS3LTBS3LTBS3LTBS3LTBS3LTB3TBBS3LTB3TBBS3LTBS2LO3ALO3EFA3LTB2SZ2TF3NDB4STOB4LSRCS3LTBS3LTBS3EFA3LTB2TF3NDB4STOBS3LTB4LSRCS3LTBS3LTBS3LTB2HBS2LO3ALO3ARB3LTBS3LTB3TBBS3LTB3TBBS3LTB3TBBS3LTB3TBBS3LTB2SZ2TF3NDB4STOBS3EFA3LTB2TF3NDB4STOB4LSRCS3LTB2SZ2TF3NDB4STOBS2LO3ALO3LTBS2LO3ALO3LTBS3LTB4LSRCS3LTBS2LO3ALO3LTB3NDB4STOBS2LO3ALO3LTB3NDB4STOBS2LO3ALO3LTB2SZ2TF3NDB4STOBS2LO3LTB4LSRCS3LTB4LSRCS3LTBS3ARB3LTBS3LTB2SZS3LTBS2LO3ALO3EFA3LTB2SZ2TF3TBB3NDB4STOBFS3LTB3TBBS3LTB4LSRCS3LTBS3ARB3LTBS3ARB3LTBS2LO3ALO3LTBS3LTBS2LO3LTBS2LO3ALO3LTBS3LTBS3LTBS3LTB4LSRCS3LTB2HBS3LTB2HBS3LTBS3LTB2SZ2TF3NDB4STOBS2LO3ALO3ARB3EFA3LTB2SZ2TF3NDB4STOB4LSRCS3ALO3EFA3LTB2SZ2TF3NDB4STOB4LSRCS2LO3ALO3LTBS2LO3ALO3LTBS3LTB3TBBS3LTBS2LO3ALO3LTB3NDB4STOBS2LO3ALO3LTB3NDB4STOBS3LTB3NDBS3LTB2HBS3LTBS3LTB2SZ2TF3NDB4STOB4LSRCS3ARB3LTBS3ARB3LTBS3LTBS3LTB2SZ3NDB4STOBS3LTBS3LTBS3LTBS3EFA3LTB2SZ2TF3NDB4STOB5SEPNS2K12K62K74LSRCS2LO3ALO3LTBS2LO3ALO3LTBS2LO3ALO3LTBS2LO3ALO3LTBS3LTBS3LTB4LSRCS2LO3ALO3LTBS3LTB4LSRCS2LO3ALO3EFA3LTB2SZ2TF3NDB4STOBS3LTBFS2LO3ALO3LTBS3LTB3NDBS2LO3LTB4LSRCS3EFA3LTB2SZ3NDB4STOB5SEPNS2K12K62K74LSRCS2LO3ALO3LTB3NDB4STOBS2LO3ALO3LTB3NDB4STOBS2LO3ALO3LTBS3LTB3NDB4STOBS3LTB3SPRS3LTB2HBS3LTB2TF4LSRCS3LTB2TF4LSRCS3EFA3LTB2SZ3NDB4STOB5SEPNS2K12K62K72HBS3LTB2HBS3LTB2HBS3LTB2HBS2LO3ALO3LTBS3LTB4LSRCS3LTBS3ARB3LTBS3ARB3LTBS3ARB3LTBS3ARB3LTBS3LTBS3LTBS3LTBS3LTBS2LO3ALO3EFA3LTB2SZ2TFS3LTBS3LTBS3LTBS3LTBS3LTBS3LTBS3LTBS3LTBS3LTB3TBBS2LO3ALO3LTBS2LO3ALO3LTBS3EFA3LTB2SZ2TF3NDB4STOB2K12K62K74LSRCS2LO3ALO3LTB2SZ2TF3NDB4STOBS2LO3ALO3LTB2SZ2TF3NDB4STOBS2LO3ALO3LTB2SZ2TF3NDB4STOBS3LTB4LSRCS3LTBS2LO3ALO3LTBS3LTB2HBS3LTB2SZ2TF3NDB4STOBS3LTB2SZ2TF3NDB4STOB4LSRCS3LTB2SZ2TF3NDB4STOBS3LTB2SZ2TF3NDB4STOB4LSRCS3LTB2SZ2TF3NDB4STOBS3LTB2SZ2TF3NDB4STOB4LSRCS3ARB3LTBS2LO3ALO3LTB2SZ3NDB4STOB4LSRCS2LO3LTBS3LTB3TBBS3LTB3TBBS2LO3ALO3LTBS3EFA3LTB2SZ2TF3NDB4STOB4LSRC1HS2LO3ALO3LTB2SZ2TF3NDB4STOBS2LO3ALO3LTB2SZ2TF3NDB4STOBS3LTB2HBS3EFA3LTB2TF3NDB4STOBS3LTB3NDB4LSRCS3LTB2HBS3LTBS3EFA3LTB2TF3NDB4STOB4LSRCS3LTB4LSRCS2LO3ALO3EFA3LTB2SZ2TF3NDB4STOB4LSRCS2LO3ALO3LTB2SZ2TF3NDB4STOBS2LO3ALO3LTB2SZ2TF3NDB4STOBFS2SZ2K1S2K2S2K4S2K5S2K8S4STOB2K6S2TF4STOB2K7S3LTB2SZ4LSRCS3LTB4LSRCS2LO3ALO3LTBS3LTB4LSRCS2LO3LTB4LSRCS3LTBS3LTBS3LTB4LSRCS3LTBS3LTB2SZ3NDB4STOBS3LTB4LSRCS2LO3ALO3ARB3EFA3LTB2SZ2TF3NDB4STOBS3LTBS3LTBS3LTBS2LO3ALO3LTBS2LO3ALO3LTBS3LTB2HBFS3LTB3NDBS3LTB2SZS3LTB2SZS3LTB2SZS3LTB2SZS3LTB2SZS3LTB2HBS3LTBS3LTB2HBS2LO3ALO3LTB3NDB4STOBS3LTB4LSRCS3LTBS3LTBS3LTB4LSRCS3LTBS2LO3ALO3LTB2SZ2TF3NDB4STOBS3LTB4LSRCS3LTB3SPRS3LTB3SPRS3LTB3SPRS3LTB3SPRS3LTB4LSRCS3LTBS2LO3ALO3EFA3LTB2SZ2TF3NDB4STOBS3LTB4LSRCS3LTB4LSRCS3LTB3NDB4LSRCS3LTB4LSRCS3LTB4LSRCS3LTB4LSRCS3LTBS3LTBS2LO3ALO3LTBS2LO3ALO3LTBS2LO3ALO3LTBS2LO3ALO3LTBS3LTBS2LO3ALO3LTBS2LO3LTBS3ARB3LTBS3LTB2HBS3LTB2SZ2TF3NDB4STOB4LSRCS3EFA3LTB2SZ2TF3NDB4STOB2K12K62K74LSRCS2LO3ALO3LTB3NDB4STOBS3LTBS2LO3ALO3LTBS2LO3ALO3LTBS2LO3ALO3LTB3NDB4STOBS3LTB3SPRS2LO3ALO3LTB3NDB4STOB4LSRCS3LTBS3LTB2TF4LSRCS3LTB2SZ2TF3NDB4STOB4LSRCS3LTB2SZ2TF3NDB4STOB4LSRCS3EFA3LTB2TF3NDB4STOB4LSRCS3EFA3LTB2TF3NDB4STOB4LSRCS3LTB".
assert (RSTK' : rng RNG (bv_unsigned sp + -112) 112) by (eapply rng_sub'; [exact RSTK| lia]).
    subst a0 a2 a3.
    change (?P) with (sf_hide P) in SEPNS.
    pose proof FRAMES as FRM. change (?P) with (sf_hide P) in FRAMES. pose proof NODE as NDC. change (?P) with (sf_hide P) in NODE.
    pose proof ARGS as ARGC. change (?P) with (sf_hide P) in ARGS.
    carve_frame 32%nat ST.
    do 10 zstep. zstep.
    (* [comment removed for export] *)
    carve_frame 64%nat ST.
    do 9 zstep. zstep. rewrite sx32_lit by lia. zstep. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). zstep. fold_lits.
    rewrite Z.lor_0_r. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. clear -K1 SZ. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. lia. }
    zstep. zstep.
    (* [comment removed for export] *)
    let x1 := reg_val 1%Z in let x2 := reg_val 2%Z in let x5 := reg_val 5%Z in let x6 := reg_val 6%Z in let x7 := reg_val 7%Z in
    let x8 := reg_val 8%Z in let x9 := reg_val 9%Z in let x11 := reg_val 11%Z in let x12 := reg_val 12%Z in let x13 := reg_val 13%Z in
    let x14 := reg_val 14%Z in let x15 := reg_val 15%Z in let x16 := reg_val 16%Z in let x17 := reg_val 17%Z in let x18 := reg_val 18%Z in
    let x19 := reg_val 19%Z in let x20 := reg_val 20%Z in let x21 := reg_val 21%Z in let x28 := reg_val 28%Z in let x29 := reg_val 29%Z in
    let x30 := reg_val 30%Z in let x31 := reg_val 31%Z in
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (REST : forall x10, evtF bsegs RNG nstore_post (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                 F (Z_to_bv 64 0x6f6b0) fc None mc (seg_rom bsegs)))
    end.
    2:{ zstep. if_cases K3; zify_cond K3; [apply REST|]. zstep. replace (Z_to_bv 64 255) with (Z_to_bv 64 sz) by (f_equal; clear -K3 SZ; lia). apply REST. }
    intros x10.
    zstep. zstep. zstep. do 4 zstep. zstep.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    do 5 zstep. amo_step.
    zstep. zstep. shr0. zstep. zstep. shr0.
    zstep. if_cases K4; zify_cond K4. { exfalso. clear -K4. lia. }
    zstep. shr0.
    zstep. if_cases K5; zify_cond K5. 2:{ exfalso. clear -K5. lia. }
    zstep. zstep. zstep. zstep. zstep. if_cases K6; zify_cond K6. { exfalso. clear -K6 STOB. unfold AIMG_HI in STOB. lia. }
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    match goal with |- context [Z.shiftr ?e 41] =>
      replace (Z.shiftr e 41) with (8 * tf)%Z
        by (rewrite Z.shiftl_mul_pow2 by lia;
            first [ change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia
                  | change 18446744073709551616%Z with (2^64)%Z ];
            rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia;
            change (2^44)%Z with (8 * 2^41)%Z; rewrite Z.mul_assoc, Z.div_mul by lia; lia)
    end.
    do 3 zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K7; zify_cond K7. { exfalso. clear -K7 STOB TF. unfold AIMG_HI in STOB. lia. }
    zstep. zstep. zstep. rewrite Z.lor_0_l.
    apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FRM. destruct FRM as [FRM FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR2.
    remember (STORE + 8 * tf)%Z as FA eqn:EFA.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    set (SRC := firstn (Z.to_nat (8 * sz)) (u64s tb)).
    assert (LSRC : length SRC = Z.to_nat (8 * sz)) by (subst SRC; rewrite firstn_length, u64s_length, LTB; lia).
    replace (Z.shiftl sz 3) with (Z.of_nat (length SRC)) by (rewrite LSRC, Z.shiftl_mul_pow2 by lia; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (TBc : bytes_at bsegs mc T (SRC ++ skipn (Z.to_nat (8 * sz)) (u64s tb)))
        by (subst SRC; rewrite firstn_skipn; match goal with H : u64arr bsegs mc T tb |- _ => exact (proj1 H) end);
      assert (DSTc : rw_cells bsegs mc (FA + 8) [CB (length SRC) jf]) by (rewrite LSRC; assumption)
    end.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evtF_cut;
      [ eapply (imemcpy_specZ RNG) with (src := SRC) (rest := skipn (Z.to_nat (8 * sz)) (u64s tb)) (junk := jf);
        [ eassumption | exact TBc | exact DSTc | reflexivity
        | rewrite length_app, skipn_length, u64s_length, LTB, LSRC; unfold sf_hide in *; lia
        | rewrite LSRC; lia | rewrite length_app, skipn_length, u64s_length, LTB, LSRC; lia | rewrite LSRC; lia
        | rewrite LSRC; eapply rng_sub'; [exact RT | lia] | rewrite LSRC; eapply rng_sub'; [exact RFR | lia] ]
      | (post_call bsegs mc) ]
    end.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (Z.land (Z.shiftr tf 16) 18446744073709551600) with 0%Z.
    2:{ change 18446744073709551600%Z with (2^64 - 2^4)%Z. rewrite land_align_down by (shr0; try lia; rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
        rewrite Z.shiftr_div_pow2 by lia. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    zstep. zstep. fold_lits. amo_stepW4. rewrite sx32_lit by lia.
    zstep. zstep. zstep. shr0.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    match goal with H : rw_cells bsegs _ (bv_unsigned sp + -96) (C8 (Z_to_bv 64 tf) :: ?rest) |- _ =>
      apply (rw_cells_C8_C4C4 bsegs _ _ [] rest tf) in H; [cbn [app] in H | lia] end.
    zstep. rewrite sx32_lit by lia. zstep.
    (* [comment removed for export] *)
    setreg 10%Z (Z_to_bv 64 0)
      ltac:(f_equal; symmetry;
            match goal with |- Z.b2z (Z.lxor ?y 1048576 <? 1)%Z = 0%Z =>
              replace y with (sz + 1 + tf)%Z
                by (try change 4294967295%Z with (Z.ones 32); try change 18446744073709551615%Z with (Z.ones 64);
                    rewrite ?Z.land_ones by lia; try change (2^32)%Z with 4294967296%Z; try change (2^64)%Z with 18446744073709551616%Z;
                    symmetry; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia) end;
            change 1048576%Z with (2^20)%Z; rewrite zb_lxor_pow2_small by lia;
            replace (_ <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
    zstep. zstep. zstep. try rewrite sx32_lit by lia.
    (* [comment removed for export] *)
    do 9 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K8; zify_cond K8. { exfalso. clear -K8. lia. }
    do 4 zstep.
    match goal with FR1 : rw_cells bsegs _ (bv_unsigned sp + -112) _, ST : stk bsegs _ lo _ |- _ => release_frame FR1 ST (bv_unsigned sp + -96)%Z end.
    match goal with FR0 : rw_cells bsegs _ (bv_unsigned sp + -96) _, ST : stk bsegs _ lo _ |- _ => release_frame FR0 ST (bv_unsigned sp + -32)%Z end.
    match goal with FR : rw_cells bsegs _ (bv_unsigned sp + -32) _, ST : stk bsegs _ lo _ |- _ => release_frame FR ST (bv_unsigned sp) end.
    match goal with CTF : rw_cells bsegs _ 1519368 _ |- _ => cbn [amo_val] in CTF; rewrite lit_add_lit in CTF end.
    apply evtF_done. unfold nstore_post. subst FA. unfold sf_hide in *.
    replace (bv_unsigned sp - 112)%Z with (bv_unsigned sp + -112)%Z by lia.
    replace (tf + (sz + 1))%Z with (tf + sz + 1)%Z in * by lia.
    do 16 eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try assumption.
    - match goal with H : rw_cells bsegs _ NDp _ |- _ =>
        rewrite bv_swrap_small in H by (change (bv_half_modulus 32) with 2147483648%Z; lia); exact H end.
    - fold SRC. apply (proj2 (rw_cells_app bsegs _ _ [_] _)). split; [assumption|].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite <- LSRC. assumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End NStore.
End NStoreFile.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section HashLoop.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (T sz : Z) (tb : list word).
  Hypothesis TB : u64arr bsegs m T tb.
  Hypothesis LTB : length tb = 255%nat.
  Hypothesis SZ : (1 <= sz <= 255)%Z.
  Hypothesis TBB : (0 <= T /\ T + 2040 <= 2^47)%Z.
  Hypothesis RT : rng RNG T 2040.

  #[using="TB LTB SZ TBB RT"] Lemma hash_loop : forall (k : nat) (i h : Z) x15 x16 (Q : machine_state -> Prop),
    Z.to_nat (sz - i) = k -> (0 <= i < sz)%Z -> (0 <= h < 2^64)%Z ->
    (forall x15' x16',
       evtF bsegs RNG Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 14313749767032793493) (Z_to_bv 64 (T + 8 * sz))
                  (Z_to_bv 64 (mz_adds h (map bv_unsigned (firstn (Z.to_nat (sz - i)) (skipn (Z.to_nat i) tb)))))
                  a3 (Z_to_bv 64 (T + 8 * sz)) x15' x16' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x71d28) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 14313749767032793493) (Z_to_bv 64 (T + 8 * i)) (Z_to_bv 64 h)
               a3 (Z_to_bv 64 (T + 8 * sz)) x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x71d04) fc None m (seg_rom bsegs)).
  Proof.
    Local Ltac2 Set LiaHints.tbl := fun () => "00D0>10353725385.5111293233672.5525607159172.5541348280724.5743622467737.5543935889328.5545579985956.6045579985963.6151441913051.5352781141368.5554468097430.6254468097432.6056660910639.5559310648043.5059314923118.4759586081460.6059586081465.6359586081466.6262759001015.5567789172792.5500000;00I00[00f01401F01G01H01S01[01c01k02902K02V02^02f02n03<03GS3LTB2Hk2HiS3LTB2Hk2Hi2KBS3LTB2SZ3TBB2Hk2HiS3LTB2Hk2HiS3LTB2Hk2Hi2KBS3LTB2SZ3TBB2Hk2HiFFS3LTB2Hk2HiS3LTB2HkS3LTB2HkS3LTB2HkS3LTB2Hk2Hi2KBS3LTB2SZ2Hk2Hi3NTHS3LTB2Hk2HiS3LTB2HkS3LTB2HkS3LTB2HkS3LTB2SZ2Hk2HiS3LTB2Hk2Hi".
induction k as [|k IH]; intros i h x15 x16 Q Hk Hi Hh K; [exfalso; lia|].
    destruct (nth_error tb (Z.to_nat i)) as [w|] eqn:NTH. 2:{ exfalso. apply nth_error_None in NTH. rewrite LTB in NTH. lia. }
    pose proof (u64arr_read bsegs m T tb i w (wa (T + 8 * i)) TB NTH ltac:(lia) eq_refl) as RD.
    do 8 zstep.
    lazymatch goal with |- context [Z_to_bv 64 (Z.lxor ?a h * ?M)%Z] =>
      replace (Z_to_bv 64 (Z.lxor a h * M)%Z) with (Z_to_bv 64 (mz_add h (bv_unsigned w)))
        by (unfold mz_add, mz_mix; apply Z_to_bv_mod64) end.
    pose proof (mz_add_range h (bv_unsigned w)) as Hh'.
    assert (SK : skipn (Z.to_nat i) tb = w :: skipn (Z.to_nat (i + 1)) tb).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      clear - NTH. revert NTH. generalize (Z.to_nat i) as n. intros n NTH.
      revert tb NTH. induction n as [|n IHn]; intros [|x l] NTH; cbn in *; try discriminate.
      - injection NTH as ->. reflexivity.
      - apply IHn. exact NTH. }
    zstep. if_cases KB; zify_cond KB.
    - replace (T + 8 * i + 8)%Z with (T + 8 * (i + 1))%Z by lia.
      eapply (IH (i + 1)%Z); [lia | lia | exact Hh' |].
      intros x15' x16'.
      replace (mz_adds (mz_add h (bv_unsigned w)) (map bv_unsigned (firstn (Z.to_nat (sz - (i + 1))) (skipn (Z.to_nat (i + 1)) tb))))
        with (mz_adds h (map bv_unsigned (firstn (Z.to_nat (sz - i)) (skipn (Z.to_nat i) tb)))); [apply K|].
      rewrite SK. replace (Z.to_nat (sz - i)) with (S (Z.to_nat (sz - (i + 1)))) by lia. cbn [firstn map mz_adds fold_left]. reflexivity.
    - replace (T + 8 * i + 8)%Z with (T + 8 * sz)%Z by lia.
      replace (mz_add h (bv_unsigned w)) with (mz_adds h (map bv_unsigned (firstn (Z.to_nat (sz - i)) (skipn (Z.to_nat i) tb)))); [apply K|].
      rewrite SK. replace (Z.to_nat (sz - i)) with 1%nat by lia. cbn. reflexivity.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End HashLoop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FindFile.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Section FindLoop.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (hsh NODES N : Z) (hs lk sid : Z -> Z).
  Hypothesis Hh : (0 <= hsh < 2^64)%Z.
  Hypothesis HN : (1 <= N < 65536)%Z.
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis CMAP : rw_cells bsegs m MAP1 [C8 (Z_to_bv 64 NODES)].
  Hypothesis CN : forall i, (1 <= i <= N)%Z ->
    rw_cells bsegs m (NODES + 16 * i) [C8 (Z_to_bv 64 (hs i)); C4 (Z_to_bv 64 (lk i)); C4 (Z_to_bv 64 (sid i))].
  Hypothesis NB : (AIMG_HI <= NODES /\ NODES + 1048576 <= ATOP /\ NODES mod 4096 = 0)%Z.
  Hypothesis LK : lk_ok lk N.
  Hypothesis HS : forall i, (1 <= i <= N)%Z -> (0 <= hs i < 2^64)%Z.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RNODES : rng RNG NODES 1048576.

  #[warnings="-notation-for-abbreviation"] Notation ST_AT pc x10 x11 x12 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 hsh) s4 s5 (Z_to_bv 64 0xffff) s7 (Z_to_bv 64 MAP1) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  #[using="rc NODES sid Hh HN CMAP CN NB LK HS RI RNODES"] Lemma find_loop : forall (k : nat) (j : Z) x10 x12 (Q : machine_state -> Prop),
    (Z.to_nat j <= k)%nat -> (0 <= j <= N)%Z ->
    (forall j' x11 x12', (1 <= j' <= N)%Z -> hs j' = hsh -> In j' (chain lk j) ->
       evtF bsegs RNG Q (ST_AT 0x71e98 (Z_to_bv 64 j') x11 x12')) ->
    (forall x10' x12', Forall (fun j' => hs j' <> hsh) (chain lk j) ->
       evtF bsegs RNG Q (ST_AT 0x71dec x10' (Z_to_bv 64 0) x12')) ->
    evtF bsegs RNG Q (ST_AT 0x71d94 x10 (Z_to_bv 64 j) x12).
  Proof.
    unfold AIMG_HI, MAP1 in *.
    induction k as [|k IH]; intros j x10 x12 Q Hk Hj FOUND ABSENT.
    - Local Ltac2 Set LiaHints.tbl := fun () => "00P0>18204077971.7121921109347.6321921109347.642597469165.71 28915217076.7132579247557.6332954672962.6232963790148.7032963790154.7334612439040.7136511323770.6336511323770.6440140147424.6540818989526.6445281471074.7148788237276.7452843860937.765798337359.65 59308628179.1 59314873579.6359314873579.6459586081460.7160210310797.5860210310797.5960210310797.6060210310797.6160210310797.6563118856890.6663852889314.6465504523926.6365504523926.649124237546.55 00000E00R00_00c00g00n01;01H01U01V01c02002;02?02F02[02_03003403B03L03P03Z03d04204@04N04_04c04g04k055S2HN2NB2Hk2Hj3ENA3LKjS2HN2NB2Hk2HjS2HN2NB2Hk2HjS2HkS2HkS2NB2HkS2HN2NB2Hk2HjS2HN2NB2Hk2HjS2HN2NB2Hk2HjFS2HN2NB2Hk2HjS2HN2NB2Hk2HjS2NB2Hk3LKjS2HkS2Hk2HjS2HN2NB2Hk2Hj3ENA3LKjS2HkS2HN2NB2Hk2Hj3LKjS2K0S2NB2Hk3LKj2K0S2NB2Hk2K1S2HkS2Hk2Hj2NZS2Hk2Hj2NZS2NB2Hk2Hj3LKjS2NB2Hk2Hj3LKjS2NB2Hk2Hj3LKjS2HN2NB2Hk2Hj3LKjS2HkS2HkS2HkS2NB2Hk2Hj".
assert (j = 0%Z) by lia. subst j.
      zstep. if_cases K0; zify_cond K0. 2:{ exfalso. clear -K0. lia. }
      apply ABSENT. rewrite chain_0. constructor.
    - destruct (Z.eq_dec j 0) as [->|NZ].
      { zstep. if_cases K0; zify_cond K0. 2:{ exfalso. clear -K0. lia. } apply ABSENT. rewrite chain_0. constructor. }
      pose proof (CN j ltac:(lia)) as NODE. pose proof (LK j ltac:(lia)) as LKj. pose proof (HS j ltac:(lia)) as HSj.
      pose proof (chain_cons lk N j LK ltac:(lia)) as CC.
      zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
      zstep. zstep.
      replace (bv_swrap 32 (Z.shiftr (bv_wrap 32 j) 16)) with 0%Z
        by (rewrite bv_wrap_small by (change (bv_modulus 32) with 4294967296%Z; lia); rewrite Z.shiftr_div_pow2, Z.div_small by lia; reflexivity).
      do 3 zstep.
      zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
      do 5 zstep.
      setreg 11%Z (Z_to_bv 64 (NODES + 16 * j))
        ltac:(f_equal; rewrite Z.mod_small by lia; change 65535%Z with (Z.ones 16); rewrite Z.land_ones by lia;
              rewrite Z.mod_small by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
      remember (NODES + 16 * j)%Z as NA eqn:ENA.
      zstep. zstep. rewrite sx32_lit by lia.
      subst NA.
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        eapply (IH (lk j)); [lia | lia | |].
        * intros j' x11 x12' H1 H2 H3. apply FOUND; [exact H1 | exact H2 |]. rewrite CC. right. exact H3.
        * intros x10' x12' FA. apply ABSENT. rewrite CC. constructor; [| exact FA]. clear -K2. intros E. apply K2. rewrite E. reflexivity.
      + (* [comment removed for export] *)
        zstep. apply FOUND; [lia | | rewrite CC; left; reflexivity]. clear -K2 Hh HSj. first [exact K2 | symmetry; exact K2 | lia].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End FindLoop.
End FindFile.
End CANSEC3.
