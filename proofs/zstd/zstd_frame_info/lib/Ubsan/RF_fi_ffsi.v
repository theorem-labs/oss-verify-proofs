(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge Image Mem.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg RF_fi_iface RF_fi_cbs RF_fi_gfha RF_fi_gfha2.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

(* [comment removed for export] *)
Lemma lor_lt_pow2 : forall a b k, 0 <= a < 2^k -> 0 <= b < 2^k -> 0 <= Z.lor a b < 2^k.
Proof.
  intros a b k Ha Hb. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>26983584907.8 43330057433.6 44204549936.5 51796692231.6 59314955108.1061883703582.8 62711757.5    62742594.8    67469320460.6 67469320589.8 9666691384.10 00000700:00A00E00V00c00g00k00o01301ES2Ha2NaS1HS2Ha2HbS2HaS2Ha2Hb2Na2Nb1H1ES2Hb2Ha2Na2NbS2HbS2HbS2HaS2HaS2Ha2Hb2Na2Nb1H2H0".
split; [apply Z.lor_nonneg; lia|].
  assert (Hk : 0 <= k). { destruct (Z.le_gt_cases 0 k); [assumption|]. rewrite Z.pow_neg_r in Ha by lia. lia. }
  destruct (Z.eq_dec a 0) as [->|Na]. { rewrite Z.lor_0_l. lia. }
  destruct (Z.eq_dec b 0) as [->|Nb]. { rewrite Z.lor_0_r. lia. }
  apply Z.log2_lt_pow2. { pose proof (Z.lor_nonneg a b). assert (Z.lor a b <> 0). { intros E. apply Z.lor_eq_0_iff in E. lia. } lia. }
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma shiftl_mod_lt : forall a s M, 0 < M -> 0 <= (Z.shiftl a s) mod M < M.
Proof. intros. apply Z.mod_pos_bound. assumption. Qed.

(* [comment removed for export] *)
Lemma le32_bound : forall b4 b5 b6 b7 : bv 8,
  0 <= Z.lor (Z.lor ((Z.shiftl (bv_unsigned b7) 24) mod 18446744073709551616) ((Z.shiftl (bv_unsigned b6) 16) mod 18446744073709551616))
             (Z.lor ((Z.shiftl (bv_unsigned b5) 8) mod 18446744073709551616) (bv_unsigned b4)) < 2^32.
Proof.
  intros b4 b5 b6 b7.
  pose proof (bv_unsigned_in_range 8 b4) as H4. pose proof (bv_unsigned_in_range 8 b5) as H5.
  pose proof (bv_unsigned_in_range 8 b6) as H6. pose proof (bv_unsigned_in_range 8 b7) as H7.
  unfold bv_modulus in *. cbn in H4, H5, H6, H7.
  Local Ltac2 Set LiaHints.tbl := fun () => "0060=12500131186.816039847595.833911805249.841891547815.863368315815.865502416423.800000:00D00H00I00J00KS2H72H62H5S2H72H62H5S2H4SSS".
rewrite !Z.shiftl_mul_pow2 by lia. rewrite !Z.mod_small by lia.
  apply lor_lt_pow2; apply lor_lt_pow2; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Definition FFSI_DEPTH : Z := 176.   (* [comment removed for export] *)

Definition ffsi_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R n lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists (a0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (nb : list byte) (cs db : word) (m' : fmem),
    ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(R, R + 24); (SP - FFSI_DEPTH, SP)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' R [CB 8 nb; C8 cs; C8 db]
    /\ stk usegs m' lo SP
    /\ (bv_unsigned cs < 2^64 - 119 -> 1 <= bv_unsigned cs <= n).

Definition ffsi_stmt : Prop :=
  forall (ra : word) (SP : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (S : Z) (bl : list Z) (R lo : Z) (rj : list cell),
    buf_at m S bl -> zlen bl < 2^62 -> S + zlen bl < 2^63 ->
    rw_cells usegs m R rj -> cells_size rj = 24%nat ->
    stk usegs m lo SP -> lo <= SP - FFSI_DEPTH -> 0 <= SP < 2^64 ->
    (S + zlen bl <= R \/ R + 24 <= S) -> (S + zlen bl <= SP - FFSI_DEPTH \/ SP <= S) -> (R + 24 <= SP - FFSI_DEPTH \/ SP <= R) ->
    mem_inv usegs m -> (0 < S \/ zlen bl = 0) -> SP mod 16 = 0 -> a3 = Z_to_bv 64 0 ->
    a0 = Z_to_bv 64 R -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlen bl) ->
    evt usegs (ffsi_post ra SP gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R (zlen bl) lo m)
        (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PFI_FFSI) fc None m (seg_rom usegs)).

Section FFSI.
  Variables (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : fmem) (S : Z) (bl : list Z) (R lo : Z).
  Notation n := (zlen bl).
  Notation sp := (Z_to_bv 64 SP).
  Notation W := [(R, R + 24); (SP - FFSI_DEPTH, SP)].
  Notation POST := (ffsi_post ra SP gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R n lo m).
  Hypothesis BUF : buf_at m S bl.
  Hypothesis NB : n < 2^62.
  Hypothesis SN : S + n < 2^63.
  Hypothesis LO : lo <= SP - FFSI_DEPTH.
  Hypothesis SPH : 0 <= SP < 2^64.
  Hypothesis SEP1 : S + n <= R \/ R + 24 <= S.
  Hypothesis SEP2 : S + n <= SP - FFSI_DEPTH \/ SP <= S.
  Hypothesis SEP3 : R + 24 <= SP - FFSI_DEPTH \/ SP <= R.
  Hypothesis SPOS : 0 < S \/ n = 0.
  Hypothesis SPA : SP mod 16 = 0.

  (* [comment removed for export] *)
  Definition frame_cells (j0 : list byte) (b0 b1 b2 : list byte) (zc : list cell) : list cell :=
    CB 4 j0 :: CB 4 b0 :: CB 4 b1 :: CB 4 b2 :: zc ++ [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  #[using="LO SPH"] Lemma ffsi_tail : forall m1 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 q8 q9 q18 q19 q20 q21 q22 : word)
      j0 b0 b1 b2 zc (nb : list byte) (cs db : word),
    cells_size zc = 48%nat ->
    (bv_unsigned cs < 2^64 - 119 -> 1 <= bv_unsigned cs <= n) ->
    rw_cells usegs m1 R [CB 8 nb; C8 cs; C8 db] ->
    rw_cells usegs m1 (SP + -128) (frame_cells j0 b0 b1 b2 zc) ->
    stk usegs m1 lo (SP + -128) -> munch W m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    evt usegs POST
      (MS (mkR x1 (Z_to_bv 64 (SP + -128)) gp tp x5 x6 x7 q8 q9 x10 x11 x12 x13 x14 x15 x16 x17 q18 q19 q20 q21 q22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x13878) fc None m1 (seg_rom usegs)).
  Proof.
    intros until db. intros ZC CSF RR FR ST MU WM MI. unfold FFSI_DEPTH, frame_cells in *.
    (* [comment removed for export] *)
    apply (rw_cells_merge usegs m1 _ [CB 4 j0; CB 4 b0; CB 4 b1; CB 4 b2] zc [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) in FR.
    rewrite ZC in FR. cbn [app] in FR.
    pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
    Local Ltac2 Set LiaHints.tbl := fun () => "0090>19565526897.7924357189705.7028547637617.8036101642353.7839100099953.7943379581041.7944874942577.7845183686513.7347497582246.7100000W00b01I02002W03>03e04L04ZS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32ZC2FBS3SPH2ZC2FBS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32ZC2FBS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32ZC2FBS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32ZC2FBS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32ZC2FBS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32ZC2FBS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32ZC2FBS2LO3SPH2ZC2FB".
do 9 zstep.
    release_frame FR ST SP.
    zstep. finish. all: try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="LO SPH SEP3"] Lemma ffsi_err : forall m1 (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 q8 q9 q18 q19 q20 q21 q22 : word) (e : word)
      j0 b0 b1 b2 zc rc,
    cells_size zc = 48%nat -> cells_size rc = 24%nat ->
    2^64 - 119 <= bv_unsigned e ->
    rw_cells usegs m1 R rc ->
    rw_cells usegs m1 (SP + -128) (frame_cells j0 b0 b1 b2 zc) ->
    stk usegs m1 lo (SP + -128) -> munch W m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    q8 = Z_to_bv 64 R ->
    evt usegs POST
      (MS (mkR x1 (Z_to_bv 64 (SP + -128)) gp tp x5 x6 x7 q8 q9 e x11 x12 x13 x14 x15 x16 x17 q18 q19 q20 q21 q22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x1386c) fc None m1 (seg_rom usegs)).
  Proof.
    intros until rc. intros ZC RC EE RR FR ST MU WM MI ->. unfold FFSI_DEPTH, frame_cells in *.
    pose proof (rw_cells_bound _ _ _ _ RR) as RB. rewrite RC in RB.
    (* [comment removed for export] *)
    apply (rw_cells_merge usegs m1 _ [CB 4 j0; CB 4 b0; CB 4 b1; CB 4 b2] zc [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) in FR.
    rewrite ZC in FR. cbn [app] in FR.
    (* [comment removed for export] *)
    destruct (rw_cells_forget usegs m1 R rc RR) as [rj RR']. clear RR. rewrite RC in RR'.
    apply (rw_cells_split_CB usegs m1 _ [] 24 rj [] [8; 8; 8]%nat) in RR'; [| reflexivity]. cbn [app mk_CB_cells] in RR'.
    zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0090>19302942247.8426642192459.8226642192459.8429018245758.8437038741246.8237371137959.8239782709267.8448810528403.8259308663652.3 00000A00O00]00n01?01P01c02602<S3SPH2ZC2RC2RB2HBS3SPH2ZC2RC2RBS3SPH2ZC2RC2RBS3SPH2ZC2RC2RB2HBS3SPH2ZC2RC2RB2HBS3SPH2ZC2RC2RB2HBS3SPH4SEP32ZC2RC2RBS3SPH4SEP32ZC2RC2RBS1C2EE".
zstep. zstep. (* [comment removed for export] *)
    eapply (ffsi_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j0 b0 b1 b2 [CB 48 (cells_bytes zc)]); try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; [reflexivity|].
    intros C. exfalso. revert C EE. clear. intros C EE. lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="S NB LO SPH SEP1 SEP2 SEP3"] Lemma ffsi_ok : forall m1 (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 q8 q9 q18 q19 q20 q21 q22 : word) (csz : Z)
      j0 b0 b1 b2 zc rc,
    cells_size zc = 48%nat -> cells_size rc = 24%nat ->
    1 <= csz <= n ->
    rw_cells usegs m1 R rc ->
    rw_cells usegs m1 (SP + -128) (frame_cells j0 b0 b1 b2 zc) ->
    stk usegs m1 lo (SP + -128) -> munch W m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    q8 = Z_to_bv 64 R ->
    evt usegs POST
      (MS (mkR x1 (Z_to_bv 64 (SP + -128)) gp tp x5 x6 x7 q8 q9 x10 (Z_to_bv 64 csz) x12 x13 x14 x15 x16 x17 q18 q19 q20 q21 q22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x138d4) fc None m1 (seg_rom usegs)).
  Proof.
    intros until rc. intros ZC RC CS RR FR ST MU WM MI ->. unfold FFSI_DEPTH, frame_cells in *.
    pose proof (rw_cells_bound _ _ _ _ RR) as RB. rewrite RC in RB.
    (* [comment removed for export] *)
    apply (rw_cells_merge usegs m1 _ [CB 4 j0; CB 4 b0; CB 4 b1; CB 4 b2] zc [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) in FR.
    rewrite ZC in FR. cbn [app] in FR.
    destruct (rw_cells_forget usegs m1 R rc RR) as [rj RR']. clear RR. rewrite RC in RR'.
    apply (rw_cells_split_CB usegs m1 _ [] 24 rj [] [8; 8; 8]%nat) in RR'; [| reflexivity]. cbn [app mk_CB_cells] in RR'.
    Local Ltac2 Set LiaHints.tbl := fun () => "00@0>13722052944.7017112407867.7019302942247.8222954551237.7426642192459.7426642192459.8126642192459.8229018245758.8229791052619.7437038741246.8137371137959.8139782709267.8247910218415.7448810528403.8164373332722.7465093347183.7400000A00d01501b02002>02L02]02n03?03P03c04604I04Z05GS3SPH2ZC2RC2CS2RBS2NB3SPH4SEP14SEP24SEP32ZC2RC2CS2RBS3SPH2ZC2RC2RB2HBS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32ZC2RC2CS2RBS3SPH2ZC2RC2RBS3SPH2ZC2RC2RBS3SPH2ZC2RC2RBS3SPH2ZC2RC2RB2HBS3SPH2ZC2RC2RB2HBS3SPH2ZC2RC2RB2HBS3SPH2ZC2RC2RB2HBS3SPH4SEP32ZC2RC2RBS3SPH4SEP32ZC2RC2RBS3SPH4SEP32ZC2RC2RBS3SPH2ZC2RC2RB2HBS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32ZC2RC2CS2RB".
zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    lazymatch goal with H : rw_cells _ ?m2 R [C8 ?w0; C8 ?w1; C8 ?w2] |- _ =>
      apply (rw_cells_reshape m2 R _ [CB 8 (le8 w0); C8 w1; C8 w2]) in H;
        [| cbn [cells_wf cell_wf]; rewrite length_le8; repeat split; reflexivity | reflexivity | reflexivity ] end.
    eapply (ffsi_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j0 b0 b1 b2 [CB 48 (cells_bytes zc)]); try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; [reflexivity|].
    intros _. rewrite unsigned_lit by lia. lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  Definition head_st (m1 : fmem) (k : Z) (r nb x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (SP + -128)) gp tp x5 x6 x7 (Z_to_bv 64 R) (Z_to_bv 64 S) r x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (n - k)) x19 (Z_to_bv 64 (S + k)) nb (Z_to_bv 64 (-119)) s7 s8 s9 s10 s11 x28 x29 x30 x31)
       F (Z_to_bv 64 0x1382c) fc None m1 (seg_rom usegs).
  Definition head_inv (m1 : fmem) (k : Z) (r : word) j0 b0 b1 b2 j1 h j2 rc : Prop :=
    0 <= k <= n /\ 1 <= k /\ bv_unsigned r <= 2^64 - 120 /\ cells_size rc = 24%nat /\
    rw_cells usegs m1 R rc /\
    rw_cells usegs m1 (SP + -128) (frame_cells j0 b0 b1 b2 [CB 24 j1; C4 (Z_to_bv 64 h); CB 20 j2]) /\
    bytes_at usegs m1 S (map (Z_to_bv 8) bl) /\
    stk usegs m1 lo (SP + -128) /\ munch W m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.

  (* [comment removed for export] *)
  Ltac fin_tac :=
    zstep; zstep; zstep; (* [comment removed for export] *)
    zstep; (let KF := fresh "KF" in if_cases KF; clear KF);
    [ | zstep; zstep ];   (* [comment removed for export] *)
    (lazymatch goal with FRx : rw_cells _ _ (_ + -128) (CB 4 ?a :: CB 4 ?b :: CB 4 ?c :: CB 4 ?d :: ?rest) |- _ =>
       let zc := eval cbv in (firstn (length rest - 8) rest) in
       eapply (ffsi_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a b c d zc); try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try reflexivity end);
    rewrite ?unsigned_lit by lia; rewrite ?Z.mod_small by lia; lia.

  (* [comment removed for export] *)
  Ltac err_tac :=
    (lazymatch goal with FRx : rw_cells _ _ (_ + -128) (CB 4 ?a :: CB 4 ?b :: CB 4 ?c :: CB 4 ?d :: ?rest) |- _ =>
       let zc := eval cbv in (firstn (length rest - 8) rest) in
       eapply (ffsi_err _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a b c d zc); try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try reflexivity end);
    rewrite ?unsigned_lit_wrap; first [vm_compute; discriminate | lia].

  (* [comment removed for export] *)
  #[using="BUF NB SN LO SPH SEP1 SEP2 SEP3 SPOS SPA"] Lemma ffsi_step : forall m1 k r nb x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 j0 b0 b1 b2 j1 h j2 rc,
    head_inv m1 k r j0 b0 b1 b2 j1 h j2 rc ->
    (forall m2 k2 r2 nb2 y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31 c0 c1 c2 rc2,
       head_inv m2 k2 r2 j0 c0 c1 c2 j1 h j2 rc2 -> k + 3 <= k2 ->
       evt usegs POST (head_st m2 k2 r2 nb2 y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31)) ->
    evt usegs POST (head_st m1 k r nb x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31).
  Proof.
    intros until rc. intros (K & K1 & RU & RC & RR & FR & PL & ST & MU & WM & MI) CONT. unfold head_st, FFSI_DEPTH, frame_cells in *.
    cbn [app] in FR.
    pose proof (proj2 BUF) as PLR.
    pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = n) by (rewrite length_map; reflexivity).
    pose proof (rw_cells_bound _ _ _ _ RR) as RB. rewrite RC in RB.
    pose proof (bv_unsigned_in_range 64 r) as RR0. unfold bv_modulus in RR0. cbn in RR0.
    assert (ST0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (SP0 : 0 < S) by lia.
    zstep. (* [comment removed for export] *)
    zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00X0>11237527855.7611237533443.7711628294193.9311801586693.9211801586693.9313642778481.8613642778481.8714040770588.7916760036534.9322700267513.9425261071709.8626234366065.862858122154.87 2862464294.78 29696350348.8630689261738.8730702190118.7833124399503.923479450872.76 3486507728.88 35918459776.9136393902218.7636399560354.8840307773297.8640443842838.8640703418902.8842088900514.7944484923210.9246162050552.7948947615290.8650915236738.8656258481082.8664297306692.9064297306692.9167302398321.8867302398321.8967966163678.868929152550.77 8935173664.90 9097623341.79 00000T01801901D01O02M03N03Y04B04O04]05[05f06106@06K06V07007R08408Y08k09=0:;0:F0:Q0;50;@0;K0;Y0;d0<H0<c0=>0><0?=0?a0@H0@m0AGS3SPH4SEP14SEP24SEP32K12RC2RB3RR02KXS3SPH4SEP14SEP24SEP32K12RC2RB3RR02K4FS3SPH2RC2RBS3SPH2RC2RBS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP31K2K12RU2RC2BB4LENB2RB3RR02KXS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP31K2K12RU2RC2BB4LENB2RB3RR02KX2K4S3SPH2RC2RBS3SPH4SEP14SEP24SEP32K12RC4LENB2RB3RR02KXS3SPH2RC2RB1HS3SPH2RC2RB2KXS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP31K2K12RU2RC2BB4LENB2RB3RR02KXS3SPH2RC2RBS3SPH2RC2RBS3SPH2RC2RB3RR0S3SPH2RC2RBS3SPH2RC2RBS3SPH4SEP32K12RC2RB3RR02KXS2NB3SPH4SEP14SEP24SEP31K2K12RC2RBS2NB3SPH4SEP14SEP24SEP31K2K12RC2RBS2SN3SPH4SEP24SEP32K12RC2BB2RB3RR02K4S3SPH2RU2RC2RB3RR0S3SPH2RU2RC2RB3RR0S3BUF2NB2SN2LO3SPH4SEP14SEP24SEP31K2K12RU2RC2BB4LENB2RB3RR02KXS3SPH2RC2RBS3SPH2RC2RBS3SPH4SEP14SEP24SEP32K12RC2RB3RR02KXS3SPH2RC2RBS3SPH2RC2RBS3SPH2RC2RB2KES3SPH2RC2RBS3SPH4SEP14SEP24SEP32K12RC2RB3RR02KXS2SN3SPH2K12RC2BB2RB3RR02KXS2SN3SPH2K12RC2BB2RB3RR02K4S3BUF2NB2SN2LO3SPH4SEP14SEP24SEP31K2K12RU2RC2BB4LENB2RB3RR02KXS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP31K2K12RU2RC2BB4LENB2RB3RR02KX2K4S3SPH4SEP14SEP24SEP32K12RC2RB3RR02KXS2NB3SPH4SEP14SEP24SEP32K12RC2RB3RR02KXS2SN3SPH4SEP24SEP32K12RC2BB2RB3RR02KXS3SPH4SEP22K12RC2RB3RR02KX".
if_cases KX; zify_cond KX.
    - (* [comment removed for export] *)
      zstep. zstep. err_tac.
    - zstep. (* [comment removed for export] *)
      zstep. if_cases U1; zify_cond U1; [exfalso; lia|].
      zstep. if_cases U2; zify_cond U2; [exfalso; lia|].
      zstep. if_cases U3; zify_cond U3; [exfalso; lia|].
      zstep. zstep. (* [comment removed for export] *)
      zstep. if_cases KL; clear KL.
      + (* [comment removed for export] *)
        zstep. (* [comment removed for export] *)
        zstep. if_cases KC; clear KC.
        * (* [comment removed for export] *)
          fin_tac.
        * (* [comment removed for export] *)
          zstep. zstep. if_cases K4; zify_cond K4.
          -- (* [comment removed for export] *) zstep. zstep. err_tac.
          -- zstep. (* [comment removed for export] *) zstep. zstep. if_cases U4; zify_cond U4; [exfalso; lia|]. fin_tac.
      + (* [comment removed for export] *)
        zstep. zstep. zstep. (* [comment removed for export] *)
        (* [comment removed for export] *)
        lazymatch type of FR with rw_cells _ ?mq ?A (?c12 :: ?cb0 :: ?cb1 :: ?cb2 :: ?rest) =>
          apply (proj1 (rw_cells_app mq A [c12] (cb0 :: cb1 :: cb2 :: rest))) in FR; destruct FR as [F12 FB]; cbn [cells_size csize Nat.add] in FB;
          apply (proj1 (rw_cells_app mq _ [cb0; cb1; cb2] rest)) in FB; destruct FB as [FB FZ]; cbn [cells_size csize Nat.add] in FZ end.
        replace (SP + -128 + Z.of_nat 4) with (SP + -124) in FB, FZ by lia.
        replace (SP + -124 + Z.of_nat 12) with (SP + -112) in FZ by lia.
        pose proof cbs_proof as CB'. unfold cbs_stmt, cbs_post in CB'.
        zstep. (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          eapply evt_cut; [ eapply CB';
            [ apply (buf_at_skipn mc S bl (k + (bv_unsigned r + 3))); [split; [exact PL| exact PLR] | lia]
            | exact FB
            | rewrite zlen_skipn by lia; lia
            | assumption
            | lia
            | lia
            | lia
            | f_equal; lia
            | rewrite zlen_skipn by lia; f_equal; lia
            | reflexivity ] | ]; post_call usegs mc end.
        clear CB'. try rename MI0 into MI.
        (* [comment removed for export] *)
        lazymatch goal with PCx : rw_cells _ ?m2 (SP + -124) [?y0; ?y1; ?y2], FZx : rw_cells _ _ (SP + -112) ?rest, F12x : rw_cells _ _ (SP + -128) [?c12] |- _ =>
          assert (FR : rw_cells usegs m2 (SP + -128) ([c12] ++ ([y0; y1; y2] ++ rest)))
            by (apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact F12x|]; cbn [cells_size csize Nat.add];
                replace (SP + -128 + Z.of_nat 4) with (SP + -124) by lia;
                apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact PCx|]; cbn [cells_size csize Nat.add];
                replace (SP + -124 + Z.of_nat 12) with (SP + -112) by lia; exact FZx);
          clear PCx FZx F12x; cbn [app] in FR end.
        zstep. zstep. (* [comment removed for export] *)
        zstep. if_cases KE; zify_cond KE.
        * (* [comment removed for export] *)
          replace (S + k + (bv_unsigned r + 3)) with (S + (k + (bv_unsigned r + 3))) by lia.
          replace (n - k - (bv_unsigned r + 3)) with (n - (k + (bv_unsigned r + 3))) by lia.
          eapply CONT; [| lia]. unfold head_inv, frame_cells. cbn [app].
          lazymatch goal with BPx : rw_cells _ _ (SP + -128) _ |- _ => idtac end.
          repeat match goal with |- _ /\ _ => split end; try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try lia.
        * (* [comment removed for export] *) err_tac.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="BUF NB SN LO SPH SEP1 SEP2 SEP3 SPOS SPA"] Lemma ffsi_loop : forall (f : nat) m1 k r nb x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 j0 b0 b1 b2 j1 h j2 rc,
    n - k <= Z.of_nat f ->
    head_inv m1 k r j0 b0 b1 b2 j1 h j2 rc ->
    evt usegs POST (head_st m1 k r nb x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31).
  Proof.
    induction f as [|f IH]; intros until rc; intros FUEL INV.
    - eapply ffsi_step; [exact INV|]. intros until rc2. intros INV2 HK. exfalso.
      destruct INV as (K & _). destruct INV2 as (K2 & _). cbn in FUEL. Local Ltac2 Set LiaHints.tbl := fun () => "0020>48304467294.8759308582510.8500000=00MS3SPH4FUEL2HKS3SPH4FUEL2K22HK".
lia.
    - eapply ffsi_step; [exact INV|]. intros until rc2. intros INV2 HK. eapply IH; [| exact INV2]. destruct INV2 as (K2 & _). lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="BUF NB SN LO SPH SEP1 SEP2 SEP3 SPOS SPA"] Lemma ffsi_frame : forall m1 (x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x28 x29 x30 x31 q19 q20 q21 q22 : word) j0 b0 b1 b2 zj rc,
    cells_size rc = 24%nat ->
    rw_cells usegs m1 R rc ->
    rw_cells usegs m1 (SP + -128) (frame_cells j0 b0 b1 b2 [CB 48 zj]) ->
    bytes_at usegs m1 S (map (Z_to_bv 8) bl) ->
    stk usegs m1 lo (SP + -128) -> munch W m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 (SP + -128)) gp tp x5 x6 x7 (Z_to_bv 64 R) (Z_to_bv 64 S) x10 x11 x12 (Z_to_bv 64 0) x14 x15 x16 x17
                (Z_to_bv 64 n) q19 q20 q21 q22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x137c8) fc None m1 (seg_rom usegs)).
  Proof.
    intros until rc. intros RC RR FR PL ST MU WM MI. unfold FFSI_DEPTH, frame_cells in *. cbn [app] in FR.
    pose proof (proj2 BUF) as PLR.
    pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = n) by (rewrite length_map; reflexivity).
    pose proof (rw_cells_bound _ _ _ _ RR) as RB. rewrite RC in RB.
    zstep. zstep. zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ ?mq ?A (?c12 :: ?cb0 :: ?cb1 :: ?cb2 :: ?cz :: ?rest) =>
      apply (proj1 (rw_cells_app mq A [c12; cb0; cb1; cb2] (cz :: rest))) in FR; destruct FR as [Flo FZ]; cbn [cells_size csize Nat.add] in FZ;
      apply (proj1 (rw_cells_app mq _ [cz] rest)) in FZ; destruct FZ as [FZ Fhi]; cbn [cells_size csize Nat.add] in Fhi end.
    Local Ltac2 Set LiaHints.tbl := fun () => "00]0?10753198419.10011628294193.10711801586693.10611801586693.10712347144177.94 12428150072.93 12936212602.71 13210268013.93 15866384723.71 16083456449.10116760036534.10717765706380.71 20005849380.93 22700267513.10823760000278.10225076071819.93 25076071819.94 28040491972.94 2858122154.101 2864531590.92  28995526769.10230689261738.10130700129158.92 33124399503.10636398363926.90 3918595962.93  42775044694.71 42967381372.69 42979999466.89 44016079372.10044484923210.1064761334412.100 50592957753.10150969836650.89 50982385660.69 55298587438.10056998280248.1005744875442.89  5744880645.88  57622410744.94 57701858490.90 60734918886.71 6550575845.100 8660374389.93  8699854703.71  00000M00N00Y00d00e00f01601K01V01d02C02Q02_02l03703B03M03l04704B05B05M05X05k06606A06g07207=07K07V07e08708B08M08X08f08g08h09509G09W09e0:80:FS3SPH4SEP14SEP24SEP32RC2RB2HhFS3SPH2RC2RBS3SPH2RC2RBFFS3SPH4SEP22RC2RBS3SPH4SEP32RC4LENB2RBS3SPH2RC2RBS2NB3SPH2RC2RBS3SPH4SEP14SEP24SEP32RC4LENB2RBS2NB3SPH2RC2RBS3SPH2RC2RB2HhS3SPH2RC2RB1HS3SPH2RC2RBS3SPH2RC2RBS3SPH2RC2RBS3SPH4SEP14SEP24SEP32RC4LENB2RBS3SPH2RC2RBS3SPH2RC2RBS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32RC2BB4LENB2RB3ST02KE2K02Hh3H18S3SPH2RC2RBS3SPH2RC2RBS3SPH4SEP32RC2RB2HhS3SPH2RC2RBS3SPH2RC2RBS2LO3SPH4SEP14SEP24SEP32RC4LENB2RB3ST0S3SPH2RC2RBS3SPH2RC2RBS3SPH2RC2RB2HhS3SPH2RC2RBS3SPH2RC2RB3KE2S3SPH2RC2RB2Hh3H18S3SPH2RC2RBS3SPH2RC2RBS3SPH2RC2RBS3SPH2RC2RB2HhFFS3SPH2RC2RB1HS3SPH2RC2RB2Hh3H18S3SPH4SEP22RC2RBS3SPH2RC2RB2HhS3SPH4SEP22RC2RB2HhS2LO3SPH2RC2RB".
replace (SP + -128 + Z.of_nat 16) with (SP + -112) in FZ, Fhi by lia.
    replace (SP + -112 + Z.of_nat 48) with (SP + -64) in Fhi by lia.
    pose proof gfha_proof as G. unfold gfha_stmt, gfha_stmt_at, gfha_post, GFHA_FRAME in G.
    zstep. (* [comment removed for export] *)
    assert (ST0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply G; [ split; [exact PL| exact PLR] | lia | exact FZ | lia | exact ST | lia | lia | lia | lia | lia | assumption | reflexivity
                   | reflexivity | reflexivity | reflexivity ] | ]; post_call usegs mc end.
    clear G. try rename MI0 into MI.
    (* [comment removed for export] *)
    lazymatch goal with PCx : rw_cells _ ?m2 (SP + -112) ?cz, Fhix : rw_cells _ _ (SP + -64) ?hi |- _ =>
      lazymatch type of Flo with rw_cells _ _ _ ?lo4 =>
      assert (FR : rw_cells usegs m2 (SP + -128) (lo4 ++ (cz ++ hi)))
        by (apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact Flo|]; cbn [cells_size csize Nat.add];
            replace (SP + -128 + Z.of_nat 16) with (SP + -112) by lia;
            apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact PCx|]; cbn [cells_size csize Nat.add];
            replace (SP + -112 + Z.of_nat 48) with (SP + -64) by lia; exact Fhix);
      clear Flo PCx Fhix; cbn [app] in FR end end.
    zstep. zstep. if_cases KE; zify_cond KE.
    { (* [comment removed for export] *) err_tac. }
    zstep. if_cases K0; zify_cond K0.
    2: { (* [comment removed for export] *) zstep. zstep. err_tac. }
    (* [comment removed for export] *)
    lazymatch goal with RF : _ -> exists h, _ |- _ => destruct (RF ltac:(rewrite ?unsigned_lit_wrap in K0; exact K0)) as (h & -> & Hh & H18); clear RF end.
    pose proof (proj1 (proj1 FR)) as WF. cbn [cells_wf cell_wf] in WF.
    lazymatch type of FR with rw_cells _ ?m2 _ (?a :: ?b :: ?c :: ?d :: CB 24 ?j1 :: CB 4 _ :: ?rest) =>
      apply (rw_cells_reshape m2 (SP + -128) _ (a :: b :: c :: d :: CB 24 j1 :: C4 (Z_to_bv 64 h) :: rest)) in FR;
      [| cbn [cells_wf cell_wf]; tauto | reflexivity | reflexivity ] end.
    clear WF.
    zstep. (* [comment removed for export] *) rewrite (zx32_small h) by lia.
    zstep. (* [comment removed for export] *)
    zstep. if_cases U1; zify_cond U1; [exfalso; lia|].
    zstep. zstep. zstep. zstep. if_cases U2; zify_cond U2;
      [exfalso; rewrite (proj2 (Z.ltb_lt 0 S)), (proj2 (Z.ltb_ge (h + S) 1)) in U2 by lia; vm_compute in U2; discriminate U2|].
    zstep.
    zstep. zstep. zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ ?mq ?A (?c12 :: ?cb0 :: ?cb1 :: ?cb2 :: ?rest) =>
      apply (proj1 (rw_cells_app mq A [c12] (cb0 :: cb1 :: cb2 :: rest))) in FR; destruct FR as [F12 FB]; cbn [cells_size csize Nat.add] in FB;
      apply (proj1 (rw_cells_app mq _ [cb0; cb1; cb2] rest)) in FB; destruct FB as [FB FZ]; cbn [cells_size csize Nat.add] in FZ end.
    replace (SP + -128 + Z.of_nat 4) with (SP + -124) in FB, FZ by lia.
    replace (SP + -124 + Z.of_nat 12) with (SP + -112) in FZ by lia.
    pose proof cbs_proof as CB'. unfold cbs_stmt, cbs_post in CB'.
    zstep. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply CB';
        [ apply (buf_at_skipn mc S bl h); [split; [eassumption| exact PLR] | lia]
        | exact FB
        | rewrite zlen_skipn by lia; lia
        | assumption
        | lia
        | lia
        | lia
        | f_equal; lia
        | rewrite zlen_skipn by lia; f_equal; lia
        | reflexivity ] | ]; post_call usegs mc end.
    clear CB'. try rename MI0 into MI.
    lazymatch goal with PCx : rw_cells _ ?m2 (SP + -124) [?y0; ?y1; ?y2], FZx : rw_cells _ _ (SP + -112) ?rest, F12x : rw_cells _ _ (SP + -128) [?c12] |- _ =>
      assert (FR : rw_cells usegs m2 (SP + -128) ([c12] ++ ([y0; y1; y2] ++ rest)))
        by (apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact F12x|]; cbn [cells_size csize Nat.add];
            replace (SP + -128 + Z.of_nat 4) with (SP + -124) by lia;
            apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact PCx|]; cbn [cells_size csize Nat.add];
            replace (SP + -124 + Z.of_nat 12) with (SP + -112) by lia; exact FZx);
      clear PCx FZx F12x; cbn [app] in FR end.
    zstep. zstep. if_cases KE2; zify_cond KE2.
    { (* [comment removed for export] *) err_tac. }
    zstep. zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    replace (h + S) with (S + h) by lia.
    eapply (ffsi_loop (Z.to_nat n)); [lia|].
    unfold head_inv, frame_cells. cbn [app].
    repeat match goal with |- _ /\ _ => split end; try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="BUF NB SN LO SPH SEP1 SEP2 SEP3 SPOS SPA"] Lemma ffsi_body : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (rj : list cell),
    rw_cells usegs m R rj -> cells_size rj = 24%nat -> stk usegs m lo SP -> mem_inv usegs m -> a3 = Z_to_bv 64 0 ->
    evt usegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 R) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PFI_FFSI) fc None m (seg_rom usegs)).
  Proof.
    intros until rj. intros RR RC ST MI ->. unfold PFI_FFSI, FFSI_DEPTH in *.
    pose proof (proj1 BUF) as PL. pose proof (proj2 BUF) as PLR.
    pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = n) by (rewrite length_map; reflexivity).
    pose proof (rw_cells_bound _ _ _ _ RR) as RB. rewrite RC in RB.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM. unfold FFSI_DEPTH in MU.
    assert (ST0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    Local Ltac2 Set LiaHints.tbl := fun () => "01Q0>10642850069.6014204193982.6415201037962.681534902743.67 15534906496.8215534906502.921573166614.97 1579170362.65 15878973754.7216075584073.7716075585474.6019240297687.6819302942247.9719565526897.6819923284396.6821155567546.6721327680983.6721920002365.6222163107130.6822668008062.6822954551237.9623594159545.7025950987820.6726642192459.6526642192459.6726642192459.6826642192459.9626642192459.9727869677446.5728465183332.7628465183336.6828465183337.7028465183338.7228465183339.7428465183341.6228465183342.6428465183343.6628547637617.6828734743530.9629018245758.9729791052619.9629873736458.673114556542.68 3132576384.82 3132576390.92 31963894956.6835215891719.8135239261194.6735247899786.6536101642353.6736921773962.6837038741246.9737371137959.9739100099953.6839304366957.5539782709267.9743379581041.6743929283712.8243929283718.9243933922359.8143935878913.7743936118704.8244002406316.6544874942577.6745069577528.6845091696599.6745183686513.6546232973498.6747910218415.9648810528403.9749101319550.6550027895852.6751733410046.6754261855034.6855783155582.6855960661207.6556038818476.6857123477511.8159315053158.8159576979888.7859586081465.7959588178614.926010473214.67 61450317119.6662060115756.6762417871063.6863108286907.7464373332722.9665093347183.9665320511703.6865805175866.687855550858.68 8803967242.67 8947101182.67 92979094.97   9396544682.83 9610135226.67 00000A00R00e01[01\01]02E02V02g03;03L04B04S05I05Z05k06a07207C07e09c0:40:E0:S0:a0:o0;=0;K0;V0;d0<20<@0<N0<\0<j0=80=F0><0>d0?50?F0?Y0@;0@<0@=0@N0@\0@o0AB0B80BK0B\0Bm0Cc0D10DD0E:0E;0E<0E=0E>0ER0Ec0FY0Fj0G`0HV0Hg0I:0IM0Io0J@0Jb0K30KU0LK0L\0Lj0M:0MH0MV0Md0NF0NW0Nh0O^0Oo0P@0R>0S40SE0SX0Sk0TM0U50U^0UoS3SPH2RC2RB2LJ2K8S3SPH2RC2RB2LJ2K8S3SPH4SEP32RC2RB2LJS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32RC2BB4LENB2RB3ST02LJFFS3SPH4SEP14SEP24SEP32RC4LENB2RB2LJ2K82K2S3SPH2RC2RB2LJ2HBS3SPH2RC2RB2LJ2K8S2NB3SPH2RC2RB2LJ2K8S2NB3SPH2RC2RB2LJS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32RC2BB4LENB2RB3ST02LJS3SPH2RC2RB2LJ2HBS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32RC2BB4LENB2RB3ST02LJS3SPH2RC2RB2LJ2HBS3SPH2RC2RB2LJ2HBS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32RC2BB4LENB2RB3ST02LJS3SPH2RC2RB2LJ2K8S3SPH2RC2RB2LJ2HBS3SPH4SEP14SEP24SEP32RC4LENB2RB2LJS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32RC2BB4LENB2RB3ST02LJ2K82RD3RB03RD03RB13RD13RB23RD23RB33RD33RB43RD43RB53RD53RB63RD63RB72K12K2S3SPH2RC2RB2LJ2K8S3SPH2RC2RB2LJ2HBS3SPH2RC2RB2LJS3SPH2RC2RB2LJS3SPH2RC2RB2LJS3SPH2RC2RB2LJS3SPH2RC2RB2LJS3SPH2RC2RBS3SPH2RC2RB2LJS3SPH2RC2RB2LJS3SPH2RC2RB2LJS3SPH2RC2RB2LJS3SPH2RC2RB2LJS3SPH2RC2RB2LJS3SPH2RC2RB2LJS3SPH2RC2RB2LJS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32RC2BB4LENB2RB3ST02LJS3SPH4SEP14SEP24SEP32RC4LENB2RB2LJ2K82K2S3SPH2RC2RB2LJ2HBS3SPH2RC2RB2LJ2HBS3SPH4SEP32RC2RB2LJS3SPH4SEP14SEP24SEP32RC4LENB2RB2LJFFS3SPH2RC2RB2LJ2HBS3SPH2RC2RB2LJS3SPH4SEP32RC2RB2LJS3SPH4SEP32RC2RB2LJS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32RC2BB4LENB2RB3ST02LJS3SPH4SEP32RC2RB2LJS3SPH2RC2RB2LJ2HBS3SPH2RC2RB2LJ2HBS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32RC2BB4LENB2RB3ST02LJS2LO3SPH2RC2RBS3SPH4SEP32RC2RB2LJS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32RC2BB4LENB2RB3ST02LJFFFFS3SPH2RC2RB2LJ2K22EBS3SPH2RC2RB2LJ2HBS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32RC2BB4LENB2RB3ST02LJS3SPH2RC2RB2LJ2K8S3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32RC2BB4LENB2RB3ST02LJS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32RC2BB4LENB2RB3ST02LJS3SPH2RC2RB2LJ2HBS3SPH4SEP32RC2RB2LJS3SPH4SEP32RC2RB2LJS3SPH4SEP14SEP24SEP32RC4LENB2RB2LJS3SPH2RC2RB2LJ2HBS3SPH4SEP14SEP24SEP32RC4LENB2RB2LJS3SPH2RC2RB2LJ2HBS3SPH4SEP14SEP24SEP32RC4LENB2RB2LJS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32RC2BB4LENB2RB3ST02LJS3SPH2RC2RB2LJ2HBS3SPH2RC2RB2LJS3SPH2RC2RB2LJ1CS3SPH2RC2RB2LJS3SPH2RC2RB2LJS3SPH2RC2RB2LJS3SPH4SEP14SEP24SEP32RC4LENB2RB2LJS3SPH2RC2RB2LJ2K8S3SPH2RC2RB2LJ2HBS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32RC2BB4LENB2RB3ST02LJS3SPH2RC2RB2LJ2K8S3SPH2RC2RB2LJ2HBS3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32RC2BB4LENB2RB3ST02LJ2K82RD3RB03RD03RB13RD13RB23RD23RB33RD33RB43RD43RB53RD53RB63RD63RB72K12K2S3BUF2NB2SN2LO3SPH4SEP14SEP24SEP32RC2BB4LENB2RB3ST02LJS3SPH2RC2RB2LJ2HBS3SPH4SEP32RC2RB2LJS3SPH4SEP32RC2RB2LJS3SPH4SEP14SEP24SEP32RC4LENB2RB2LJS3SPH4SEP14SEP24SEP32RC4LENB2RB2LJ2K82K2S3SPH4SEP14SEP24SEP32RC2RB2LJ2K82K12K22EBS3SPH2RC2RB2LJ2HB".
carve_frame 128%nat ST.
    assert (LJ : length junk = 128%nat) by exact (proj1 (proj1 (proj1 FR))).
    apply (rw_cells_split_CB usegs m _ [] 128 junk [] [4; 4; 4; 4; 48; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
    do 9 zstep. (* [comment removed for export] *)
    do 4 zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. if_cases K8; zify_cond K8.
    - (* [comment removed for export] *)
      eapply (ffsi_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rj); try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
    - zstep. if_false. (* [comment removed for export] *)
      zstep. if_cases U0; zify_cond U0; [exfalso; lia|].
      clear_rd. pose_rd 0. pose_rd 1. pose_rd 2. pose_rd 3.
      do 13 zstep. (* [comment removed for export] *)
      zstep. if_cases KM; clear KM.
      + (* [comment removed for export] *)
        eapply (ffsi_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rj); try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
      + (* [comment removed for export] *)
        zstep. zstep. zstep. if_cases U5; zify_cond U5; [exfalso; lia|].
        pose_rd 4. pose_rd 5. pose_rd 6. pose_rd 7.
        do 10 zstep. (* [comment removed for export] *)
        zstep. (* [comment removed for export] *)
        zstep. if_cases K1; zify_cond K1; [ | zstep (* [comment removed for export] *) ];
          (zstep; zstep; zstep; (* [comment removed for export] *)
           zstep; if_cases K2; zify_cond K2; [ | zstep (* [comment removed for export] *) ]).
        (* [comment removed for export] *)
        all: destruct (rw_cells_forget usegs _ R rj RR) as [rjb RR']; clear RR; rewrite RC in RR';
             apply (rw_cells_split_CB usegs _ _ [] 24 rjb [] [8; 8; 8]%nat) in RR'; [| reflexivity]; cbn [app mk_CB_cells] in RR'.
        all: zstep; zstep; zstep; zstep.
        all: lazymatch goal with H : rw_cells _ ?m2 R [C8 ?w0; C8 ?w1; C8 ?w2] |- _ =>
               apply (rw_cells_reshape m2 R _ [CB 8 (le8 w0); C8 w1; C8 w2]) in H;
               [| cbn [cells_wf cell_wf]; rewrite length_le8; repeat split; reflexivity | reflexivity | reflexivity ] end.
        all: lazymatch goal with FRx : rw_cells _ _ (SP + -128) (CB 4 ?a :: CB 4 ?b :: CB 4 ?c :: CB 4 ?d :: ?z :: _) |- _ =>
               eapply (ffsi_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a b c d [z]); try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try reflexivity end.
        (* [comment removed for export] *)
        all: intros C.
        all: first [ exfalso; rewrite unsigned_lit in C by lia; lia
                   | lazymatch goal with |- 1 <= bv_unsigned (Z_to_bv 64 (?E + 8)) <= _ =>
                       pose proof (le32_bound (Z_to_bv 8 (Znth 4 bl)) (Z_to_bv 8 (Znth 5 bl)) (Z_to_bv 8 (Znth 6 bl)) (Z_to_bv 8 (Znth 7 bl))) as EB;
                       let EQ := fresh "EQ" in
                       assert (EQ : bv_unsigned (Z_to_bv 64 (E + 8)) = E + 8) by (apply unsigned_lit; lia);
                       rewrite EQ in *; lia end ].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End FFSI.

Theorem ffsi_proof : ffsi_stmt.
Proof.
  intros until rj; intros BUF NB SN RR RC ST LO SPH SEP1 SEP2 SEP3 MI SPOS SPA A3 -> -> ->.
  eapply ffsi_body; eassumption.
Qed.
