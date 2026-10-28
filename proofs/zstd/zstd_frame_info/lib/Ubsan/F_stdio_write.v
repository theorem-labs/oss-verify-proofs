(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac ITree Nodes Decode SysStep MonadX.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import Stdio_pure.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg F_syscalls StdioFiles Stdio_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

Ltac showregsM :=
  lazymatch goal with
  | |- context [MS ?R _ _ _ _ _ _] =>
      let pr n := (let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
                   let v := eval cbv beta iota delta [tget mkR] in (tget p R) in idtac n ":=" v) in
      pr 1%Z; pr 2%Z; pr 8%Z; pr 9%Z; pr 10%Z; pr 11%Z; pr 12%Z; pr 13%Z; pr 14%Z; pr 15%Z; pr 18%Z; pr 19%Z; pr 20%Z; pr 21%Z; pr 22%Z
  end.

Definition STDIO_WRITE : Z := 0x16644.
Definition STDIO_WRITE_DEPTH : Z := 112.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition iovs_of (buf s : list Z) : list (list Z) :=
  match buf with [] => [s] | _ => [buf; s] end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zlength_to_bytes : forall l, zlength (to_bytes l) = zlength l.
Proof. intros l. unfold zlength, to_bytes. rewrite length_map. reflexivity. Qed.
Lemma length_to_bytes : forall l, length (to_bytes l) = length l.
Proof. intros l. unfold to_bytes. apply length_map. Qed.
Lemma zlength_skipn : forall {A} n (l : list A), zlength (skipn n l) = zlength l - Z.of_nat (Nat.min n (length l)).
Proof. intros A n l. unfold zlength. rewrite length_skipn. Local Ltac2 Set LiaHints.tbl := fun () => "0010=47821050258.3000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma to_bytes_skipn : forall n l, to_bytes (skipn n l) = skipn n (to_bytes l).
Proof. intros n l. unfold to_bytes. rewrite skipn_map. reflexivity. Qed.
Lemma iov_total_1 : forall b, iov_total [b] = zlength b.
Proof. intros b. unfold iov_total, zlength. cbn. rewrite app_nil_r. reflexivity. Qed.
Lemma iov_total_2 : forall a b, iov_total [a; b] = zlength a + zlength b.
Proof. intros a b. unfold iov_total, zlength. cbn. rewrite app_nil_r, length_app. Local Ltac2 Set LiaHints.tbl := fun () => "0010=62108319258.2000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Section StdioWrite.
  Context {St : Type}.

  Definition stdio_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (Fp : Z) (flags : word) (B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
      (l : Z) (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - STDIO_WRITE_DEPTH, bv_unsigned sp); (Fp + 32, Fp + 64)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' Fp (file_cells flags (B + bufsize) B B wfn B bufsize fd mode lbf tail)
      /\ ssp_cells m' canary
      /\ st' = st.

  Section Body.
    Variables (ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (m : mem) (st : St) (Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
              (buf s : list Z) (S lo : Z) (canary : word).
    Local Notation q := (bv_unsigned sp + -112).
    Let POST := stdio_write_post ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
                                 (zlength s) lo canary m st.
    Hypothesis FD : fd = 1 \/ fd = 2.
    Hypothesis LO : lo <= bv_unsigned sp - STDIO_WRITE_DEPTH.
    Hypothesis GLO : GLOBALS_TOP <= lo.
    Hypothesis Fp0 : 0 <= Fp. Hypothesis FPLO : Fp + 232 <= lo.
    Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
    Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
    Hypothesis B0 : 0 <= B. Hypothesis BS0 : 0 <= bufsize. Hypothesis BUFLE : zlength buf <= bufsize. Hypothesis BShi : B + bufsize < 2^64.
    Hypothesis S0 : 0 <= S < 2^64. Hypothesis Shi : S + zlength s <= 2^64.
    (* [comment removed for export] *)
    Hypothesis SP47 : bv_unsigned sp < 2^47. Hypothesis B47 : B + bufsize <= 2^47. Hypothesis S47 : S + zlength s <= 2^47.
    Hypothesis SEPS : s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S)).
    Hypothesis SEPB : buf = [] \/ ((B + zlength buf <= lo \/ bv_unsigned sp <= B) /\ (B + zlength buf <= Fp + 32 \/ Fp + 64 <= B)).
    Hypothesis FC0 : rw_cells usegs m Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail).
    Hypothesis ST0 : stk usegs m lo (bv_unsigned sp).
    Hypothesis SSP0 : ssp_cells m canary.
    Hypothesis MI0 : mem_inv usegs m.
    Hypothesis BUFB : bytes_at usegs m B (to_bytes buf).
    Hypothesis SRC : bytes_at usegs m S (to_bytes s).

    (* [comment removed for export] *)
    Definition frame (j0 : list byte) (w1 w2 w3 w4 : word) : list cell :=
      [CB 8 j0; C8 w1; C8 w2; C8 w3; C8 w4; C8 canary; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra].

    (* [comment removed for export] *)
    Definition data_ok (p : Z) (l : list Z) : Prop :=
      bytes_at usegs m p (to_bytes l)
      /\ p + zlength l <= 2^47
      /\ (l = [] \/ ((p + zlength l <= lo \/ bv_unsigned sp <= p) /\ (p + zlength l <= Fp + 32 \/ Fp + 64 <= p))).

    #[using="Type"] Lemma data_ok_task : forall p l, data_ok p l -> p + Z.of_nat (length (to_bytes l)) <= 0x800000000000.
    Proof. intros p l (_ & H & _). rewrite length_to_bytes. unfold zlength in H. exact H. Qed.

    (* [comment removed for export] *)
    Definition iov_rel (iov : list (list Z)) (iovp iovcnt : Z) (w1 w2 w3 w4 : word) : Prop :=
      match iov with
      | [b] => iovp = q + 24 /\ iovcnt = 1 /\ w4 = Z_to_bv 64 (zlength b) /\ data_ok (bv_unsigned w3) b
      | [a; b] => iovp = q + 8 /\ iovcnt = 2 /\ w2 = Z_to_bv 64 (zlength a) /\ w4 = Z_to_bv 64 (zlength b)
               /\ data_ok (bv_unsigned w1) a /\ data_ok (bv_unsigned w3) b
      | _ => False
      end.

    #[using="buf s LO FPLO"] Lemma data_ok_now : forall m1 p l,
      data_ok p l -> munch [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m m1 ->
      bytes_at usegs m1 p (to_bytes l).
    Proof.
      intros m1 p l (BA & _ & SEP) MU. pose proof (bytes_at_bound _ _ _ _ BA) as BB. rewrite length_to_bytes in BB.
      destruct SEP as [-> | [S1 S2]].
      - apply bytes_at_nil. cbn in BB. Local Ltac2 Set LiaHints.tbl := fun () => "0020>31165936320.6647761750701.6900000400CS2BBS2LO4FPLO2S12S2".
lia.
      - apply (bytes_at_transport _ _ _ m1 _ _ BA MU). cbn [disjoint_from]. rewrite length_to_bytes.
        unfold zlength, STDIO_WRITE_DEPTH in *. lia.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    #[using="buf s FPLO"] Lemma data_ok_skipn : forall p l k, data_ok p l -> 0 <= k <= zlength l -> data_ok (p + k) (skipn (Z.to_nat k) l).
    Proof.
      intros p l k (BA & T47 & SEP) Hk. pose proof (bytes_at_bound _ _ _ _ BA) as BB. rewrite length_to_bytes in BB.
      Local Ltac2 Set LiaHints.tbl := fun () => "0070>17718774308.7134019840975.6934245929091.7149058408312.6854969821204.6956850834073.6959308586510.6800000?00G00Q00R00V00Z00hS4FPLO2S12Hk2NES3T472HkS2S22Hk2NESS2HkS2HkS3T472NE2BB2Hk".
split; [|split; [rewrite zlength_skipn; unfold zlength in *; lia|]].
      - rewrite to_bytes_skipn. replace (p + k) with (p + Z.of_nat (Z.to_nat k)) by lia.
        rewrite <- (firstn_skipn (Z.to_nat k) (to_bytes l)) in BA. apply bytes_at_app in BA as [_ BA].
        rewrite length_firstn, length_to_bytes in BA.
        replace (Nat.min (Z.to_nat k) (length l)) with (Z.to_nat k) in BA by (unfold zlength in Hk; lia).
        exact BA.
      - destruct (Z.eq_dec k (zlength l)) as [->|NE].
        + left. apply skipn_all2. unfold zlength. lia.
        + destruct SEP as [-> | [S1 S2]]. { exfalso. unfold zlength in *. cbn in *. lia. }
          right. rewrite zlength_skipn. unfold zlength in *. split; lia.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    (* [comment removed for export] *)
    #[using="buf s FPLO"] Lemma data_ok_skipn_w : forall p l k, data_ok p l -> 0 <= k <= zlength l ->
      data_ok (bv_unsigned (Z_to_bv 64 (p + k))) (skipn (Z.to_nat k) l).
    Proof.
      intros p l k D Hk. pose proof (bytes_at_bound _ _ _ _ (proj1 D)) as BB. rewrite length_to_bytes in BB.
      change (Z.of_nat (length l)) with (zlength l) in BB. pose proof (proj1 (proj2 D)) as T47.
      Local Ltac2 Set LiaHints.tbl := fun () => "0010=5446587155.6800000;S2Hk2BB3T47".
rewrite unsigned_lit by lia. apply data_ok_skipn; assumption.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    (* [comment removed for export] *)
    #[using="Type"] Lemma frame_iov2 : forall m1 j0 w1 w2 w3 w4, rw_cells usegs m1 q (frame j0 w1 w2 w3 w4) ->
      bytes_at usegs m1 (bv_unsigned sp + -104) (iovec_bytes [(w1, w2); (w3, w4)]).
    Proof.
      intros m1 j0 w1 w2 w3 w4 FR.
      change (frame j0 w1 w2 w3 w4) with ([CB 8 j0] ++ [C8 w1; C8 w2; C8 w3; C8 w4] ++ [C8 canary; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]) in FR.
      apply rw_cells_app in FR as [_ FR]. apply rw_cells_app in FR as [FR _].
      cbn [cells_size csize Nat.add] in FR. Local Ltac2 Set LiaHints.tbl := fun () => "0010>45674267130.68000001S".
replace (q + Z.of_nat 8) with (bv_unsigned sp + -104) in FR by lia.
      eapply bytes_at_ext; [exact (rw_cells_bytes_at _ _ _ _ FR)|]. cbn [cells_bytes cbytes iovec_bytes flat_map fst snd].
      rewrite !app_nil_r, <- ?app_assoc. reflexivity.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
    #[using="Type"] Lemma frame_iov1 : forall m1 j0 w1 w2 w3 w4, rw_cells usegs m1 q (frame j0 w1 w2 w3 w4) ->
      bytes_at usegs m1 (bv_unsigned sp + -88) (iovec_bytes [(w3, w4)]).
    Proof.
      intros m1 j0 w1 w2 w3 w4 FR.
      change (frame j0 w1 w2 w3 w4) with ([CB 8 j0; C8 w1; C8 w2] ++ [C8 w3; C8 w4] ++ [C8 canary; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]) in FR.
      apply rw_cells_app in FR as [_ FR]. apply rw_cells_app in FR as [FR _].
      cbn [cells_size csize Nat.add] in FR. Local Ltac2 Set LiaHints.tbl := fun () => "0010>62417289978.68000001S".
replace (q + Z.of_nat 24) with (bv_unsigned sp + -88) in FR by lia.
      eapply bytes_at_ext; [exact (rw_cells_bytes_at _ _ _ _ FR)|]. cbn [cells_bytes cbytes iovec_bytes flat_map fst snd].
      rewrite !app_nil_r, <- ?app_assoc. reflexivity.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    (* [comment removed for export] *)
    #[using="LO GLO Fp0 FPLO FSEP1 FSEP2"] Lemma ok_path : forall (m1 : mem) (j0 : list byte) (w1 w2 w3 w4 : word)
        (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31 : word),
      rw_cells usegs m1 q (frame j0 w1 w2 w3 w4) ->
      rw_cells usegs m1 Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
      rw_cells usegs m1 got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells usegs m1 ssp_guard [C8 canary] ->
      mem_inv usegs m1 ->
      munch [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m m1 -> wmono usegs m m1 ->
      stk usegs m1 lo q ->
      evt usegs (POST tt st)
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
                   x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ssp_guard) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x166d8) fc None m1 (seg_rom usegs)).
    Proof.
      intros until x31. intros FR FC GOT GUARD MI MU WM ST.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      unfold got_ssp, ssp_guard, STDIO_WRITE_DEPTH, GLOBALS_TOP, frame, file_cells in *.
      Local Ltac2 Set LiaHints.tbl := fun () => "00M0?11091651096.95 1183002124.107 1263254915.102 13253656393.1051573081545.107 1735888094.107 18246208652.10519507795017.10725071629079.10525071629079.10725518734025.10526279284492.10727576742750.10531546306377.10736781431939.10238898478558.10740420408451.1034253879427.103 44612541059.1044496343073.96  45098659203.10248475009685.96 50201051337.1075666901214.107 60172785283.10361383599491.10363405537758.10764757487454.1058940551555.103 00000100500600I00\00c00g00l00m00n01301701>01C01D01K01L01M01N01O01P01T01g01n01o02002702>02?SS2HBSS2LO3GLO4FPLO5FSEP2S2LO3GLO4FPLO5FSEP2S5FSEP2S2HBS3Fp0SSS3Fp0S2HBS5FSEP1S3Fp0SS5FSEP2SSSSSS2LOS2LO3GLO4FPLO5FSEP2S5FSEP1SSS5FSEP1S5FSEP2S".
do 7 step.
      do 3 step. if_false. do 10 step.
      release_frame FR ST (bv_unsigned sp).
      subst POST. unfold stdio_write_post, STDIO_WRITE_DEPTH, file_cells, ssp_cells, got_ssp, ssp_guard. sys_finish.
      reflexivity.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    (* [comment removed for export] *)
    Ltac sysret_fast ret :=
      zstep; zstep; zstep; zstep;
      let Hr := fresh "Hr" in (if_cases Hr; zify_cond Hr); [ | exfalso; lia ];
      zstep; replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    (* [comment removed for export] *)
    #[using="FD LO GLO Fp0 FPLO FSEP1 FSEP2 SP47"] Lemma loop_L2 : forall (fuel : nat) (iov : list (list Z)) (c : Z) (m1 : mem) (j0 : list byte) (w1 w2 w3 w4 : word) (iovp iovcnt : Z)
        (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
      iov_rel iov iovp iovcnt w1 w2 w3 w4 ->
      rw_cells usegs m1 q (frame j0 w1 w2 w3 w4) ->
      rw_cells usegs m1 Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
      rw_cells usegs m1 got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells usegs m1 ssp_guard [C8 canary] ->
      mem_inv usegs m1 ->
      munch [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m m1 -> wmono usegs m m1 ->
      stk usegs m1 lo q ->
      0 <= c < iov_total iov -> iov_total iov <= 67108864 ->
      implM usegs (stdio_write_loop fuel fd (iov_advance iov c)) st POST
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
                   (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 iovcnt) (Z_to_bv 64 iovp) x20 (Z_to_bv 64 ssp_guard)
                   (Z_to_bv 64 (iov_total iov)) s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x16764) fc None m1 (seg_rom usegs)).
    Proof.
      induction fuel as [|fuel IH]; intros until x31; intros IR FR FC GOT GUARD MI MU WM ST Hc TOT.
      { cbn [stdio_write_loop]. apply implM_unr. }
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      unfold got_ssp, ssp_guard, STDIO_WRITE_DEPTH, GLOBALS_TOP, frame, file_cells in *.
      (* [comment removed for export] *)
      Ltac cont IH total iov' FR FC GOT GUARD MI MU WM ST DATA :=
        let rsp := fresh "rsp" in let ans := fresh "ans" in let Hdec := fresh "Hdec" in let ci := fresh "ci" in
        let Hans := fresh "Hans" in let Hcase := fresh "Hcase" in let Keq := fresh "Keq" in
        intros rsp ans Hdec; apply dec_writev_Some in Hdec as (ci & -> & Hans & Hcase);
        replace (iov_total iov') with total in Hcase by (rewrite ?iov_total_1, ?iov_total_2, ?zlength_skipn; unfold zlength in *; lia);
        apply implM_from_evt; sys_nret;
        sysret_fast 0x1675c%Z;
        zstep; zstep; (if_cases Keq; zify_cond Keq);
        [ apply evt_done; replace (ans =? iov_total iov') with true by (symmetry; apply Z.eqb_eq; rewrite ?iov_total_1, ?iov_total_2, ?zlength_skipn; unfold zlength in *; lia);
          apply implM_ret;
          eapply ok_path; first [exact FR | exact FC | exact GOT | exact GUARD | exact MI | exact MU | exact WM | exact ST]
        | apply evt_done; replace (ans =? iov_total iov') with false by (symmetry; apply Z.eqb_neq; rewrite ?iov_total_1, ?iov_total_2, ?zlength_skipn; unfold zlength in *; lia);
          replace (Z_to_bv 64 total : word) with (Z_to_bv 64 (iov_total iov') : word)
            by (f_equal; rewrite ?iov_total_1, ?iov_total_2, ?zlength_skipn; unfold zlength in *; lia);
          lazymatch type of FR with rw_cells _ ?mf _ (CB 8 ?j0 :: C8 ?v1 :: C8 ?v2 :: C8 ?v3 :: C8 ?v4 :: _) =>
            eapply (IH iov' _ mf j0 v1 v2 v3 v4) end;
          first [exact FR | exact FC | exact GOT | exact GUARD | exact MI | exact MU | exact WM | exact ST
                | rewrite ?iov_total_1, ?iov_total_2, ?zlength_skipn; unfold zlength in *; lia
                | cbn [iov_rel]; DATA ] ].
      destruct iov as [|a [|b [|? ?]]]; try contradiction.
      - (* [comment removed for export] *)
        rename a into b. destruct IR as (-> & -> & -> & DB).
        pose proof (bytes_at_bound _ _ _ _ (proj1 DB)) as BB. rewrite length_to_bytes in BB.
        change (Z.of_nat (length b)) with (zlength b) in BB.
        rewrite iov_total_1 in *.
        Local Ltac2 Set LiaHints.tbl := fun () => "02I0?11444581763.10711444581763.11311444581763.11711875767022.11111875767022.11511910133012.10612191364848.10712191364848.11112209782646.11412209782646.11813945494591.10614539528123.10517256834476.11017611149315.11217857850634.10217857850634.10618004552480.1081807047817.101 18292433221.11219446761366.10219446761366.10621729101182.11721816137573.10821816137573.11222194145798.10222194145798.10622856607214.11523734946939.10823734946939.11224531599015.11324531599015.11724730433221.10824730433221.11224732548164.10724732548164.11124929101479.11725071629079.11125071629079.11325071629079.11525071629079.11725203823395.99 25203950530.10226733586808.10826733586808.1122728429678.117 27399541823.10827399541823.11228886576219.11229126480746.11229128493451.10629377718491.10829379998266.10231339131998.10231339131998.10631847340711.11131847340711.11532534202715.11033680001082.11133680001082.11533781268846.11333781268846.11734329296772.11234349563011.11534990166189.11235484866318.1053971437694.113 3971437694.117 40104401007.10240104401007.10640196840212.10240196840212.10640928162421.1124242606947.108 4242606947.112 43570532452.10243570532452.10643725716909.11243727857484.10644762256494.11745221239098.11545607773934.11145607773934.11545659830526.11145659830526.11545797402170.106469426752.102  469426752.106  4821892890.106 48559260418.10648563437846.10848563437846.11253085287934.11554055154495.10254055154495.10654763372166.10654770104018.11654772201172.11354772201172.11454772201178.11554775866482.1055494439228.115 55162595506.10155333271071.10155333271071.10455336861632.11055336861632.11455336861646.11155336861646.11555338958790.11355338958790.11655345854354.10255345854354.10655460987188.10856145720764.11356145720764.11756238753134.11356238753134.117563227834.117  56582466030.11557297723570.11257745675194.11357745675194.11759308587409.10759308587409.11159308634759.10259308634759.10659321217802.10159321217802.10459498428761.1055955160707.111 5955160707.115 5968447876.108 5968447876.112 61895388678.11361897485824.10961897485824.11061897485824.11461906576978.10262175402556.11162175402556.11563920274819.11063920274819.1176495440936.112 65461747917.10265461747917.10666143077031.11567750960678.11468186327228.1178395091436.106 8937270820.114 9063607643.102 9063607643.106 9765216476.106 00000100200300;00C00P00Q00R00S00T00Z00b00l01501601701801<01=01A01E01X01f02902:02;02C02Q02d02e02f03503D03S03b03c03d03e03f03g03h03i03n04>04F04N04[04\04c04j04n05205305405505605?05E05K05S05[05\05]05f05g06:06M06Q06[06h07507@07H07V07W07X07a07j08208808@08H08[08n09709809909:09>09B09L09_09e09k0:>0:I0:\0:g0;70;G0;K0;L0;T0;\0;e0;n0<70<@0<I0<R0<[0<d0<h0<l0=00=80=@0=F0=N0=X0=^0=d0>50>L0>S0>c0?00?=0?C0?D0?E0?F0?G0?O0?W0?_0?j0@20@60@:0@;0@<0@J0@N0@R0@S0@c0@g0A10A?0AD0AW0A_SSSS2LO3GLOS2LO3GLOS2LO3GLO4SP47SSSSS4SP47S6NODROPS2Hc2Za2KdS2Hc4DROPFFFS2HcFS2FDS2FDS2LO3GLO4FPLO5FSEP2S2Hc5Hcase3KeqS2Hc4DROP5Hcase3KeqFFS2LO3GLOS2Hc5Hcase3KeqS2Hc4DROP5Hcase3KeqSSS2Hc4Hans5HcaseS2Hc4Hans5HcaseS2Hc4Hans5HcaseS2Hc4Hans5HcaseSSSSSSSS3TOTS2Hc3TOT2Za4DROPS2LO3GLOS2Hc3KeqS2Hc4DROP3KeqFS2Hc2KdS2Hc2KdS2HcS2HcFFSSS2Hc4DROPS4SP47S4SP47S2LO3GLOS2LO3GLOSSS2Hc4DROPSS2LO3GLO4FPLO5FSEP2S2LO3GLO4FPLO5FSEP2S2HcS2Hc2Za2KdS2LO3GLO4SP47S2LO3GLO4SP47S3TOT2Za2KdS2Hc3TOTS2Hc3TOT2Za2KdSSS2Hc4DROPS2Hc4DROPS2LO3GLOS4SP47S2LO3GLOS2LO3GLOS2LO3GLO4FPLO5FSEP2S2LO3GLO4FPLO5FSEP2S2Hc4DROPFFSS2HcS2HcS2Hc2Za2KdS2LO3GLO4FPLO5FSEP2S4SP47S4SP47S2Hc3TOT2Za4DROP2ZbS3TOT2Za2ZbS2Hc3TOT2Za4DROP2ZbS3TOT2Za2ZbS2Hc3TOT2Za4DROPS2Hc3TOT2Za4DROPS2HBSS2Hc3TOTS2Hc3TOTS2Hc4KnegS2Hc4KnegS2Hc4KnegS2Hc4KnegS2Hc4KnegS2Hc4KnegS2Hc4KnegS2Hc4KnegS2HcS2HBS2HBS2LO3GLOS2LO3GLOS4SP47S2LO3GLOS2Hc2Za2KdS4SP47S4SP47S2Hc3TOT5Hcase2HrS2Hc3TOT2Za2Kd5Hcase2HrS2Hc2KdS4DROP2Kd6NODROPS2Hc3TOT4KnegS2Hc3TOT4KnegS4DROPSSSSS3TOT2ZbS3TOT2ZbS3TOT2ZbS3TOT2Za2ZbS3TOT2ZbS2HBS2HBSSS2Hc2Za2Kd3KeqS2FDS2FDSS2Hc3TOT2Za4DROPS2HBS6NODROP1lS2Hc3TOT2Za2KdS3TOTS2Hc3TOT2Za4DROP2KdS4DROP1n".
assert (Zb : 0 <= zlength b) by (unfold zlength; lia).
        cbn [stdio_write_loop]. apply implM_sysk.
        zstep. if_cases Kneg; zify_cond Kneg. { exfalso. lia. }
        zstep. zstep.
        replace (zlength b <? c) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
        change (iov_advance [b] c) with [skipn (Z.to_nat c) b].
        do 5 zstep. rewrite Z.land_0_l. zstep. rewrite Z.sub_0_r. zstep. zstep. zstep.
        if_cases Kd; zify_cond Kd. 2:{ exfalso. lia. }
        zstep. zstep. zstep. do 8 zstep.
        replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd : word) by (symmetry; apply sx32_small; lia).
        step_ecall.
        split.
        { at_node_red; split_spine; try reflexivity; try lia;
            try (cbn [map concat length]; rewrite ?app_nil_r, ?length_app, ?length_to_bytes, ?length_skipn; unfold zlength in *; lia);
            try (rewrite unsigned_lit by lia; cbn [map length]; lia).
          eexists [(_, _)]. split.
          + rewrite unsigned_lit by lia. eapply frame_iov1. exact FR.
          + constructor; [|constructor]. split; [|split].
            * cbn [snd]. rewrite length_to_bytes, length_skipn. f_equal. unfold zlength in *. lia.
            * cbn [fst]. apply (data_ok_task _ _ (data_ok_skipn_w _ _ c DB ltac:(lia))).
            * cbn [fst]. apply (data_ok_now _ _ _ (data_ok_skipn_w _ _ c DB ltac:(lia)) MU). }
        cont IH (zlength b - c) [skipn (Z.to_nat c) b] FR FC GOT GUARD MI MU WM ST
             ltac:(idtac; split; [lia|]; split; [reflexivity|]; split; [f_equal; rewrite zlength_skipn; unfold zlength in *; lia|];
                   apply (data_ok_skipn_w _ _ c DB ltac:(lia))).
      - (* [comment removed for export] *)
        destruct IR as (-> & -> & -> & -> & DA & DB).
        pose proof (bytes_at_bound _ _ _ _ (proj1 DA)) as BA. pose proof (bytes_at_bound _ _ _ _ (proj1 DB)) as BB.
        rewrite length_to_bytes in BA, BB.
        change (Z.of_nat (length a)) with (zlength a) in BA. change (Z.of_nat (length b)) with (zlength b) in BB.
        rewrite iov_total_2 in *.
        assert (Za : 0 <= zlength a) by (unfold zlength; lia). assert (Zb : 0 <= zlength b) by (unfold zlength; lia).
        cbn [stdio_write_loop]. apply implM_sysk.
        zstep. if_cases Kneg; zify_cond Kneg. { exfalso. lia. }
        zstep. zstep.
        destruct (Z.ltb_spec0 (zlength a) c) as [DROP|NODROP].
        + (* [comment removed for export] *)
          replace (zlength a <? c) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
          replace (iov_advance [a; b] c) with [skipn (Z.to_nat (c - zlength a)) b]
            by (cbn [iov_advance]; destruct (Z.ltb_spec0 (zlength a) c); [reflexivity|lia]).
          do 5 zstep.
          replace (Z.land 18446744073709551615 (zlength a)) with (zlength a)
            by (change 18446744073709551615 with (2^64-1); rewrite zb_land_mask_l by lia; rewrite Z.mod_small by lia; reflexivity).
          zstep. zstep. zstep. zstep. if_cases Kd; zify_cond Kd. { exfalso. lia. }
          zstep. zstep.
          do 8 zstep.
          replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd : word) by (symmetry; apply sx32_small; lia).
          zstep. zstep. step_ecall.
          split.
          { at_node_red; split_spine; try reflexivity; try lia;
              try (cbn [map concat length]; rewrite ?app_nil_r, ?length_app, ?length_to_bytes, ?length_skipn; unfold zlength in *; lia);
              try (rewrite unsigned_lit by lia; cbn [map length]; lia).
            eexists [(_, _)]. split.
            + rewrite unsigned_lit by lia. eapply frame_iov1. exact FR.
            + constructor; [|constructor]. split; [|split].
              * cbn [snd]. rewrite length_to_bytes, length_skipn. f_equal. unfold zlength in *. lia.
              * cbn [fst]. apply (data_ok_task _ _ (data_ok_skipn_w _ _ (c - zlength a) DB ltac:(lia))).
              * cbn [fst]. apply (data_ok_now _ _ _ (data_ok_skipn_w _ _ (c - zlength a) DB ltac:(lia)) MU). }
          cont IH (zlength a + zlength b - c) [skipn (Z.to_nat (c - zlength a)) b] FR FC GOT GUARD MI MU WM ST
               ltac:(idtac; split; [lia|]; split; [reflexivity|]; split; [f_equal; rewrite zlength_skipn; unfold zlength in *; lia|];
                     apply (data_ok_skipn_w _ _ (c - zlength a) DB ltac:(lia))).
        + (* [comment removed for export] *)
          replace (zlength a <? c) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
          replace (iov_advance [a; b] c) with [skipn (Z.to_nat c) a; b]
            by (cbn [iov_advance]; destruct (Z.ltb_spec0 (zlength a) c); [lia|reflexivity]).
          do 5 zstep. rewrite Z.land_0_l. zstep. rewrite Z.sub_0_r. zstep. zstep. zstep.
          if_cases Kd; zify_cond Kd. 2:{ exfalso. lia. }
          zstep. zstep. zstep. do 8 zstep.
          replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd : word) by (symmetry; apply sx32_small; lia).
          step_ecall.
          split.
          { at_node_red; split_spine; try reflexivity; try lia;
              try (cbn [map concat length]; rewrite ?app_nil_r, ?length_app, ?length_to_bytes, ?length_skipn; unfold zlength in *; lia);
              try (rewrite unsigned_lit by lia; cbn [map length]; lia).
            eexists [(_, _); (_, _)]. split.
            + rewrite unsigned_lit by lia. eapply frame_iov2. exact FR.
            + constructor; [|constructor; [|constructor]]; (split; [|split]).
              * cbn [snd]. rewrite length_to_bytes, length_skipn. f_equal. unfold zlength in *. lia.
              * cbn [fst]. apply (data_ok_task _ _ (data_ok_skipn_w _ _ c DA ltac:(lia))).
              * cbn [fst]. apply (data_ok_now _ _ _ (data_ok_skipn_w _ _ c DA ltac:(lia)) MU).
              * cbn [snd]. rewrite length_to_bytes. reflexivity.
              * cbn [fst]. apply (data_ok_task _ _ DB).
              * cbn [fst]. apply (data_ok_now _ _ _ DB MU). }
          cont IH (zlength a + zlength b - c) [skipn (Z.to_nat c) a; b] FR FC GOT GUARD MI MU WM ST
               ltac:(idtac; split; [lia|]; split; [reflexivity|]; split; [f_equal; rewrite zlength_skipn; unfold zlength in *; lia|];
                     split; [reflexivity|]; split; [apply (data_ok_skipn_w _ _ c DA ltac:(lia)) | exact DB]).
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    (* [comment removed for export] *)
    #[using="wend FD LO GLO Fp0 FPLO FSEP1 FSEP2 B0 BS0 BUFLE S0 SP47 B47 S47 SEPS SEPB FC0 ST0 SSP0 MI0 BUFB SRC"] Lemma stdio_write_body : forall (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      implM usegs (stdio_write (St:=St) fd buf s) st POST
            (MS (mkR ra sp gp tp x5 x6 x7 s0i s1i (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 (zlength s)) x13 x14 x15 x16 x17
                     s2i s3i s4i s5i s6i s7 s8 s9 s10 s11 x28 x29 x30 x31)
                F (Z_to_bv 64 0x16644) fc None m (seg_rom usegs)).
    Proof.
      intros.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof SSP0 as SSP. destruct SSP as [GOT GUARD]. pose proof FC0 as FC. pose proof ST0 as ST. pose proof MI0 as MI.
      unfold got_ssp, ssp_guard, STDIO_WRITE_DEPTH, GLOBALS_TOP, file_cells in *.
      pose proof (bytes_at_bound _ _ _ _ BUFB) as BB. pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
      rewrite length_to_bytes in BB, BS. change (Z.of_nat (length buf)) with (zlength buf) in BB. change (Z.of_nat (length s)) with (zlength s) in BS.
      Local Ltac2 Set LiaHints.tbl := fun () => "02Z0?11444581763.98 11875767022.99 11910081892.99 12080262273.98 1263254915.97  13322745511.97 13518985818.98 13716328399.10013945275471.99 14013085244.99 15442153454.98 16629598702.99 17366728278.10017857934714.94 17857934714.99 19415681262.98 19446718438.94 19446718438.99 1974571836.96  20038558908.98 21155567546.98 21729101182.97 21816137573.10521890222206.98 22163107130.99 22193934966.94 22193934966.99 22856607214.98 23734946939.10524427909389.84 24531599015.98 24630998586.98 24730433221.10024730433221.10524732548164.10424732548164.99 24929101479.97 25071629079.96 25071629079.97 25071629079.98 25071629079.99 26049497404.99 26477173415.96 26733586808.10526968004263.98 2728429678.97  27399541823.10529085018494.98 29414937255.99 29906675326.98 30196181434.98 30258623470.96 30396535790.98 31339211822.94 31339211822.99 31651016162.94 31653113715.10031757500965.10331847340711.99 31913473429.91 32017482750.96 32070795196.98 32651489978.97 33140611582.99 33680001082.99 33781268846.98 34329296772.10534349563011.98 36166524798.97 36608995310.96 36781431939.96 37360254574.97 38098496572.98 38168338087.98 39400444670.98 3971437694.98  40196653924.94 40420408451.98 40623921831.99 41422295406.98 4253879427.99  42619492738.10342621589898.10142621589899.10042628419649.10542628727976.97 42630517456.94 42630517456.99 42849687948.97 42852061172.99 42857743526.10342859840686.10142859840687.10043055481388.88 43570612244.94 44109304508.97 44250622631.98 4461167854.98  44612541059.99 44762256494.97 45098659203.98 45221239098.98 45228683929.10045257912942.97 45607773934.99 45659830526.99 46232973498.98 469350960.94   469350960.99   4822099818.99  48606131566.98 49691078311.98 49746962786.83 49961654863.95 50134779708.98 51820114670.99 53085287934.98 53510313882.10153699986484.10554055365455.94 54261855034.96 54794350626.1005494439228.98  55459467943.98 55509061630.98 56020583278.98 56145720764.98 56238753134.98 563227834.97   56336554256.82 5646517998.99  56582466030.98 56625144942.98 57745675194.98 58088949744.10458088949744.99 58102910582.10658102910582.11159308587409.10459308587409.99 59308634497.94 59308634497.99 59314955108.97 5955160707.99  59586984046.98 5968447876.100 60172785283.98 60330452198.90 61383599491.98 62175402556.99 62801085934.99 6340307024.81  63920274819.97 64302924052.94 64302924052.99 64305021829.10064305021829.10565461573821.94 65461573821.99 65805175866.99 66143077031.98 67604033390.98 67802098942.99 68186327228.97 8002142652.98  8166968988.100 8583720762.98  8927061985.105 8940551555.98  9063429419.99  00000100900F00G00H00I00Q00R00X00\00d00l01101201301;01?01C01G01K01Q01d02602I02O02P02Q02Y03103603703=03I03b04;04G04H04I04J04K04L04P04Q04W04X04`04e05805905L05R05Z05b05c05d05m06606706806906L06P06V06i06o07707807907L07T07U07]07a07b08508H08U08V08W08_08`08l09809D09V09h0:70:I0:[0:m0;>0;O0;`0;d0;e0;i0;j0<20<30<;0<<0<B0<N0<V0<^0=10=70=80=90=:0=B0=C0=N0=O0=S0=[0=n0=o0>00>60><0>J0>N0>O0>b0>j0>n0?60?<0?=0?E0?M0?U0?[0?\0?]0?^0?_0@;0@P0@T0@\0@c0@d0@l0@m0@n0@o0A00A40A<0A=0A>0AB0AF0AJ0AN0AR0AV0A\0A]0Ae0B80B<0B@0BN0BT0Ba0Bb0BhSS2LO3GLOS2LO3GLO4SP47SSSS3XNZ2XRFS4SP47S2HBS2LO3GLOS2LO3GLOS3KeqFFS2LO3GLOS2FDS2FDS2HBS2HBS4SP47S2LO3GLO4FPLO5FSEP2S2Zb3XNZ2XR2Kb3KeqS2LO3GLO4FPLO5FSEP2S4SP47FFS2LO3GLOS2Zb3XNZ2XR2Kb5Hcase3KeqS3S47SS4SP47S4Hans5HcaseS2Zb3XNZ2XR2Kb4Hans5HcaseS2Zb3XNZ2XR2Kb4Hans5HcaseS4Hans5HcaseSSSSSS2HBSS4LENSSS2LO3GLOS3KeqS2LO3GLO4FPLO5FSEP2SS2LO3GLO4FPLO5FSEP2S4SP47S2LO3GLOS2LO3GLOFFS2Zb4LENSS2Zb4LENSSSSS2LO3GLO4FPLO5FSEP2S2HBS4SP47S2LO3GLO4FPLO5FSEP2S4SP47S2LO3GLOSSS2LO3GLO4FPLO5FSEP2S2LO3GLOSS2LO3GLOS2HBSS2LO3GLO4FPLO5FSEP2S2LO3GLO4FPLO5FSEP2S2LO3GLO4SP47SSS2LO3GLOSS2B03BS03B47S2B03BS03B47S2B03BS03B47S2B05BUFLE3B473NB1S2B05BUFLE3B473NB1S2B03BS03B472KbS2B05BUFLE3B473NB1S5BUFLE3B472BB3NB1S5BUFLE3B472BB3NB1S5BUFLE3B472BB2ZbS5BUFLE3B472BB2ZbS5BUFLE3B472BB2ZbS2LOSS2HBSS2LO3GLOSS2LO3GLOSS4SP47S2Zb2Zs4LENSS2LO3GLOS2LO3GLOS2LO3GLO4FPLO5FSEP2S4SP47FFSS2LO3GLOSS5BUFLE3B47SS2HBS2LO3GLOS2LO3GLO4FPLO5FSEP2SFS4SP47S4SP47S2Zs5Hcase3KeqS2HBSS2LO3GLO4FPLO5FSEP2S2LO3GLOS2HBS2LO3GLOS4SP47SS2LO3GLOS2LO3GLOS2LO3GLOS4SP47SSSSS2Zb4LENS3XNZ2XR2Kb5Hcase2HrS2Zb2Zs4LENS5Hcase2HrS2KbS3NB12KbS3NB11ESS2LO3GLOSSSSS2HBS2LO3GLOSSS2S0S2S0S2S0S2S0S2FDS2FDS4SP47SS2LO3GLOS2LO3GLO4FPLO5FSEP2S2HBS2HBS2Zs5Hcase3KeqS4SP47S2Zs4LENS3NB1SS4LENS".
assert (Zb : 0 <= zlength buf) by (unfold zlength; lia). assert (Zs : 0 <= zlength s) by (unfold zlength; lia).
      assert (DBUF : data_ok B buf) by (split; [exact BUFB | split; [lia | exact SEPB]]).
      assert (DS : data_ok S s) by (split; [exact SRC | split; [lia | exact SEPS]]).
      change (bytes_at usegs m S (to_bytes s)) with (boxed (bytes_at usegs m S (to_bytes s))) in SRC.
      change (bytes_at usegs m B (to_bytes buf)) with (boxed (bytes_at usegs m B (to_bytes buf))) in BUFB.
      pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m) as MU.
      pose proof (wmono_refl usegs m) as WM.
      unfold stdio_write, WRITE_MAX.
      destruct (Z.ltb_spec0 67108864 (zlength buf + zlength s)) as [BIG|LENS]. { apply implM_unr. }
      apply Z.nlt_ge in LENS.
      cbn [stdio_write_loop]. apply implM_sysk.
      carve_frame 112%nat ST.
      do 12 zstep. do 13 zstep.
      replace (B + zlength buf - B) with (zlength buf) in * by lia.
      lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => set (j0 := j) in FR end.
      (* [comment removed for export] *)
      Ltac cont0 total iov0 iovp iovcnt FR FC GOT GUARD MI MU WM ST DATA :=
        let rsp := fresh "rsp" in let ans := fresh "ans" in let Hdec := fresh "Hdec" in let ci := fresh "ci" in
        let Hans := fresh "Hans" in let Hcase := fresh "Hcase" in let Keq := fresh "Keq" in
        intros rsp ans Hdec; apply dec_writev_Some in Hdec as (ci & -> & Hans & Hcase);
        replace (iov_total iov0) with total in Hcase by (rewrite ?iov_total_1, ?iov_total_2; unfold zlength in *; lia);
        apply implM_from_evt; sys_nret;
        sysret_fast 0x166d4%Z;
        zstep; (if_cases Keq; zify_cond Keq);
        [ apply evt_done; replace (ans =? iov_total iov0) with false by (symmetry; apply Z.eqb_neq; rewrite ?iov_total_1, ?iov_total_2; unfold zlength in *; lia);
          let L := fresh "L" in
          lazymatch type of FR with rw_cells _ ?mf _ (CB 8 ?j0 :: C8 ?v1 :: C8 ?v2 :: C8 ?v3 :: C8 ?v4 :: _) =>
            pose proof (fun fuel x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 =>
                          loop_L2 fuel iov0 ans mf j0 v1 v2 v3 v4 iovp iovcnt x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31) as L end;
          cbv beta in L; rewrite ?iov_total_1, ?iov_total_2 in L; unfold ssp_guard in L;
          eapply L; clear L;
          first [exact FR | exact FC | exact GOT | exact GUARD | exact MI | exact MU | exact WM | exact ST
                | unfold zlength in *; lia
                | cbn [iov_rel]; DATA ]
        | apply evt_done; replace (ans =? iov_total iov0) with true by (symmetry; apply Z.eqb_eq; rewrite ?iov_total_1, ?iov_total_2; unfold zlength in *; lia);
          apply implM_ret;
          eapply ok_path; first [exact FR | exact FC | exact GOT | exact GUARD | exact MI | exact MU | exact WM | exact ST] ].
      destruct buf as [|b0 buf'] eqn:Ebuf; rewrite <- ?Ebuf in *.
      - (* [comment removed for export] *)
        replace (zlength buf) with 0 in FR |- * by (rewrite Ebuf; reflexivity).
        rewrite !Z.add_0_r, !Z.add_0_l. rewrite Z.lxor_nilpotent. change (Z.b2z (0 <? 0)) with 0.
        zstep. if_cases Kb; zify_cond Kb. 2:{ exfalso. lia. }
        zstep. zstep.
        replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd : word) by (symmetry; apply sx32_small; lia).
        zstep. change (0 + 1) with 1. zstep. zstep. zstep. step_ecall.
        split.
        { at_node_red; split_spine; try reflexivity; try lia;
            try (cbn [map concat length]; rewrite ?app_nil_r, ?length_app, ?length_to_bytes; unfold zlength in *; lia);
            try (rewrite unsigned_lit by lia; cbn [map length]; lia).
          eexists [(_, _)]. split.
          + rewrite unsigned_lit by lia. eapply frame_iov1. exact FR.
          + constructor; [|constructor]. split; [|split].
            * cbn [snd]. rewrite length_to_bytes. reflexivity.
            * cbn [fst]. rewrite unsigned_lit by lia. apply (data_ok_task _ _ DS).
            * cbn [fst]. rewrite unsigned_lit by lia. apply (data_ok_now _ _ _ DS MU). }
        cont0 (zlength s) [s] (bv_unsigned sp + -88) 1 FR FC GOT GUARD MI MU WM ST
              ltac:(idtac; split; [lia|]; split; [reflexivity|]; split; [reflexivity|]; rewrite unsigned_lit by lia; exact DS).
      - (* [comment removed for export] *)
        assert (NB1 : 1 <= zlength buf) by (rewrite Ebuf; unfold zlength; cbn [length]; lia).
        replace (match buf with [] => [s] | _ :: _ => [buf; s] end) with [buf; s] by (rewrite Ebuf; reflexivity).
        assert (XNZ : Z.lxor (B + zlength buf) B <> 0).
        { intros E. rewrite <- (Z.add_0_r B) in E at 2. apply Z.lxor_eq in E. lia. }
        pose proof (Z_lxor_range (B + zlength buf) B ltac:(lia) ltac:(lia)) as XR.
        replace (0 <? Z.lxor (B + zlength buf) B) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
        zstep. if_cases Kb; zify_cond Kb. 1:{ exfalso. lia. }
        zstep. zstep. zstep.
        replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd : word) by (symmetry; apply sx32_small; lia).
        zstep. change (1 + 1) with 2. zstep. zstep. zstep. step_ecall.
        split.
        { at_node_red; split_spine; try reflexivity; try lia;
            try (cbn [map concat length]; rewrite ?app_nil_r, ?length_app, ?length_to_bytes; unfold zlength in *; lia);
            try (rewrite unsigned_lit by lia; cbn [map length]; lia).
          eexists [(_, _); (_, _)]. split.
          + rewrite unsigned_lit by lia. eapply frame_iov2. exact FR.
          + constructor; [|constructor; [|constructor]]; (split; [|split]).
            * cbn [snd]. rewrite length_to_bytes. reflexivity.
            * cbn [fst]. rewrite unsigned_lit by lia. apply (data_ok_task _ _ DBUF).
            * cbn [fst]. rewrite unsigned_lit by lia. apply (data_ok_now _ _ _ DBUF MU).
            * cbn [snd]. rewrite length_to_bytes. reflexivity.
            * cbn [fst]. rewrite unsigned_lit by lia. apply (data_ok_task _ _ DS).
            * cbn [fst]. rewrite unsigned_lit by lia. apply (data_ok_now _ _ _ DS MU). }
        cont0 (zlength buf + zlength s) [buf; s] (bv_unsigned sp + -104) 2 FR FC GOT GUARD MI MU WM ST
              ltac:(idtac; split; [lia|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
                    rewrite !unsigned_lit by lia; split; [exact DBUF | exact DS]).
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  End Body.

  (* [comment removed for export] *)
  #[using="Type"] Lemma stdio_write_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
           (buf s : list Z) (S lo : Z) (canary : word),
      rw_cells usegs m Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
      bytes_at usegs m B (to_bytes buf) ->
      bytes_at usegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      (fd = 1 \/ fd = 2) ->
      stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDIO_WRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
      ssp_cells m canary -> mem_inv usegs m ->
      (0 <= Fp) -> (Fp + 232 <= lo) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (0 <= B) -> (0 <= bufsize) -> (zlength buf <= bufsize) -> (B + bufsize < 2^64) ->
      (0 <= S < 2^64) -> (S + zlength s <= 2^64) ->
      (bv_unsigned sp < 2^47) -> (B + bufsize <= 2^47) -> (S + zlength s <= 2^47) ->     (* [comment removed for export] *)
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S))) ->
      (buf = [] \/ ((B + zlength buf <= lo \/ bv_unsigned sp <= B) /\ (B + zlength buf <= Fp + 32 \/ Fp + 64 <= B))) ->
      implM usegs (stdio_write (St:=St) fd buf s) st
            (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
                              (zlength s) lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16644) fc None m (seg_rom usegs)).
  Proof.
    intros until canary. intros FC BUFB SRC -> -> -> FD ST LO GLO SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BUFLE BShi S0 Shi SP47 B47 S47 SEPS SEPB.
    eapply stdio_write_body; eassumption.
  Qed.
End StdioWrite.
