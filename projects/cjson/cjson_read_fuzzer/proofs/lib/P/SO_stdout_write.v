(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_syscalls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module SO_stdio_write.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_model.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.


Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

Definition STDIO_WRITE : Z := 0x17a70.
Definition STDIO_WRITE_DEPTH : Z := 112.

(* [comment removed for export] *)
Definition boxed (P : Prop) : Prop := P.

(* [comment removed for export] *)
Definition iovs_of (buf s : list Z) : list (list byte) :=
  match buf with [] => [to_bytes s] | _ => [to_bytes buf; to_bytes s] end.

(* [comment removed for export] *)
Ltac src_now SRC SEPS MU LSB :=
  unfold boxed in SRC;
  lazymatch goal with
  | |- bytes_at _ ?m' ?S (to_bytes ?s) =>
      destruct SEPS as [-> | [SEP1 SEP2]];
      [ apply bytes_at_nil; lia
      | apply (bytes_at_transport _ _ _ m' _ _ SRC MU); cbn [disjoint_from]; rewrite LSB; unfold zlength in SEP1, SEP2; lia ]
  end.

Section StdioWrite.
  Context {St : Type}.

  Definition stdio_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (Fp : Z) (flags : word) (B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
      (l : Z) (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom psegs)
      /\ munch [(bv_unsigned sp - STDIO_WRITE_DEPTH, bv_unsigned sp); (Fp + 32, Fp + 64)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ stk psegs m' lo (bv_unsigned sp)
      /\ rw_cells psegs m' Fp (file_cells flags (B + bufsize) B B wfn B bufsize fd mode lbf tail)
      /\ ssp_cells m' canary
      /\ st' = st.

  (* [comment removed for export] *)
  Lemma implM_wv_step : forall (fd : Z) (iov : list (list Z)) (fuel : nat) (st : St)
      (Q : unit -> St -> machine_state -> Prop) ms,
    evt psegs (fun ms1 => at_node psegs (NWritev fd (map to_bytes iov)) ms1 /\
       forall rsp k, dec_wv (wv_total iov) rsp = Some k ->
          (k = wv_total iov -> evt psegs (Q tt st) (nret ms1 rsp)) /\
          (k <> wv_total iov -> implM psegs (mloop fuel (wv_body fd) (wv_advance iov k)) st Q (nret ms1 rsp))) ms ->
    implM psegs (mloop (S fuel) (wv_body (St:=St) fd) iov) st Q ms.
  Proof using .
    intros fd iov fuel st Q ms H. apply implM_loop_S. unfold wv_body.
    eapply implM_bind with (Q1 := fun k s' ms' => s' = st /\
        (k = wv_total iov -> evt psegs (Q tt st) ms') /\
        (k <> wv_total iov -> implM psegs (mloop fuel (wv_body fd) (wv_advance iov k)) st Q ms')).
    - apply implM_sys. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp k Hd. apply evt_done. split; [reflexivity|]. exact (Hk rsp k Hd).
    - intros k s' ms' nelH_; (nelim nelH_ 3%nat; intros -> HD HL). cbv beta. destruct (Z.eqb_spec k (wv_total iov)) as [E|NE].
      + apply implM_ret. cbn. eapply evt_mono; [apply HD; exact E|]. intros ms'' H''. apply evt_done. exact H''.
      + apply implM_ret. cbn. apply evt_done. apply HL. exact NE.
  Qed.

  Section Call.
    (* [comment removed for export] *)
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (st : St)
              (Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
              (buf s : list Z) (S lo : Z) (canary : word).
    Hypothesis FD : fd = 1 \/ fd = 2.
    Hypothesis LO : lo <= bv_unsigned sp - 112.
    Hypothesis GLO : 0x55000 <= lo.
    Hypothesis Fp0 : 0 <= Fp.
    Hypothesis FPLO : Fp + 232 <= lo.
    Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
    Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
    Hypothesis B0 : 0 <= B.
    Hypothesis BS0 : 0 <= bufsize.
    Hypothesis BUFLE : zlength buf <= bufsize.
    Hypothesis BShi : B + bufsize < 2^64.
    Hypothesis LENS : zlength buf + zlength s < 2^62.
    Hypothesis S0 : 0 <= S < 2^64.
    Hypothesis Shi : S + zlength s <= 2^64.
    Hypothesis SEPS : s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S)).
    Hypothesis SEPB : B + zlength buf <= lo \/ bv_unsigned sp <= B.
    Hypothesis SPHI : 0 <= bv_unsigned sp < 2^64.
    (* [comment removed for export] *)
    Hypothesis TSP : bv_unsigned sp <= TASK_SIZE.
    Hypothesis TB : zlength buf = 0 \/ B + zlength buf <= TASK_SIZE.
    Hypothesis TS : S + zlength s <= TASK_SIZE.
    Local Ltac task_sp := rewrite ?unsigned_lit by lia; cbn [map length Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    Local Ltac task_iovs :=
      repeat (apply Forall_cons; [cbn [fst snd]; rewrite ?unsigned_lit by (unfold zlength in *; lia); unfold zlength in *; lia|]); apply Forall_nil.

    Notation SPF := (bv_unsigned sp + -112).
    Notation POST := (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
                        (zlength s) lo canary m0 st).
    Notation W := [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)].
    Notation WF := [(bv_unsigned sp - 112, bv_unsigned sp)].
    (* [comment removed for export] *)
    Notation FRAME mm jk b0w l0w b1w l1w :=
      (rw_cells psegs mm (bv_unsigned sp + -112)
         [CB 8 jk; C8 b0w; C8 l0w; C8 b1w; C8 l1w; C8 canary; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    Notation FILE mm := (rw_cells psegs mm Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail)).
    (* [comment removed for export] *)
    Notation LST pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31 :=
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 ssp_guard) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

    (* [comment removed for export] *)
    Definition minv (mm : mem) : Prop :=
      munch WF m0 mm /\ wmono psegs m0 mm /\ mem_inv psegs mm /\ stk psegs mm lo SPF /\ FILE mm /\ ssp_cells mm canary.

    Hypothesis SRC0 : bytes_at psegs m0 S (to_bytes s).
    Hypothesis BUF0 : bytes_at psegs m0 B (to_bytes buf).

    Lemma to_bytes_length : forall l, length (to_bytes l) = length l.
    Proof using . intros. unfold to_bytes. apply length_map. Qed.

    Lemma src_cur : forall mm, munch WF m0 mm -> bytes_at psegs mm S (to_bytes s).
    Proof using FPLO LO S0 SEPS SRC0 buf.
      intros mm MU. destruct SEPS as [E | [SEP1 SEP2]].
      - rewrite E. apply bytes_at_nil. lia.
      - apply (bytes_at_transport _ _ _ mm _ _ SRC0 MU). cbn [disjoint_from]. rewrite to_bytes_length. unfold zlength in *. lia.
    Qed.

    Lemma buf_cur : forall mm, munch WF m0 mm -> bytes_at psegs mm B (to_bytes buf).
    Proof using BUF0 LO SEPB s.
      intros mm MU. apply (bytes_at_transport _ _ _ mm _ _ BUF0 MU). cbn [disjoint_from]. rewrite to_bytes_length.
      unfold zlength in *. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma bytes_at_drop : forall mm A (l : list Z) j, bytes_at psegs mm A (to_bytes l) -> 0 <= j <= zlength l ->
      bytes_at psegs mm (A + j) (to_bytes (skipn (Z.to_nat j) l)).
    Proof using .
      intros mm A l j BY Hj. unfold zlength in Hj.
      rewrite <- (firstn_skipn (Z.to_nat j) l) in BY. unfold to_bytes in BY |- *. rewrite map_app in BY.
      apply bytes_at_app in BY. destruct BY as [_ BY]. rewrite length_map, length_firstn in BY.
      replace (A + Z.of_nat (Init.Nat.min (Z.to_nat j) (length l))) with (A + j) in BY by lia. exact BY.
    Qed.

    (* [comment removed for export] *)
    Lemma frame_iovs : forall mm jk b0w l0w b1w l1w, FRAME mm jk b0w l0w b1w l1w ->
      bytes_at psegs mm (bv_unsigned sp + -112 + 8) (iovec_bytes [(b0w, l0w); (b1w, l1w)])
      /\ bytes_at psegs mm (bv_unsigned sp + -112 + 24) (iovec_bytes [(b1w, l1w)]).
    Proof using .
      intros mm jk b0w l0w b1w l1w FR.
      change (rw_cells psegs mm (bv_unsigned sp + -112) ([CB 8 jk] ++ [C8 b0w; C8 l0w] ++ [C8 b1w; C8 l1w] ++
                [C8 canary; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) in FR.
      apply F_fwritex.rw_cells_app in FR. destruct FR as [[[W0 _] _] FR]. cbn [cells_wf cell_wf] in W0. destruct W0 as [L8 _].
      cbn [cells_size csize Nat.add] in FR.
      apply F_fwritex.rw_cells_app in FR. destruct FR as [[[_ B1] _] FR]. cbn [cells_size csize Nat.add] in FR.
      apply F_fwritex.rw_cells_app in FR. destruct FR as [[[_ B2] _] _].
      cbn [cells_bytes cbytes] in B1, B2. rewrite app_nil_r in B1, B2.
      cbn [iovec_bytes flat_map fst snd]. rewrite !app_nil_r. split.
      - apply bytes_at_app. split; [exact B1|]. rewrite length_app, !length_le8.
        replace (bv_unsigned sp + -112 + 8 + Z.of_nat (8 + 8)) with (bv_unsigned sp + -112 + Z.of_nat 8 + Z.of_nat 16) by lia.
        exact B2.
      - replace (bv_unsigned sp + -112 + 24) with (bv_unsigned sp + -112 + Z.of_nat 8 + Z.of_nat 16) by lia. exact B2.
    Qed.

    Lemma sub_WF_W : sub_fp WF W.
    Proof using . intros x Hx. cbn in Hx |- *. destruct Hx as [H1 _]. split; [exact H1| exact I]. Qed.

    (* [comment removed for export] *)
    Lemma sw_done : forall mm jk b0w l0w b1w l1w x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31,
      minv mm -> FRAME mm jk b0w l0w b1w l1w ->
      evt psegs (POST tt st) (LST 0x17b04 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31).
    Proof using FPLO FSEP1 FSEP2 Fp0 GLO LO.
      intros until x31. intros (MU0 & WM & MI & ST & FC & [GOT GUARD]) FR.
      pose proof (munch_weaken _ _ _ _ sub_WF_W MU0) as MU. clear MU0.
      unfold got_ssp, ssp_guard in *. unfold file_cells in FC.
      do 7 step.
      step. step. step. if_false.
      do 10 step.
      release_frame FR ST (bv_unsigned sp).
      unfold stdio_write_post, file_cells. sys_finish.
      + split; [exact GOT| exact GUARD].
      + reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma sw_loop1 : forall (n : nat) (j j' : Z) (fuel : nat) mm jk b0w l0w (kw rw bw lw : Z) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31,
      (Z.to_nat (zlength s - j') < n)%nat ->
      0 <= j -> j < j' < zlength s -> (Z.to_nat (zlength s - j') < fuel)%nat ->
      kw = j' - j -> rw = zlength s - j -> bw = S + j -> lw = zlength s - j ->
      minv mm -> FRAME mm jk b0w l0w (Z_to_bv 64 bw) (Z_to_bv 64 lw) ->
      implM psegs (mloop fuel (wv_body (St:=St) fd) [skipn (Z.to_nat j') s]) st POST
            (LST 0x17b90 mm x1 x5 x6 x7 (Z_to_bv 64 kw) x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -112 + 24)) x20 (Z_to_bv 64 rw) x28 x29 x30 x31).
    Proof using FD FPLO FSEP1 FSEP2 Fp0 GLO LENS LO S0 SEPS SPHI SRC0 Shi TS TSP.
      induction n as [|n IH]; [lia|].
      intros until x31. intros Hn Hj Hjj Hfuel -> -> -> -> MINV FR. (nelimp MINV 6%nat; intros MU WM MI ST FC [GOT GUARD]).
      unfold got_ssp, ssp_guard in *. unfold file_cells in FC. unfold zlength in *.
      destruct fuel as [|fuel]; [lia|].
      apply implM_wv_step.
      step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
      zstep. zstep.
      replace (Z.of_nat (length s) - j <? j' - j) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
      zstep. zstep. zstep. zstep. zstep. rewrite Z.land_0_l. zstep. rewrite Z.sub_0_r. zstep.
      (* [comment removed for export] *)
      step.
      step. if_cases K; zify_cond K; [| exfalso; lia]. clear K.
      step. step. zstep. zstep. zstep. step.
      replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply Shgetc_lemmas.sx32_small; lia).
      zstep. zstep.
      (* [comment removed for export] *)
      step.
      step. step. step_ecall.
      lazymatch goal with |- _ /\ _ => idtac end.
      lazymatch goal with H : rw_cells psegs ?mx (bv_unsigned sp + -112) _ |- _ => rename H into FR1; rename mx into m1 end.
      assert (MU1 : munch WF m0 m1) by assumption.
      replace (S + j + (j' - j)) with (S + j') in FR1 by lia.
      replace (Z.of_nat (length s) - j - (j' - j)) with (Z.of_nat (length s) - j') in * by lia.
      pose proof (frame_iovs _ _ _ _ _ _ FR1) as [_ IOV].
      pose proof (bytes_at_drop m1 S s j' (src_cur m1 MU1) ltac:(unfold zlength; lia)) as SRCj.
      assert (LSK : Z.of_nat (length (skipn (Z.to_nat j') s)) = Z.of_nat (length s) - j') by (rewrite length_skipn; lia).
      split.
      { at_node_red; split_spine; try reflexivity; try lia.
        - cbn [map length]. lia.
        - cbn [map concat]. rewrite app_nil_r, to_bytes_length. lia.
        - exists [(Z_to_bv 64 (S + j'), Z_to_bv 64 (Z.of_nat (length s) - j'))]. split; [task_sp|]. split; [task_iovs|]. split.
          + rewrite unsigned_lit by lia. replace (bv_unsigned sp + -88) with (bv_unsigned sp + -112 + 24) by lia. exact IOV.
          + cbn [map]. constructor; [|constructor]. split; [cbn [snd]; rewrite to_bytes_length, LSK; reflexivity|].
            cbn [fst]. rewrite unsigned_lit by lia. exact SRCj. }
      intros rsp k2 Hdec. apply dec_wv_Some in Hdec as (-> & Hk2 & Rk2).
      unfold wv_total, zlength in Hk2 |- *. cbn [concat] in Hk2 |- *. rewrite app_nil_r, LSK in Hk2 |- *.
      assert (K2 : 1 <= k2 <= Z.of_nat (length s) - j') by lia. clear Hk2.
      assert (MINV1 : minv m1). { split; [exact MU1|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FC| split; assumption]. }
      split.
      + (* [comment removed for export] *)
        intros E. unfold eff0. sys_nret.
        step. step. step. step. if_cases Hc; zify_cond Hc; [| exfalso; lia]. step.
        replace (ret_pc (Z_to_bv 64 0x17b88)) with (Z_to_bv 64 0x17b88 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        step. step. if_cases Hd; zify_cond Hd; [| exfalso; lia].
        eapply sw_done; [exact MINV1| exact FR1].
      + (* [comment removed for export] *)
        intros NE. cbn [wv_advance]. rewrite skipn_skipn.
        replace (Z.to_nat k2 + Z.to_nat j')%nat with (Z.to_nat (j' + k2)) by lia.
        unfold implM. iprefix. unfold eff0. sys_nret.
        step. step. step. step. if_cases Hc; zify_cond Hc; [| exfalso; lia]. step.
        replace (ret_pc (Z_to_bv 64 0x17b88)) with (Z_to_bv 64 0x17b88 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        step. step. if_cases Hd; zify_cond Hd; [exfalso; lia|].
        apply evt_done. cbv beta.
        replace (Z_to_bv 64 (bv_unsigned sp + -88)) with (Z_to_bv 64 (bv_unsigned sp + -112 + 24) : word) by (f_equal; lia).
        eapply (IH j' (j' + k2) fuel m1 jk b0w l0w); [ | | | | | | | | exact MINV1| exact FR1]; lia.
    Qed.

    Lemma land_ones64_l : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
    Proof using . intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

    (* [comment removed for export] *)
    Lemma sw_loop2 : forall (n : nat) (j k : Z) (fuel : nat) mm jk (rw bw lw : Z) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31,
      (Z.to_nat (zlength buf - j + zlength s - k) < n)%nat ->
      0 <= j <= zlength buf -> 1 <= k -> k < zlength buf - j + zlength s ->
      (Z.to_nat (zlength buf - j + zlength s - k) < fuel)%nat ->
      rw = zlength buf - j + zlength s -> bw = B + j -> lw = zlength buf - j ->
      minv mm -> FRAME mm jk (Z_to_bv 64 bw) (Z_to_bv 64 lw) (Z_to_bv 64 S) (Z_to_bv 64 (zlength s)) ->
      implM psegs (mloop fuel (wv_body (St:=St) fd) (wv_advance [skipn (Z.to_nat j) buf; s] k)) st POST
            (LST 0x17b90 mm x1 x5 x6 x7 (Z_to_bv 64 k) x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 2) (Z_to_bv 64 (bv_unsigned sp + -112 + 8)) x20 (Z_to_bv 64 rw) x28 x29 x30 x31).
    Proof using BS0 BShi BUF0 BUFLE FD FPLO FSEP1 FSEP2 Fp0 GLO LENS LO S0 SEPB SEPS SPHI SRC0 Shi TB TS TSP.
      induction n as [|n IH]; [lia|].
      intros until x31. intros Hn Hj HkA HkB Hfuel -> -> -> MINV FR. (nelimp MINV 6%nat; intros MU WM MI ST FC [GOT GUARD]).
      unfold got_ssp, ssp_guard in *. unfold file_cells in FC. unfold zlength in *.
      pose proof (bytes_at_bound _ _ _ _ BUF0) as BB. rewrite to_bytes_length in BB.
      destruct fuel as [|fuel]; [lia|].
      cbn [wv_advance]. unfold zlength. rewrite length_skipn.
      replace (Z.of_nat (length buf - Z.to_nat j)) with (Z.of_nat (length buf) - j) by lia.
      apply implM_wv_step.
      step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
      zstep. zstep.
      destruct (Z.ltb_spec (Z.of_nat (length buf) - j) k) as [ADV|NADV]; cbn [Z.b2z].
      - (* [comment removed for export] *)
        set (j1 := k - (Z.of_nat (length buf) - j)) in *.
        zstep. zstep. zstep. zstep. zstep. rewrite (land_ones64_l (Z.of_nat (length buf) - j)) by lia.
        zstep. zstep.
        replace (k - (Z.of_nat (length buf) - j)) with j1 by lia.
        step.
        step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
        step. step.
        step. zstep. zstep. zstep. step.
        replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply Shgetc_lemmas.sx32_small; lia).
        zstep. zstep.
        replace (Z.of_nat (length s) - (Z.of_nat (length buf) - j + Z.of_nat (length s) - k)) with j1 by lia.
        step.
        step. step. step_ecall.
        lazymatch goal with H : rw_cells psegs ?mx (bv_unsigned sp + -112) _ |- _ => rename H into FR1; rename mx into m1 end.
        assert (MU1 : munch WF m0 m1) by assumption.
        pose proof (frame_iovs _ _ _ _ _ _ FR1) as [_ IOV].
        pose proof (bytes_at_drop m1 S s j1 (src_cur m1 MU1) ltac:(unfold zlength; lia)) as SRCj.
        assert (LSK : Z.of_nat (length (skipn (Z.to_nat j1) s)) = Z.of_nat (length s) - j1) by (rewrite length_skipn; lia).
        assert (MINV1 : minv m1). { split; [exact MU1|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FC| split; assumption]. }
        split.
        { at_node_red; split_spine; try reflexivity; try lia.
          - cbn [map length]. lia.
          - cbn [map concat]. rewrite app_nil_r, to_bytes_length. lia.
          - exists [(Z_to_bv 64 (S + j1), Z_to_bv 64 (Z.of_nat (length s) - j1))]. split; [task_sp|]. split; [task_iovs|]. split.
            + rewrite unsigned_lit by lia. replace (bv_unsigned sp + -88) with (bv_unsigned sp + -112 + 24) by lia. exact IOV.
            + cbn [map]. constructor; [|constructor]. split; [cbn [snd]; rewrite to_bytes_length, LSK; reflexivity|].
              cbn [fst]. rewrite unsigned_lit by lia. exact SRCj. }
        intros rsp k2 Hdec. apply dec_wv_Some in Hdec as (-> & Hk2 & Rk2).
        unfold wv_total, zlength in Hk2 |- *. cbn [concat] in Hk2 |- *. rewrite app_nil_r, LSK in Hk2 |- *.
        assert (K2 : 1 <= k2 <= Z.of_nat (length s) - j1) by lia. clear Hk2.
        split.
        + intros E. unfold eff0. sys_nret.
          step. step. step. step. if_cases Hc; zify_cond Hc; [| exfalso; lia]. step.
          replace (ret_pc (Z_to_bv 64 0x17b88)) with (Z_to_bv 64 0x17b88 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          step. step. if_cases Hd; zify_cond Hd; [| exfalso; lia].
          eapply sw_done; [exact MINV1| exact FR1].
        + intros NE. cbn [wv_advance]. rewrite skipn_skipn.
          replace (Z.to_nat k2 + Z.to_nat j1)%nat with (Z.to_nat (j1 + k2)) by lia.
          unfold implM. iprefix. unfold eff0. sys_nret.
          step. step. step. step. if_cases Hc; zify_cond Hc; [| exfalso; lia]. step.
          replace (ret_pc (Z_to_bv 64 0x17b88)) with (Z_to_bv 64 0x17b88 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          step. step. if_cases Hd; zify_cond Hd; [exfalso; lia|].
          apply evt_done. cbv beta.
          replace (Z_to_bv 64 (bv_unsigned sp + -88)) with (Z_to_bv 64 (bv_unsigned sp + -112 + 24) : word) by (f_equal; lia).
          eapply (sw_loop1 (Datatypes.S (Z.to_nat (Z.of_nat (length s) - (j1 + k2)))) j1 (j1 + k2) fuel m1); [ | | | | | | | | exact MINV1| exact FR1]; unfold zlength; lia.
      - (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. rewrite Z.land_0_l. zstep. rewrite Z.sub_0_r. zstep.
        step.
        step. if_cases K; zify_cond K; [| exfalso; lia]. clear K.
        step. step. zstep. zstep. zstep. step.
        replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply Shgetc_lemmas.sx32_small; lia).
        zstep. zstep.
        step.
        step. step. step_ecall.
        lazymatch goal with H : rw_cells psegs ?mx (bv_unsigned sp + -112) _ |- _ => rename H into FR1; rename mx into m1 end.
        assert (MU1 : munch WF m0 m1) by assumption.
        replace (B + j + k) with (B + (j + k)) in FR1 by lia.
        replace (Z.of_nat (length buf) - j - k) with (Z.of_nat (length buf) - (j + k)) in * by lia.
        pose proof (frame_iovs _ _ _ _ _ _ FR1) as [IOV _].
        pose proof (bytes_at_drop m1 B buf (j + k) (buf_cur m1 MU1) ltac:(unfold zlength; lia)) as BUFj.
        pose proof (src_cur m1 MU1) as SRC1.
        assert (LSK : Z.of_nat (length (skipn (Z.to_nat (j + k)) buf)) = Z.of_nat (length buf) - (j + k)) by (rewrite length_skipn; lia).
        assert (MINV1 : minv m1). { split; [exact MU1|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FC| split; assumption]. }
        rewrite skipn_skipn. replace (Z.to_nat k + Z.to_nat j)%nat with (Z.to_nat (j + k)) by lia.
        split.
        { at_node_red; split_spine; try reflexivity; try lia.
          - cbn [map length]. lia.
          - cbn [map concat]. rewrite app_nil_r, length_app, !to_bytes_length. lia.
          - exists [(Z_to_bv 64 (B + (j + k)), Z_to_bv 64 (Z.of_nat (length buf) - (j + k))); (Z_to_bv 64 S, Z_to_bv 64 (Z.of_nat (length s)))]. split; [task_sp|]. split; [task_iovs|]. split.
            + rewrite unsigned_lit by lia. replace (bv_unsigned sp + -104) with (bv_unsigned sp + -112 + 8) by lia. exact IOV.
            + cbn [map]. constructor; [| constructor; [| constructor]].
              * split; [cbn [snd]; rewrite to_bytes_length, LSK; reflexivity|]. cbn [fst]. rewrite unsigned_lit by lia. exact BUFj.
              * split; [cbn [snd]; rewrite to_bytes_length; reflexivity|]. cbn [fst]. rewrite unsigned_lit by lia. exact SRC1. }
        intros rsp k2 Hdec. apply dec_wv_Some in Hdec as (-> & Hk2 & Rk2).
        unfold wv_total, zlength in Hk2 |- *. cbn [concat] in Hk2 |- *. rewrite app_nil_r, length_app, length_skipn in Hk2 |- *.
        assert (K2 : 1 <= k2 <= Z.of_nat (length buf) - (j + k) + Z.of_nat (length s)) by lia. clear Hk2.
        split.
        + intros E. unfold eff0. sys_nret.
          step. step. step. step. if_cases Hc; zify_cond Hc; [| exfalso; lia]. step.
          replace (ret_pc (Z_to_bv 64 0x17b88)) with (Z_to_bv 64 0x17b88 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          step. step. if_cases Hd; zify_cond Hd; [| exfalso; lia].
          eapply sw_done; [exact MINV1| exact FR1].
        + intros NE.
          unfold implM. iprefix. unfold eff0. sys_nret.
          step. step. step. step. if_cases Hc; zify_cond Hc; [| exfalso; lia]. step.
          replace (ret_pc (Z_to_bv 64 0x17b88)) with (Z_to_bv 64 0x17b88 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          step. step. if_cases Hd; zify_cond Hd; [exfalso; lia|].
          apply evt_done. cbv beta.
          replace (Z_to_bv 64 (bv_unsigned sp + -104)) with (Z_to_bv 64 (bv_unsigned sp + -112 + 8) : word) by (f_equal; lia).
          eapply (IH (j + k) k2 fuel m1 jk); [ | | | | | | | | exact MINV1| exact FR1]; unfold zlength; lia.
    Qed.

    (* [comment removed for export] *)
    Lemma sw_entry : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      FILE m0 -> stk psegs m0 lo (bv_unsigned sp) -> ssp_cells m0 canary -> mem_inv psegs m0 ->
      implM psegs (stdio_writev (St:=St) fd buf s) st POST
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 (zlength s)) a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x17a70) fc None m0 (seg_rom psegs)).
    Proof using B0 BS0 BShi BUF0 BUFLE FD FPLO FSEP1 FSEP2 Fp0 GLO LENS LO S0 SEPB SEPS SPHI SRC0 Shi TB TS TSP.
      intros until t6. intros FC ST [GOT GUARD] MI.
      pose proof (bytes_at_bound _ _ _ _ BUF0) as BB. rewrite to_bytes_length in BB.
      change (boxed (bytes_at psegs m0 S (to_bytes s))) in SRC0. change (boxed (bytes_at psegs m0 B (to_bytes buf))) in BUF0.
      unfold got_ssp, ssp_guard in *. unfold file_cells in FC. unfold zlength in *.
      pose proof (munch_refl WF m0) as MU. pose proof (wmono_refl psegs m0) as WM.
      unfold stdio_writev. apply implM_wv_step.
      carve_frame 112%nat ST.
      do 12 step. do 13 step.
      rewrite !unsigned_lit by lia.
      destruct (Z.eq_dec (Z.of_nat (length buf)) 0) as [E0|NE0].
      - (* [comment removed for export] *)
        assert (Ebuf : buf = []) by (destruct buf; [reflexivity| cbn [length] in E0; lia]).
        replace (B + Z.of_nat (length buf)) with B by lia. rewrite Z.lxor_nilpotent.
        change (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0)) with (Z_to_bv 64 0).
        step. if_true. do 6 step. step_ecall.
        replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply Shgetc_lemmas.sx32_small; lia).
        replace (B - B + Z.of_nat (length s)) with (Z.of_nat (length s)) by lia.
        replace (wv_init buf s) with [s] by (rewrite Ebuf; reflexivity).
        lazymatch goal with H : rw_cells psegs ?mx (bv_unsigned sp + -112) _ |- _ => rename H into FR1; rename mx into m1 end.
        assert (MU1 : munch WF m0 m1) by assumption.
        replace (B - B) with (Z.of_nat (length s) - Z.of_nat (length s)) in FR1 by lia.
        pose proof (frame_iovs _ _ _ _ _ _ FR1) as [_ IOV].
        pose proof (src_cur m1 MU1) as SRC1.
        assert (MINV1 : minv m1). { split; [exact MU1|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FC| split; assumption]. }
        split.
        { at_node_red; split_spine; try reflexivity; try lia.
          - cbn [map length]. lia.
          - cbn [map concat]. rewrite app_nil_r, to_bytes_length. lia.
          - exists [(Z_to_bv 64 S, Z_to_bv 64 (Z.of_nat (length s)))]. split; [task_sp|]. split; [task_iovs|]. split.
            + rewrite unsigned_lit by lia. replace (bv_unsigned sp + -88) with (bv_unsigned sp + -112 + 24) by lia.
              replace (Z.of_nat (length s)) with (Z.of_nat (length s) - (Z.of_nat (length s) - Z.of_nat (length s))) at 2 by lia. exact IOV.
            + cbn [map]. constructor; [|constructor]. split; [cbn [snd]; rewrite to_bytes_length; reflexivity|].
              cbn [fst]. rewrite unsigned_lit by lia. exact SRC1. }
        intros rsp k2 Hdec. apply dec_wv_Some in Hdec as (-> & Hk2 & Rk2).
        unfold wv_total, zlength in Hk2 |- *. cbn [concat] in Hk2 |- *. rewrite app_nil_r in Hk2 |- *.
        split.
        + intros E. unfold eff0. sys_nret.
          step. step. step. step. if_cases Hc; zify_cond Hc; [| exfalso; lia]. step.
          replace (ret_pc (Z_to_bv 64 0x17b00)) with (Z_to_bv 64 0x17b00 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          step. if_cases Hd; zify_cond Hd; [exfalso; lia|].
          eapply sw_done; [exact MINV1| exact FR1].
        + intros NE. assert (K2 : 1 <= k2 < Z.of_nat (length s)) by lia. clear Hk2.
          replace (wv_advance [s] k2) with [skipn (Z.to_nat k2) s] by reflexivity.
          unfold implM. iprefix. unfold eff0. sys_nret.
          step. step. step. step. if_cases Hc; zify_cond Hc; [| exfalso; lia]. step.
          replace (ret_pc (Z_to_bv 64 0x17b00)) with (Z_to_bv 64 0x17b00 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          step. if_cases Hd; zify_cond Hd; [| exfalso; lia].
          apply evt_done. cbv beta.
          replace (Z_to_bv 64 (bv_unsigned sp + -88)) with (Z_to_bv 64 (bv_unsigned sp + -112 + 24) : word) by (f_equal; lia).
          eapply (sw_loop1 (Datatypes.S (Z.to_nat (Z.of_nat (length s) - k2))) 0 k2 _ m1); [ | | | | | | | | exact MINV1| exact FR1]; unfold zlength; lia.
      - (* [comment removed for export] *)
        set (nb := Z.of_nat (length buf)) in *.
        assert (NB1 : 1 <= nb) by lia.
        replace (Z.lxor (B + nb) B) with (Z.lxor (B + nb) (B + 0)) by (rewrite Z.add_0_r; reflexivity).
        assert (XNZ : Z.lxor (B + nb) (B + 0) <> 0). { intros E. apply Z.lxor_eq in E. lia. }
        replace (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.lxor (B + nb) (B + 0)))) with (Z_to_bv 64 1).
        2:{ pose proof (Z_lxor_range (B + nb) (B + 0) ltac:(lia) ltac:(lia)) as XR.
            unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
            destruct (Z.ltb_spec0 0 (Z.lxor (B + nb) (B + 0))); [reflexivity| exfalso; lia]. }
        step. if_cases Hb; zify_cond Hb. 1:{ exfalso. lia. } do 7 step. step_ecall.
        replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply Shgetc_lemmas.sx32_small; lia).
        replace (B + nb - B + Z.of_nat (length s)) with (nb + Z.of_nat (length s)) by lia.
        replace (B + nb - B) with nb by lia.
        replace (wv_init buf s) with [buf; s] by (destruct buf; [exfalso; subst nb; cbn [length] in NE0; lia| reflexivity]).
        lazymatch goal with H : rw_cells psegs ?mx (bv_unsigned sp + -112) _ |- _ => rename H into FR1; rename mx into m1 end.
        rewrite !unsigned_lit in FR1 by lia. replace (B + nb - B) with nb in FR1 by lia.
        assert (MU1 : munch WF m0 m1) by assumption.
        pose proof (frame_iovs _ _ _ _ _ _ FR1) as [IOV _].
        pose proof (src_cur m1 MU1) as SRC1. pose proof (buf_cur m1 MU1) as BUF1.
        assert (MINV1 : minv m1). { split; [exact MU1|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FC| split; assumption]. }
        split.
        { at_node_red; split_spine; try reflexivity; try lia.
          - cbn [map length]. lia.
          - cbn [map concat]. rewrite app_nil_r, length_app, !to_bytes_length. lia.
          - exists [(Z_to_bv 64 B, Z_to_bv 64 nb); (Z_to_bv 64 S, Z_to_bv 64 (Z.of_nat (length s)))]. split; [task_sp|]. split; [task_iovs|]. split.
            + rewrite unsigned_lit by lia. replace (bv_unsigned sp + -104) with (bv_unsigned sp + -112 + 8) by lia. exact IOV.
            + cbn [map]. constructor; [| constructor; [| constructor]].
              * split; [cbn [snd]; rewrite to_bytes_length; subst nb; reflexivity|]. cbn [fst]. rewrite unsigned_lit by lia. exact BUF1.
              * split; [cbn [snd]; rewrite to_bytes_length; reflexivity|]. cbn [fst]. rewrite unsigned_lit by lia. exact SRC1. }
        intros rsp k2 Hdec. apply dec_wv_Some in Hdec as (-> & Hk2 & Rk2).
        unfold wv_total, zlength in Hk2 |- *. cbn [concat] in Hk2 |- *. rewrite app_nil_r, length_app in Hk2 |- *. fold nb in Hk2 |- *.
        split.
        + intros E. unfold eff0. sys_nret.
          step. step. step. step. if_cases Hc; zify_cond Hc; [| exfalso; lia]. step.
          replace (ret_pc (Z_to_bv 64 0x17b00)) with (Z_to_bv 64 0x17b00 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          step. if_cases Hd; zify_cond Hd; [exfalso; lia|].
          eapply sw_done; [exact MINV1| exact FR1].
        + intros NE. assert (K2 : 1 <= k2 < nb + Z.of_nat (length s)) by lia. clear Hk2.
          unfold implM. iprefix. unfold eff0. sys_nret.
          step. step. step. step. if_cases Hc; zify_cond Hc; [| exfalso; lia]. step.
          replace (ret_pc (Z_to_bv 64 0x17b00)) with (Z_to_bv 64 0x17b00 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          step. if_cases Hd; zify_cond Hd; [| exfalso; lia].
          apply evt_done. cbv beta.
          replace (Z_to_bv 64 (bv_unsigned sp + -104)) with (Z_to_bv 64 (bv_unsigned sp + -112 + 8) : word) by (f_equal; lia).
          change (wv_advance [buf; s] k2) with (wv_advance [skipn (Z.to_nat 0) buf; s] k2).
          eapply (sw_loop2 (Datatypes.S (Z.to_nat (nb + Z.of_nat (length s) - k2))) 0 k2 _ m1); [ | | | | | | | | exact MINV1| exact FR1]; unfold zlength; lia.
    Qed.
  End Call.

  Lemma stdio_write_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
           (buf s : list Z) (S lo : Z) (canary : word),
      rw_cells psegs m Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
      bytes_at psegs m B (to_bytes buf) ->
      bytes_at psegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      (fd = 1 \/ fd = 2) ->
      stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDIO_WRITE_DEPTH) -> (0x55000 <= lo) ->
      ssp_cells m canary -> mem_inv psegs m ->
      (0 <= Fp) -> (Fp + 232 <= lo) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (0 <= B) -> (0 <= bufsize) -> (zlength buf <= bufsize) -> (B + bufsize < 2^64) ->
      (zlength buf + zlength s < 2^62) -> (0 <= S < 2^64) -> (S + zlength s <= 2^64) ->
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S))) ->
      (B + zlength buf <= lo \/ bv_unsigned sp <= B) ->
      (s = [] -> S <= TASK_SIZE) ->   (* [comment removed for export] *)
      implM psegs (stdio_writev (St:=St) fd buf s) st
            (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
                              (zlength s) lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x17a70) fc None m (seg_rom psegs)).
  Proof.
    intros until canary. intros FC BUFB SRC -> -> -> FD ST LO GLO SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BUFLE BShi LENS S0 Shi SEPS SEPB SNIL.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold STDIO_WRITE_DEPTH in LO.
    (* [comment removed for export] *)
    assert (TSP : bv_unsigned sp <= TASK_SIZE).
    { (nelimp ST 3%nat; intros _ _ STk). (nelim (STk (bv_unsigned sp - 1) ltac:(lia)) 3%nat; intros _ b Hb).
      pose proof (mem_inv_mrd_task psegs m _ b MI psegs_task Hb) as T. rewrite wa_unsigned in T by lia. lia. }
    assert (TB : zlength buf = 0 \/ B + zlength buf <= TASK_SIZE).
    { destruct buf as [|c buf']; [left; reflexivity| right].
      pose proof (bytes_at_task psegs m B _ MI psegs_task BUFB ltac:(discriminate)) as T. rewrite to_bytes_length in T. unfold zlength. exact T. }
    assert (TS : S + zlength s <= TASK_SIZE).
    { destruct s as [|c s'].
      - unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r. apply SNIL. reflexivity.
      - pose proof (bytes_at_task psegs m S _ MI psegs_task SRC ltac:(discriminate)) as T. rewrite to_bytes_length in T. unfold zlength. exact T. }
    eapply sw_entry; try eassumption; lia.
  Qed.
End StdioWrite.
End SO_stdio_write.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac ITree Nodes Decode SysStep MonadX.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_syscalls F_pad F_fmt_fp_lib Exit.
Import SO_stdio_write.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SO_model.   (* [comment removed for export] *)

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From Stdlib Require Import Zify Lia.
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require JunkAbs.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.JunkAbs.split_for_access_raw H segs m A cs kn n.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition wfn_of (so : stdout_st) : Z := if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE.
Definition lbf_of (so : stdout_st) : Z := if so_lbf_nl so then 10 else 0xffffffff.
Definition stdout_cells (so : stdout_st) (flags mode : word) (tail : list byte) : list cell :=
  file_cells flags (RSTDOUT_BUF + 1024) (RSTDOUT_BUF + zlength (so_buf so)) RSTDOUT_BUF (wfn_of so) RSTDOUT_BUF 1024 1 mode (lbf_of so) tail.

Definition STDOUT_WRITE_DEPTH : Z := 144.   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac exact_frm := lazymatch goal with |- frm0 ?f => first [is_evar f; fail 1 "exact_frm: evar" | assumption] end.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].


(* [comment removed for export] *)
Lemma rw_cells_recast : forall m A cs cs',
  rw_cells psegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells psegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.
Lemma C4_low32 : forall (a b : word) , bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 -> cbytes (C4 a) = cbytes (C4 b).
Proof.
  intros a b E. cbn [cbytes]. unfold le4.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned a) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned b) 32) by (cbn; lia).
  rewrite E. reflexivity.
Qed.
Lemma rw_cells_C4_eq : forall m A pre (a b : word) post,
  bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 ->
  rw_cells psegs m A (pre ++ C4 a :: post) -> rw_cells psegs m A (pre ++ C4 b :: post).
Proof.
  intros m A pre a b post E H. eapply rw_cells_recast; [exact H| | |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. apply cells_wf_app. destruct Hwf as [H1 H2]. split; [exact H1|]. exact H2.
  - rewrite !cells_bytes_app. cbn [cells_bytes]. rewrite (C4_low32 a b E). reflexivity.
  - rewrite !cells_size_app. reflexivity.
Qed.
(* [comment removed for export] *)
Ltac fix_lbf FC :=
  lazymatch type of FC with rw_cells ?sg ?m' ?A ?cs =>
    lazymatch cs with ?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: ?c20 :: C4 (Z_to_bv 64 (-1)) :: ?rest =>
      apply (rw_cells_C4_eq m' A [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19; c20]
               (Z_to_bv 64 (-1)) (Z_to_bv 64 4294967295) rest ltac:(vm_compute; reflexivity)) in FC
    end
  end.

(* [comment removed for export] *)
Lemma rw_cells_C4_CB4 : forall m A (v : word) cs,
  rw_cells psegs m A (C4 v :: cs) -> rw_cells psegs m A (CB 4 (le4 v) :: cs).
Proof.
  intros m A v cs [[W B] R]. split; [split|].
  - cbn [cells_wf cell_wf] in *. split; [apply length_le4| exact (proj2 W)].
  - exact B.
  - exact R.
Qed.
Lemma firstn1_le4 : forall v : word, firstn 1 (skipn 0 (le4 v)) = le1 v.
Proof. intros v. reflexivity. Qed.

Lemma flags_byte_and64 : forall flags : word,
  Z.land (bv_unsigned flags) 64 = 0 -> Z.land (bv_unsigned flags mod 256) 64 = 0.
Proof.
  intros flags H. change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia.
  rewrite (Z.land_comm _ (Z.ones 8)), <- Z.land_assoc, (Z.land_comm (Z.ones 8)), Z.land_ones by lia.
  rewrite H. reflexivity.
Qed.

Lemma rw_cells_CB4_C4 : forall m A (v : word) cs,
  rw_cells psegs m A (CB 4 (le4 v) :: cs) -> rw_cells psegs m A (C4 v :: cs).
Proof.
  intros m A v cs [[W B] R]. split; [split|].
  - cbn [cells_wf cell_wf] in *. split; [exact I| exact (proj2 W)].
  - exact B.
  - exact R.
Qed.

Section StdoutWrite.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis get_set : forall s so, get_so (set_so so s) = so.
  Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.

  (* [comment removed for export] *)
  Definition so_after (so : stdout_st) : stdout_st :=
    mkStdout true [] (if so_first so then false else so_lbf_nl so) false.

  Definition stdout_writefn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (flags mode : word) (tail : list byte) (l : Z) (lo : Z) (canary : word) (m : mem) (st : St)
      : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom psegs)
      /\ munch [(bv_unsigned sp - STDOUT_WRITE_DEPTH, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ stk psegs m' lo (bv_unsigned sp)
      /\ rw_cells psegs m' RSTDOUT (stdout_cells (so_after (get_so st)) flags mode tail)
      /\ ssp_cells m' canary
      /\ st' = set_so (so_after (get_so st)) st.

  Lemma stdout_writefn_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (flags mode : word) (tail : list byte) (s : list Z) (S lo : Z) (canary : word),
      let so := get_so st in
      so_active so = true ->
      rw_cells psegs m RSTDOUT (stdout_cells so flags mode tail) ->
      Z.land (bv_unsigned flags) 64 = 0 ->
      bytes_at psegs m RSTDOUT_BUF (to_bytes (so_buf so)) -> (zlength (so_buf so) <= 1024) ->
      bytes_at psegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDOUT_WRITE_DEPTH) -> (0x55000 <= lo) ->
      ssp_cells m canary -> mem_inv psegs m ->
      (zlength s < 2^61) -> (0 <= S < 2^64) -> (S + zlength s <= 2^64) ->
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= RSTDOUT \/ RSTDOUT + 232 <= S))) ->
      (s = [] -> S <= TASK_SIZE) ->   (* [comment removed for export] *)
      implM psegs (stdout_writefn get_so set_so s) st
            (stdout_writefn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc flags mode tail (zlength s) lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 (wfn_of so)) fc None m (seg_rom psegs)).
  Proof.
    intros until canary. cbv zeta. intros ACT FC FL64 BUFB BUFL SRC -> -> -> ST LO GLO SSP MI LENS S0 Shi SEPS SNIL.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. change psegs with psegs in GOT, GUARD. unfold got_ssp, ssp_guard, STDOUT_WRITE_DEPTH in *.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BS. unfold to_bytes in BS. rewrite length_map in BS.
    assert (LSB : length (to_bytes s) = length s) by (unfold to_bytes; apply length_map).
    unfold stdout_writefn. apply implM_rdso.
    unfold stdout_cells, wfn_of, lbf_of in *.
    destruct (so_first (get_so st)) eqn:FIRST.
    - (* [comment removed for export] *)
      apply implM_bind_assoc. apply implM_updso. apply implM_bind_assoc.
      pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m) as MU.
      pose proof (wmono_refl psegs m) as WM.
      apply implM_sysk.
      change (bytes_at psegs m S (to_bytes s)) with (boxed (bytes_at psegs m S (to_bytes s))) in SRC.
      change (bytes_at psegs m RSTDOUT_BUF (to_bytes (so_buf (get_so st)))) with (boxed (bytes_at psegs m RSTDOUT_BUF (to_bytes (so_buf (get_so st))))) in BUFB.
      assert (LBB : length (to_bytes (so_buf (get_so st))) = length (so_buf (get_so st))) by (unfold to_bytes; apply length_map).
      unfold file_cells in FC. apply rw_cells_C4_CB4 in FC.
      carve_frame 32%nat ST.
      do 9 step. rewrite firstn1_le4, zext_extract_le1. unfold zx8.
      step. step. step. fix_lit_store. step.
      if_cases Hsvb; zify_cond Hsvb. 1:{ exfalso. exact (Hsvb (flags_byte_and64 flags FL64)). }
      do 10 step. step_ecall.
      replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (symmetry; apply Shgetc_lemmas.sx32_small; lia).
      split. { at_node_red; split_spine; try reflexivity; try lia. }
      intros rsp ans Hdec. unfold dec_ioctl in Hdec. apply dec_plain_Some in Hdec.
      destruct ans as [e|v]. 2:{ exfalso. destruct Hdec as (_ & Hok & _). discriminate Hok. }
      destruct Hdec as [-> He]. unfold efferr, eff0. cbv iota.
      apply implM_updso.
      (* [comment removed for export] *)
      unfold implM. apply impl_from_evt. sys_nret.
      do 5 step.
      if_cases He0; zify_cond He0. 1:{ exfalso. rewrite unsigned_errno_ret in He0 by lia. lia. }
      step. step.
      fix_lbf FC.
      step. apply evt_done.
      rewrite !get_set, !set_set. cbn [so_active so_buf so_first].
      unfold stdout_stdio_write. apply (implM_rdso psegs get_so). rewrite get_set. cbn [so_buf].
      apply rw_cells_CB4_C4 in FC.
      eapply implM_bind.
      { eapply (stdio_write_spec (St:=St)) with (B := RSTDOUT_BUF) (fd := 1) (Fp := RSTDOUT) (buf := so_buf (get_so st)) (s := s) (S := S)
          (lo := lo) (canary := canary) (wend := RSTDOUT_BUF + 1024) (bufsize := 1024) (mode := mode) (lbf := 0xffffffff) (tail := tail)
          (flags := flags) (wfn := F_STDIO_WRITE); try reflexivity; rewrite ?unsigned_lit by lia.
        all: first [ exact FC | exact ST | exact MI | exact BUFL | split; [exact GOT | exact GUARD]
                   | lia | unfold STDIO_WRITE_DEPTH; lia | unfold got_ssp; lia | unfold ssp_guard; lia
                   | unfold boxed in BUFB; apply (bytes_at_transport _ _ _ _ _ _ BUFB MU); cbn [disjoint_from]; rewrite LBB; unfold zlength in BUFL; lia
                   | destruct SEPS as [-> | [S1 S2]]; [left; reflexivity | right; split; lia]
                   | exact SNIL
                   | src_now SRC SEPS MU LSB ]. }
      cbv beta. intros [] st' ms' PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
      rewrite !unsigned_lit in MU2, ST2 by lia.
      apply implM_upd. rewrite !get_set, !set_set. cbn [so_lbf_nl so_first].
      (* [comment removed for export] *)
      replace (ret_pc (Z_to_bv 64 0x17c88)) with (Z_to_bv 64 0x17c88 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct SSP2 as [GOT2 GUARD2]. change psegs with psegs in GOT2, GUARD2. unfold got_ssp, ssp_guard in GOT2, GUARD2.
      assert (FR2 : rw_cells psegs m2 (bv_unsigned sp + -32) [CB 8 (firstn 8 (firstn 16 (firstn 24 junk))); C8 canary; C8 s0; C8 ra]).
      { eapply (rw_cells_transport psegs _ _ m2); [exact FR | exact MU2 | exact WM2 | cbn; unfold STDIO_WRITE_DEPTH in *; lia]. }
      step. step. step. if_false. step. step. step. step.
      release_frame FR2 ST2 (bv_unsigned sp).
      unfold stdout_writefn_post, so_after, stdout_cells, wfn_of, lbf_of, file_cells. rewrite FIRST. cbn [so_first so_buf so_lbf_nl].
      sys_finish.
      + apply (munch_trans _ m m0 m2).
        * eapply munch_weaken; [| exact MU]. unfold sub_fp, STDIO_WRITE_DEPTH, STDOUT_WRITE_DEPTH in *; cbn [outside]; intros; lia.
        * eapply munch_weaken; [| exact MU2]. unfold sub_fp, STDIO_WRITE_DEPTH, STDOUT_WRITE_DEPTH in *; cbn [outside]; intros; lia.
      + eapply wmono_trans; [exact WM | exact WM2].
      + split; [exact GOT2 | exact GUARD2].
      + rewrite ?set_set. reflexivity.
    - (* [comment removed for export] *)
      apply (implM_retb psegs). unfold stdout_stdio_write. apply (implM_rdso psegs get_so).
      pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m) as MU.
      assert (LBB : length (to_bytes (so_buf (get_so st))) = length (so_buf (get_so st))) by (unfold to_bytes; apply length_map).
      eapply implM_bind.
      { eapply (stdio_write_spec (St:=St)) with (B := RSTDOUT_BUF) (fd := 1) (Fp := RSTDOUT) (buf := so_buf (get_so st)) (s := s) (S := S)
          (lo := lo) (canary := canary) (wend := RSTDOUT_BUF + 1024) (bufsize := 1024) (mode := mode) (lbf := if so_lbf_nl (get_so st) then 10 else 4294967295) (tail := tail)
          (flags := flags) (wfn := F_STDIO_WRITE); try reflexivity; rewrite ?unsigned_lit by lia.
        all: try first [ exact FC | exact ST | exact MI | exact BUFL | exact BUFB | exact SRC | exact SNIL | split; [exact GOT | exact GUARD]
                   | lia | unfold STDIO_WRITE_DEPTH in *; lia | unfold got_ssp; lia | unfold ssp_guard; lia ].
        destruct SEPS as [-> | [S1 S2]]; [left; reflexivity | right; split; lia]. }
      cbv beta. intros [] st' ms' PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
      apply implM_upd. apply evt_done. rewrite ?get_set.
      unfold stdout_writefn_post, so_after, stdout_cells, wfn_of, lbf_of, file_cells. rewrite FIRST. cbn [so_first so_buf so_lbf_nl].
      sys_finish.
      + eapply munch_weaken; [| exact MU2]. unfold sub_fp, STDIO_WRITE_DEPTH, STDOUT_WRITE_DEPTH in *; cbn [outside]; intros; lia.
      + rewrite ?set_set. reflexivity.
  Qed.
End StdoutWrite.
