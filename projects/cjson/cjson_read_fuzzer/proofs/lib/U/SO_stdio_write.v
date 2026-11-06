(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import F_syscalls F_pad F_fmt_fp_lib Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SO_model.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
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

Definition STDIO_WRITE : Z := 0x18bb4.
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
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - STDIO_WRITE_DEPTH, bv_unsigned sp); (Fp + 32, Fp + 64)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' Fp (file_cells flags (B + bufsize) B B wfn B bufsize fd mode lbf tail)
      /\ ssp_cells m' canary
      /\ st' = st.

  (* [comment removed for export] *)
  Lemma implM_wv_step : forall (fd : Z) (iov : list (list Z)) (fuel : nat) (st : St)
      (Q : unit -> St -> machine_state -> Prop) ms,
    evt usegs (fun ms1 => at_node usegs (NWritev fd (map to_bytes iov)) ms1 /\
       forall rsp k, dec_wv (wv_total iov) rsp = Some k ->
          (k = wv_total iov -> evt usegs (Q tt st) (nret ms1 rsp)) /\
          (k <> wv_total iov -> implM usegs (mloop fuel (wv_body fd) (wv_advance iov k)) st Q (nret ms1 rsp))) ms ->
    implM usegs (mloop (S fuel) (wv_body (St:=St) fd) iov) st Q ms.
  Proof using .
    intros fd iov fuel st Q ms H. apply implM_loop_S. unfold wv_body.
    eapply implM_bind with (Q1 := fun k s' ms' => s' = st /\
        (k = wv_total iov -> evt usegs (Q tt st) ms') /\
        (k <> wv_total iov -> implM usegs (mloop fuel (wv_body fd) (wv_advance iov k)) st Q ms')).
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
    Hypothesis GLO : 0x56000 <= lo.
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
      (rw_cells usegs mm (bv_unsigned sp + -112)
         [CB 8 jk; C8 b0w; C8 l0w; C8 b1w; C8 l1w; C8 canary; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    Notation FILE mm := (rw_cells usegs mm Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail)).
    (* [comment removed for export] *)
    Notation LST pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31 :=
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 ssp_guard) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

    (* [comment removed for export] *)
    Definition minv (mm : mem) : Prop :=
      munch WF m0 mm /\ wmono usegs m0 mm /\ mem_inv usegs mm /\ stk usegs mm lo SPF /\ FILE mm /\ ssp_cells mm canary.

    Hypothesis SRC0 : bytes_at usegs m0 S (to_bytes s).
    Hypothesis BUF0 : bytes_at usegs m0 B (to_bytes buf).

    Lemma to_bytes_length : forall l, length (to_bytes l) = length l.
    Proof using . intros. unfold to_bytes. apply length_map. Qed.

    Lemma src_cur : forall mm, munch WF m0 mm -> bytes_at usegs mm S (to_bytes s).
    Proof using FPLO LO S0 SEPS SRC0 buf.
      intros mm MU. destruct SEPS as [E | [SEP1 SEP2]].
      - rewrite E. apply bytes_at_nil. lia.
      - apply (bytes_at_transport _ _ _ mm _ _ SRC0 MU). cbn [disjoint_from]. rewrite to_bytes_length. unfold zlength in *. lia.
    Qed.

    Lemma buf_cur : forall mm, munch WF m0 mm -> bytes_at usegs mm B (to_bytes buf).
    Proof using BUF0 LO SEPB s.
      intros mm MU. apply (bytes_at_transport _ _ _ mm _ _ BUF0 MU). cbn [disjoint_from]. rewrite to_bytes_length.
      unfold zlength in *. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma bytes_at_drop : forall mm A (l : list Z) j, bytes_at usegs mm A (to_bytes l) -> 0 <= j <= zlength l ->
      bytes_at usegs mm (A + j) (to_bytes (skipn (Z.to_nat j) l)).
    Proof using .
      intros mm A l j BY Hj. unfold zlength in Hj.
      rewrite <- (firstn_skipn (Z.to_nat j) l) in BY. unfold to_bytes in BY |- *. rewrite map_app in BY.
      apply bytes_at_app in BY. destruct BY as [_ BY]. rewrite length_map, length_firstn in BY.
      replace (A + Z.of_nat (Init.Nat.min (Z.to_nat j) (length l))) with (A + j) in BY by lia. exact BY.
    Qed.

    (* [comment removed for export] *)
    Lemma frame_iovs : forall mm jk b0w l0w b1w l1w, FRAME mm jk b0w l0w b1w l1w ->
      bytes_at usegs mm (bv_unsigned sp + -112 + 8) (iovec_bytes [(b0w, l0w); (b1w, l1w)])
      /\ bytes_at usegs mm (bv_unsigned sp + -112 + 24) (iovec_bytes [(b1w, l1w)]).
    Proof using .
      intros mm jk b0w l0w b1w l1w FR.
      change (rw_cells usegs mm (bv_unsigned sp + -112) ([CB 8 jk] ++ [C8 b0w; C8 l0w] ++ [C8 b1w; C8 l1w] ++
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
      evt usegs (POST tt st) (LST 0x18c48 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31).
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
      implM usegs (mloop fuel (wv_body (St:=St) fd) [skipn (Z.to_nat j') s]) st POST
            (LST 0x18cd4 mm x1 x5 x6 x7 (Z_to_bv 64 kw) x11 x12 x13 x14 x15 x16 x17
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
      lazymatch goal with H : rw_cells usegs ?mx (bv_unsigned sp + -112) _ |- _ => rename H into FR1; rename mx into m1 end.
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
        replace (ret_pc (Z_to_bv 64 0x18ccc)) with (Z_to_bv 64 0x18ccc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        step. step. if_cases Hd; zify_cond Hd; [| exfalso; lia].
        eapply sw_done; [exact MINV1| exact FR1].
      + (* [comment removed for export] *)
        intros NE. cbn [wv_advance]. rewrite skipn_skipn.
        replace (Z.to_nat k2 + Z.to_nat j')%nat with (Z.to_nat (j' + k2)) by lia.
        unfold implM. iprefix. unfold eff0. sys_nret.
        step. step. step. step. if_cases Hc; zify_cond Hc; [| exfalso; lia]. step.
        replace (ret_pc (Z_to_bv 64 0x18ccc)) with (Z_to_bv 64 0x18ccc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
      implM usegs (mloop fuel (wv_body (St:=St) fd) (wv_advance [skipn (Z.to_nat j) buf; s] k)) st POST
            (LST 0x18cd4 mm x1 x5 x6 x7 (Z_to_bv 64 k) x11 x12 x13 x14 x15 x16 x17
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
        lazymatch goal with H : rw_cells usegs ?mx (bv_unsigned sp + -112) _ |- _ => rename H into FR1; rename mx into m1 end.
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
          replace (ret_pc (Z_to_bv 64 0x18ccc)) with (Z_to_bv 64 0x18ccc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          step. step. if_cases Hd; zify_cond Hd; [| exfalso; lia].
          eapply sw_done; [exact MINV1| exact FR1].
        + intros NE. cbn [wv_advance]. rewrite skipn_skipn.
          replace (Z.to_nat k2 + Z.to_nat j1)%nat with (Z.to_nat (j1 + k2)) by lia.
          unfold implM. iprefix. unfold eff0. sys_nret.
          step. step. step. step. if_cases Hc; zify_cond Hc; [| exfalso; lia]. step.
          replace (ret_pc (Z_to_bv 64 0x18ccc)) with (Z_to_bv 64 0x18ccc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
        lazymatch goal with H : rw_cells usegs ?mx (bv_unsigned sp + -112) _ |- _ => rename H into FR1; rename mx into m1 end.
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
          replace (ret_pc (Z_to_bv 64 0x18ccc)) with (Z_to_bv 64 0x18ccc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          step. step. if_cases Hd; zify_cond Hd; [| exfalso; lia].
          eapply sw_done; [exact MINV1| exact FR1].
        + intros NE.
          unfold implM. iprefix. unfold eff0. sys_nret.
          step. step. step. step. if_cases Hc; zify_cond Hc; [| exfalso; lia]. step.
          replace (ret_pc (Z_to_bv 64 0x18ccc)) with (Z_to_bv 64 0x18ccc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          step. step. if_cases Hd; zify_cond Hd; [exfalso; lia|].
          apply evt_done. cbv beta.
          replace (Z_to_bv 64 (bv_unsigned sp + -104)) with (Z_to_bv 64 (bv_unsigned sp + -112 + 8) : word) by (f_equal; lia).
          eapply (IH (j + k) k2 fuel m1 jk); [ | | | | | | | | exact MINV1| exact FR1]; unfold zlength; lia.
    Qed.

    (* [comment removed for export] *)
    Lemma sw_entry : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      FILE m0 -> stk usegs m0 lo (bv_unsigned sp) -> ssp_cells m0 canary -> mem_inv usegs m0 ->
      implM usegs (stdio_writev (St:=St) fd buf s) st POST
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 (zlength s)) a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x18bb4) fc None m0 (seg_rom usegs)).
    Proof using B0 BS0 BShi BUF0 BUFLE FD FPLO FSEP1 FSEP2 Fp0 GLO LENS LO S0 SEPB SEPS SPHI SRC0 Shi TB TS TSP.
      intros until t6. intros FC ST [GOT GUARD] MI.
      pose proof (bytes_at_bound _ _ _ _ BUF0) as BB. rewrite to_bytes_length in BB.
      change (boxed (bytes_at usegs m0 S (to_bytes s))) in SRC0. change (boxed (bytes_at usegs m0 B (to_bytes buf))) in BUF0.
      unfold got_ssp, ssp_guard in *. unfold file_cells in FC. unfold zlength in *.
      pose proof (munch_refl WF m0) as MU. pose proof (wmono_refl usegs m0) as WM.
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
        lazymatch goal with H : rw_cells usegs ?mx (bv_unsigned sp + -112) _ |- _ => rename H into FR1; rename mx into m1 end.
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
          replace (ret_pc (Z_to_bv 64 0x18c44)) with (Z_to_bv 64 0x18c44 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          step. if_cases Hd; zify_cond Hd; [exfalso; lia|].
          eapply sw_done; [exact MINV1| exact FR1].
        + intros NE. assert (K2 : 1 <= k2 < Z.of_nat (length s)) by lia. clear Hk2.
          replace (wv_advance [s] k2) with [skipn (Z.to_nat k2) s] by reflexivity.
          unfold implM. iprefix. unfold eff0. sys_nret.
          step. step. step. step. if_cases Hc; zify_cond Hc; [| exfalso; lia]. step.
          replace (ret_pc (Z_to_bv 64 0x18c44)) with (Z_to_bv 64 0x18c44 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
        lazymatch goal with H : rw_cells usegs ?mx (bv_unsigned sp + -112) _ |- _ => rename H into FR1; rename mx into m1 end.
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
          replace (ret_pc (Z_to_bv 64 0x18c44)) with (Z_to_bv 64 0x18c44 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          step. if_cases Hd; zify_cond Hd; [exfalso; lia|].
          eapply sw_done; [exact MINV1| exact FR1].
        + intros NE. assert (K2 : 1 <= k2 < nb + Z.of_nat (length s)) by lia. clear Hk2.
          unfold implM. iprefix. unfold eff0. sys_nret.
          step. step. step. step. if_cases Hc; zify_cond Hc; [| exfalso; lia]. step.
          replace (ret_pc (Z_to_bv 64 0x18c44)) with (Z_to_bv 64 0x18c44 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
      rw_cells usegs m Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
      bytes_at usegs m B (to_bytes buf) ->
      bytes_at usegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      (fd = 1 \/ fd = 2) ->
      stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDIO_WRITE_DEPTH) -> (0x56000 <= lo) ->
      ssp_cells m canary -> mem_inv usegs m ->
      (0 <= Fp) -> (Fp + 232 <= lo) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (0 <= B) -> (0 <= bufsize) -> (zlength buf <= bufsize) -> (B + bufsize < 2^64) ->
      (zlength buf + zlength s < 2^62) -> (0 <= S < 2^64) -> (S + zlength s <= 2^64) ->
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S))) ->
      (B + zlength buf <= lo \/ bv_unsigned sp <= B) ->
      (s = [] -> S <= TASK_SIZE) ->   (* [comment removed for export] *)
      implM usegs (stdio_writev (St:=St) fd buf s) st
            (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
                              (zlength s) lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x18bb4) fc None m (seg_rom usegs)).
  Proof.
    intros until canary. intros FC BUFB SRC -> -> -> FD ST LO GLO SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BUFLE BShi LENS S0 Shi SEPS SEPB SNIL.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold STDIO_WRITE_DEPTH in LO.
    (* [comment removed for export] *)
    assert (TSP : bv_unsigned sp <= TASK_SIZE).
    { (nelimp ST 3%nat; intros _ _ STk). (nelim (STk (bv_unsigned sp - 1) ltac:(lia)) 3%nat; intros _ b Hb).
      pose proof (mem_inv_mrd_task usegs m _ b MI usegs_task Hb) as T. rewrite wa_unsigned in T by lia. lia. }
    assert (TB : zlength buf = 0 \/ B + zlength buf <= TASK_SIZE).
    { destruct buf as [|c buf']; [left; reflexivity| right].
      pose proof (bytes_at_task usegs m B _ MI usegs_task BUFB ltac:(discriminate)) as T. rewrite to_bytes_length in T. unfold zlength. exact T. }
    assert (TS : S + zlength s <= TASK_SIZE).
    { destruct s as [|c s'].
      - unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r. apply SNIL. reflexivity.
      - pose proof (bytes_at_task usegs m S _ MI usegs_task SRC ltac:(discriminate)) as T. rewrite to_bytes_length in T. unfold zlength. exact T. }
    eapply sw_entry; try eassumption; lia.
  Qed.
End StdioWrite.
