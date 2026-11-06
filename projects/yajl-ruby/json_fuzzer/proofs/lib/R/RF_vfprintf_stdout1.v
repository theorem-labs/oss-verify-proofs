(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio Driver.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RF_memset RF_memcpy RF_fwritex RF_pad RF_stdio_lib RF_pop_arg R_Exit Printf_model Printf_mlib RF_printf_iface RF_printf_core RF_vfprintf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_pieces.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.  (* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Ltac ienter := lazymatch goal with |- Monad.implM _ _ _ _ _ => unfold Monad.implM; apply impl_from_evt | |- ITree.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
               lazymatch goal with |- ITree.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Monad.implM rsegs c s Q ms) | _ => idtac end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma land_mod_low : forall f c k, 0 <= k -> 0 <= c < 2^k -> Z.land f c = Z.land (f mod 2^k) c.
Proof.
  intros f c k Hk Hc. rewrite <- (Z.land_ones f k) by lia. rewrite <- Z.land_assoc, (Z.land_comm (Z.ones k) c), Z.land_ones by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma dec128 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 128)) = true -> forall x, 0 <= x < 128 -> P x = true.
Proof.
  intros P H x Hx. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

Lemma land_sub_mask : forall u a b, Z.land a b = b -> Z.land u a = 0 -> Z.land u b = 0.
Proof. intros u a b Hab Hu. rewrite <- Hab, Z.land_assoc, Hu. apply Z.land_0_l. Qed.
Lemma mod_128_of_32 : forall a, (a mod 2^32) mod 128 = a mod 128.
Proof.
  intros a. change 128 with (2^7). rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed.
Lemma sx32_mod128 : forall w : word, bv_unsigned (sx32 w) mod 128 = bv_unsigned w mod 128.
Proof.
  intros w. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq. pose proof (bv_unsigned_in_range 64 w) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R. change (2^64)%Z with 18446744073709551616%Z.
  rewrite <- (mod_128_of_32 (bv_unsigned w)). change (2^32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.
Lemma land_low7 : forall a c, 0 <= c < 128 -> Z.land a c = Z.land (a mod 128) c.
Proof. intros a c Hc. change 128 with (2^7). apply land_mod_low; lia. Qed.

(* [comment removed for export] *)
Lemma flags_noerr_nowr : forall (flags : word), Z.land (bv_unsigned flags) 72 = 0 ->
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 8 = 0.
Proof.
  intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 8) with 8.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. revert H. apply land_sub_mask. reflexivity.
Qed.
Lemma flags_noerr_104 : forall (flags : word), Z.land (bv_unsigned flags) 72 = 0 ->
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 104 = 0.
Proof.
  intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 104) with 72.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. exact H.
Qed.
Lemma flags_olderr_72 : forall (flags2 flags : word), Z.land (bv_unsigned flags2) 104 = 0 ->
  Z.land (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32)) 72 = 0.
Proof.
  intros flags2 flags H. rewrite Z.land_lor_distr_l. rewrite <- (Z.land_assoc _ 32 72). change (Z.land 32 72) with 0. rewrite Z.land_0_r, Z.lor_0_r.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. revert H. apply land_sub_mask. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section StdoutSinkProofs.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Let SINK := SINK_stdout (St:=St) get_so.

  Lemma stdout_sink_frame : sink_frame_stmt RSTDOUT RSTDOUT_BUF 1024 SINK.
  Proof using get_so.
    unfold sink_frame_stmt. intros W m m' st (ACT & flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN) MU WM D1 D2.
    split; [exact ACT|]. exists flags, mode, tail, bufbytes.
    split; [|split; [exact FL | split; [| split; [exact PFX | exact LEN]]]].
    - eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
    - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
  Qed.

  Lemma file_cells_flags_byte : forall m A flags wend wpos wbase writefn buf bufsize fd mode lbf tail,
    rw_cells rsegs m A (file_cells flags wend wpos wbase writefn buf bufsize fd mode lbf tail) ->
    rw_cells rsegs m A [CB 1 [Z_to_bv 8 (bv_unsigned flags)]].
  Proof using .
    intros until tail. intros FC. unfold file_cells in FC.
    apply (proj1 (rw_cells_app rsegs m A [_] _)) in FC. destruct FC as [F0 _].
    pose proof (rw_cells_recast m A _ [CB 1 [Z_to_bv 8 (bv_unsigned flags)]; CB 3 (Z_to_le_bytes 3 (Z.shiftr (bv_unsigned flags) 8))] F0
                  ltac:(cbn; repeat split) ltac:(reflexivity)) as F1.
    apply (proj1 (rw_cells_app rsegs m A [_] _)) in F1. exact (proj1 F1).
  Qed.

  Lemma stdout_sink_flags : sink_flags_stmt RSTDOUT SINK.
  Proof using get_so.
    unfold sink_flags_stmt. intros m st (ACT & flags & mode & tail & bufbytes & FC & FL & _).
    exists (Z_to_bv 8 (bv_unsigned flags)). split; [eapply file_cells_flags_byte; exact FC|].
    rewrite Z_to_bv_unsigned. change (bv_wrap 8 (bv_unsigned flags)) with ((bv_unsigned flags) mod 2^8).
    rewrite <- land_mod_low by lia. eapply land_sub_mask; [|exact FL]. reflexivity.
  Qed.

  Lemma topok_none : topok_stmt TOPOK_none.
  Proof using . unfold topok_stmt, TOPOK_none. intros. exact I. Qed.
End StdoutSinkProofs.

Lemma implM_upd_l {St B} : forall (f : St -> St) (k : unit -> M St B) s Q ms,
  Monad.implM rsegs (k tt) (f s) Q ms -> Monad.implM rsegs (mbind (mupd f) k) s Q ms.
Proof. intros. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stdout.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis GS : forall x so, get_so (set_so so x) = so.
  Hypothesis SS : forall x so so', set_so so' (set_so so x) = set_so so' x.
  Hypothesis FWX : fwritex_stdout_stmt.

  Let OUT := stdout_fwritex get_so set_so.
  Let SINK := SINK_stdout (St:=St) get_so.

  Definition vfprintf_stdout_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk rsegs m' lo (bv_unsigned sp)
      /\ stdout_file m' (get_so st')
      /\ ssp_cells m' canary.

  Definition vfprintf_stdout_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
           (lo : Z) (canary : word),
      let q := bv_unsigned sp in
      a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
      stdout_file m (get_so st) ->
      bytes_at rsegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      va_area m VA slots -> args_ok RSTDOUT RSTDOUT_BUF 1024 m lo q (q - VF_FRAME) slots args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk rsegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 0x800000000000) ->
      ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
      Monad.implM rsegs (stdout_towrite get_so set_so ;;; outsk OUT ps (mret tt)) st
        (vfprintf_stdout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1a298) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  Lemma vfp_stdout_active :
    forall (ra : word) (sp : word) (gp : word) (tp : word) (t0 : word) (t1 : word) (t2 : word) (s0 : word) (s1 : word) (a3 : word) (a4 : word) (a5 : word) (a6 : word) (a7 : word) (s2 : word) (s3 : word) (s4 : word) (s5 : word) (s6 : word) (s7 : word) (s8 : word) (s9 : word) (s10 : word) (s11 : word) (t3 : word) (t4 : word) (t5 : word) (t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (A : Z) (VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (lo : Z) (canary : word) (flags : word) (mode : word) (tail : list byte) (bufbytes : list byte) (m0 : mem),
    (Z.land (bv_unsigned flags) 72 = 0) ->
     forall (m1 : mem),
    (rw_cells rsegs m1 349208 [CB 1024 bufbytes]) ->
    (firstn (length (so_buf (get_so st))) bufbytes = to_bytes (so_buf (get_so st))) ->
    (zlength (so_buf (get_so st)) <= 1024) ->
    (so_active (get_so st) = true) ->
    (true = false → so_buf (get_so st) = []) ->
    (bytes_at rsegs m1 A (zb fmt)) ->
    (Forall (λ c : Z, 0 <= c < 256) fmt) ->
    (pass1_ok fmt = true) ->
    (bytes_at rsegs m1 VA (u64s slots)) ->
    (args_ok 150256 349208 1024 m lo (bv_unsigned sp) (bv_unsigned sp + -368) slots args) ->
    (printf_pieces fmt args = Some (ps, r)) ->
    (fp_calls (length fmt) fmt args = []) ->
    (lo <= bv_unsigned sp - 5552) ->
    (352256 <= lo) ->
    (bv_unsigned sp < 0x800000000000) ->
    (frm0 fc) ->
    (65536 <= A) ->
    (A + Z.of_nat (length fmt) <= 131072) ->
    (bv_unsigned sp <= VA) ->
    (VA + 8 * Z.of_nat (length slots) <= 2 ^ 64) ->
    (0 <= bv_unsigned sp < 2 ^ 64) ->
    (0 <= A ∧ A + Z.of_nat (length fmt) <= 2 ^ 64) ->
    (length (zb fmt) = length fmt) ->
    (length (u64s slots) = (8 * length slots)%nat) ->
    (munch [(lo, bv_unsigned sp); (150256, 150256 + 232); (349208, 349208 + 1024)] m m1) ->
    (wmono rsegs m m1) ->
    (munch [(lo, bv_unsigned sp); (150256, 150256 + 232)] m m1) ->
    (length bufbytes = 1024%nat) ->
     forall (junk : list byte),
    (rw_cells rsegs m1 (bv_unsigned sp + -368) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); CB 248 (firstn 248 (firstn 280 (skipn 16 (firstn 304 (firstn 312 (firstn 320 (firstn 328 (firstn 336 (firstn 344 (firstn 352 (firstn 360 junk))))))))))); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
     forall (x5 : word) (x6 : word) (x7 : word) (b1 : word) (b2 : word) (b3 : word) (b4 : word) (b5 : word) (b6 : word) (b7 : word) (x28 : word) (x29 : word) (x30 : word) (x31 : word),
    (mem_inv rsegs m1) ->
    (stk rsegs m1 lo (bv_unsigned sp + -368)) ->
    (rw_cells rsegs m1 145704 [C8 (Z_to_bv 64 348080)]) ->
    (rw_cells rsegs m1 348080 [C8 canary]) ->
    (rw_cells rsegs m1 150256 [C4 (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 106548); C8 (Z_to_bv 64 (349208 + 1024)); C8 (Z_to_bv 64 (349208 + zlength (so_buf (get_so st)))); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 349208); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (if so_first (get_so st) then 107000 else 106592)); C8 (Z_to_bv 64 106992); C8 (Z_to_bv 64 349208); C8 (Z_to_bv 64 1024); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 (if so_lbf_nl (get_so st) then 10 else 4294967295)); C4 (Z_to_bv 64 0); CB 80 tail]) ->
    evt rsegs (λ ms' : machine_state, impl rsegs (at_node rsegs) ((printf_model OUT OUTFP_stdout fmt args;;; mret ()) (set_so (get_so st) st)) (epost (λ p : () * St, vfprintf_stdout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m p.1 p.2)) ms') (MS (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some x31) TEmpty) (Some b5) TEmpty) (Some x7) (TNode TEmpty (Some s7) TEmpty)) (Some gp) (TNode (TNode TEmpty (Some (Z_to_bv 64 1)) TEmpty) (Some (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) (TNode TEmpty (Some s11) TEmpty))) (Some (Z_to_bv 64 107264)) (TNode (TNode (TNode TEmpty (Some b7) TEmpty) (Some (Z_to_bv 64 A)) (TNode TEmpty (Some s9) TEmpty)) (Some x5) (TNode (TNode TEmpty (Some (sx32 flags)) TEmpty) (Some b3) (TNode TEmpty (Some x29) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some b6) TEmpty) (Some (Z_to_bv 64 150256)) (TNode TEmpty (Some s8) TEmpty)) (Some tp) (TNode (TNode TEmpty (Some (Z_to_bv 64 0)) TEmpty) (Some b2) (TNode TEmpty (Some x28) TEmpty))) (Some (Z_to_bv 64 (bv_unsigned sp + -368))) (TNode (TNode (TNode TEmpty (Some (Z_to_bv 64 348080)) TEmpty) (Some (Z_to_bv 64 350232)) (TNode TEmpty (Some s10) TEmpty)) (Some x6) (TNode (TNode TEmpty (Some s6) TEmpty) (Some b4) (TNode TEmpty (Some x30) TEmpty))))) F (if negb (bv_eqb (Z_to_bv 64 350232) (Z_to_bv 64 0)) then Z_to_bv 64 107400 else Z_to_bv 64 107336) fc None m1 (seg_rom rsegs)).
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st A VA fmt slots args ps r lo canary flags mode tail bufbytes m0 FL72 m1 BUF PFX BLEN ACT INACT BY HF P1 VAA AOK PP FPC LO GLO QHI FRM HA0 HA QVA VAHI Rq AB LZB LU MU WM MU1 LBB junk FR x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 MIc STc SSP1 SSP2 FC.

    (* [comment removed for export] *)
    if_lit. cbv beta iota in FC.
    zs. zs. zs. zs. zs. zs.
    apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
    replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
    ileave.
    pose proof (printf_core_proof St RSTDOUT RSTDOUT_BUF 1024 SINK TOPOK_none OUT (OUTFP_stdout (St:=St))
                  (stdout_sink_frame get_so) (stdout_sink_flags get_so) topok_none (FWX St get_so set_so GS SS)) as PC2.
    unfold printf_core_stmt in PC2.
    assert (FL' : Z.land (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) 104 = 0).
    { rewrite unsigned_lit. apply flags_noerr_104. exact FL72.
      pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
      unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
    eapply implM_bind.
    { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
        clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
      all: try lia. all: try exact I.
      - unfold SINK, SINK_stdout. rewrite GS, ACT. split; [reflexivity|].
        exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode, tail, bufbytes.
        split; [unfold file_cells; exact FC|]. split; [exact FL'|]. split; [exact BUF|]. split; [exact PFX | exact BLEN].
      - exact BY.
      - exact HF.
      - reflexivity.
      - replace (VA + 8 * 0) with VA by lia. exact APC.
      - exact VAA.
      - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1].
      - rewrite FPC. apply Forall_nil.
      - exact STc.
      - split; [exact SSP1 | exact SSP2].
      - assumption.
      - exact FRM. }
    cbv beta. intros r' st' ms' P. clear PC2 MU1.
    unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
    unfold SR in MUc. cbn [app] in MUc.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m3 MUc WMc; clear MUc WMc end.
    apply implM_ret. fix_ret.
    destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3). unfold file_cells in FC3.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [rsegs] in SSP1, SSP2. fold rsegs in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. zs. zs. if_lit.
    zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs.
    (* [comment removed for export] *)
    replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
      by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
    change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
    rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.
    (* [comment removed for export] *)
    lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
      assert (FALL : rw_cells rsegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
      [ apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
      | clear AP FR ] end.
    cbn [app] in FALL.
    release_frame FALL ST3 (bv_unsigned sp).
    apply evt_done. unfold vfprintf_stdout_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST3|].
    split.
    { exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode2, tail2, bufbytes2.
      rewrite ACT3. split; [unfold file_cells; exact FC3|].
      split; [| split; [exact BUF3 | split; [exact PFX3 | split; [exact BLEN3 | intros; discriminate]]]].
      rewrite unsigned_lit; [apply flags_olderr_72; exact FL3|].
      pose proof (bv_unsigned_in_range 64 (sx32 flags2)) as R1. pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R2.
      unfold bv_modulus in R1, R2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R1, R2.
      pose proof (Z_land_range (bv_unsigned (sx32 flags)) 32).
      split; [apply Z.lor_nonneg; lia|].
      apply (lor_lt_pow2 _ _ 64); lia. }
    split; [exact SSP1 | exact SSP2].
  Qed.

  (* [comment removed for export] *)
  Lemma vfp_stdout_inactive :
    forall (ra : word) (sp : word) (gp : word) (tp : word) (t0 : word) (t1 : word) (t2 : word) (s0 : word) (s1 : word) (a3 : word) (a4 : word) (a5 : word) (a6 : word) (a7 : word) (s2 : word) (s3 : word) (s4 : word) (s5 : word) (s6 : word) (s7 : word) (s8 : word) (s9 : word) (s10 : word) (s11 : word) (t3 : word) (t4 : word) (t5 : word) (t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (A : Z) (VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (lo : Z) (canary : word) (flags : word) (mode : word) (tail : list byte) (bufbytes : list byte) (m0 : mem),
    (Z.land (bv_unsigned flags) 72 = 0) ->
     forall (m1 : mem),
    (rw_cells rsegs m1 349208 [CB 1024 bufbytes]) ->
    (firstn (length (so_buf (get_so st))) bufbytes = to_bytes (so_buf (get_so st))) ->
    (zlength (so_buf (get_so st)) <= 1024) ->
    (so_active (get_so st) = false) ->
    (false = false → so_buf (get_so st) = []) ->
    (bytes_at rsegs m1 A (zb fmt)) ->
    (Forall (λ c : Z, 0 <= c < 256) fmt) ->
    (pass1_ok fmt = true) ->
    (bytes_at rsegs m1 VA (u64s slots)) ->
    (args_ok 150256 349208 1024 m lo (bv_unsigned sp) (bv_unsigned sp + -368) slots args) ->
    (printf_pieces fmt args = Some (ps, r)) ->
    (fp_calls (length fmt) fmt args = []) ->
    (lo <= bv_unsigned sp - 5552) ->
    (352256 <= lo) ->
    (bv_unsigned sp < 0x800000000000) ->
    (frm0 fc) ->
    (65536 <= A) ->
    (A + Z.of_nat (length fmt) <= 131072) ->
    (bv_unsigned sp <= VA) ->
    (VA + 8 * Z.of_nat (length slots) <= 2 ^ 64) ->
    (0 <= bv_unsigned sp < 2 ^ 64) ->
    (0 <= A ∧ A + Z.of_nat (length fmt) <= 2 ^ 64) ->
    (length (zb fmt) = length fmt) ->
    (length (u64s slots) = (8 * length slots)%nat) ->
    (munch [(lo, bv_unsigned sp); (150256, 150256 + 232); (349208, 349208 + 1024)] m m1) ->
    (wmono rsegs m m1) ->
    (munch [(lo, bv_unsigned sp); (150256, 150256 + 232)] m m1) ->
    (length bufbytes = 1024%nat) ->
     forall (junk : list byte),
    (rw_cells rsegs m1 (bv_unsigned sp + -368) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); CB 248 (firstn 248 (firstn 280 (skipn 16 (firstn 304 (firstn 312 (firstn 320 (firstn 328 (firstn 336 (firstn 344 (firstn 352 (firstn 360 junk))))))))))); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
     forall (x5 : word) (x6 : word) (x7 : word) (b1 : word) (b2 : word) (b3 : word) (b4 : word) (b5 : word) (b6 : word) (b7 : word) (x28 : word) (x29 : word) (x30 : word) (x31 : word),
    (mem_inv rsegs m1) ->
    (stk rsegs m1 lo (bv_unsigned sp + -368)) ->
    (rw_cells rsegs m1 145704 [C8 (Z_to_bv 64 348080)]) ->
    (rw_cells rsegs m1 348080 [C8 canary]) ->
    (rw_cells rsegs m1 150256 [C4 (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 106548); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (if so_first (get_so st) then 107000 else 106592)); C8 (Z_to_bv 64 106992); C8 (Z_to_bv 64 349208); C8 (Z_to_bv 64 1024); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 (if so_lbf_nl (get_so st) then 10 else 4294967295)); C4 (Z_to_bv 64 0); CB 80 tail]) ->
    evt rsegs (λ ms' : machine_state, impl rsegs (at_node rsegs) ((printf_model OUT OUTFP_stdout fmt args;;; mret ()) (set_so {| so_active := true; so_buf := []; so_lbf_nl := so_lbf_nl (get_so st); so_first := so_first (get_so st) |} st)) (epost (λ p : () * St, vfprintf_stdout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m p.1 p.2)) ms') (MS (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some x31) TEmpty) (Some b5) TEmpty) (Some x7) (TNode TEmpty (Some s7) TEmpty)) (Some gp) (TNode (TNode TEmpty (Some (Z_to_bv 64 1)) TEmpty) (Some (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) (TNode TEmpty (Some s11) TEmpty))) (Some (Z_to_bv 64 107264)) (TNode (TNode (TNode TEmpty (Some b7) TEmpty) (Some (Z_to_bv 64 A)) (TNode TEmpty (Some s9) TEmpty)) (Some x5) (TNode (TNode TEmpty (Some (sx32 flags)) TEmpty) (Some b3) (TNode TEmpty (Some x29) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some b6) TEmpty) (Some (Z_to_bv 64 150256)) (TNode TEmpty (Some s8) TEmpty)) (Some tp) (TNode (TNode TEmpty (Some (Z_to_bv 64 0)) TEmpty) (Some b2) (TNode TEmpty (Some x28) TEmpty))) (Some (Z_to_bv 64 (bv_unsigned sp + -368))) (TNode (TNode (TNode TEmpty (Some (Z_to_bv 64 348080)) TEmpty) (Some (Z_to_bv 64 0)) (TNode TEmpty (Some s10) TEmpty)) (Some x6) (TNode (TNode TEmpty (Some s6) TEmpty) (Some b4) (TNode TEmpty (Some x30) TEmpty))))) F (if negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) then Z_to_bv 64 107400 else Z_to_bv 64 107336) fc None m1 (seg_rom rsegs)).
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st A VA fmt slots args ps r lo canary flags mode tail bufbytes m0 FL72 m1 BUF PFX BLEN ACT INACT BY HF P1 VAA AOK PP FPC LO GLO QHI FRM HA0 HA QVA VAHI Rq AB LZB LU MU WM MU1 LBB junk FR x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 MIc STc SSP1 SSP2 FC.

    (* [comment removed for export] *)
    if_lit. cbv beta iota in FC. zs. zs. zs.
    pose proof towrite_proof as TW. unfold towrite_stmt in TW.
    eapply evt_cut.
    { eapply TW; clear TW; rewrite ?unsigned_lit by lia; [ exact FC | | lia | lia | lia | assumption ].
      rewrite unsigned_lit; [apply flags_noerr_nowr; exact FL72|].
      pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
      unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
    cbv beta. intros ms' P. clear TW.
    destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FCt).
    rewrite !unsigned_lit in MUc, FCt by lia. clear FC.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
    fix_ret.
    zs. if_lit. zs. zs. zs. zs. zs. zs.
    apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
    replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
    ileave.
    pose proof (printf_core_proof St RSTDOUT RSTDOUT_BUF 1024 SINK TOPOK_none OUT (OUTFP_stdout (St:=St))
                  (stdout_sink_frame get_so) (stdout_sink_flags get_so) topok_none (FWX St get_so set_so GS SS)) as PC2.
    unfold printf_core_stmt in PC2.
    assert (FL' : Z.land (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) 104 = 0).
    { rewrite unsigned_lit. apply flags_noerr_104. exact FL72.
      pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
      unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
    eapply implM_bind.
    { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
        clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
      all: try lia. all: try exact I.
      - unfold SINK, SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [reflexivity|].
        exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode', tail, bufbytes.
        change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
        split; [exact FCt|]. split; [exact FL'|]. split; [exact BUF|]. split; [reflexivity | lia].
      - exact BY.
      - exact HF.
      - reflexivity.
      - replace (VA + 8 * 0) with VA by lia. exact APC.
      - exact VAA.
      - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1].
      - rewrite FPC. apply Forall_nil.
      - exact STc.
      - split; [exact SSP1 | exact SSP2].
      - assumption.
      - exact FRM. }
    cbv beta. intros r' st' ms' P. clear PC2 MU1.
    unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
    unfold SR in MUc. cbn [app] in MUc.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m3 MUc WMc; clear MUc WMc end.
    apply implM_ret. fix_ret.
    destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3). unfold file_cells in FC3.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [rsegs] in SSP1, SSP2. fold rsegs in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. zs. zs. if_lit.
    zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs.
    (* [comment removed for export] *)
    replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
      by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
    change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
    rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.
    (* [comment removed for export] *)
    lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
      assert (FALL : rw_cells rsegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
      [ apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
      | clear AP FR ] end.
    cbn [app] in FALL.
    release_frame FALL ST3 (bv_unsigned sp).
    apply evt_done. unfold vfprintf_stdout_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST3|].
    split.
    { exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode2, tail2, bufbytes2.
      rewrite ACT3. split; [unfold file_cells; exact FC3|].
      split; [| split; [exact BUF3 | split; [exact PFX3 | split; [exact BLEN3 | intros; discriminate]]]].
      rewrite unsigned_lit; [apply flags_olderr_72; exact FL3|].
      pose proof (bv_unsigned_in_range 64 (sx32 flags2)) as R1. pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R2.
      unfold bv_modulus in R1, R2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R1, R2.
      pose proof (Z_land_range (bv_unsigned (sx32 flags)) 32).
      split; [apply Z.lor_nonneg; lia|].
      apply (lor_lt_pow2 _ _ 64); lia. }
    split; [exact SSP1 | exact SSP2].
  Qed.
End Stdout.
End RC__1.
